"""
Range-restriction normalization (docs/range-restriction-normalization.md).

Rewrites a program into an equivalent one whose non-range-restriction is
confined to an explicit residual layer at the outputs, the way ε-production
elimination confines a CFG's one unavoidable ε to `S0 -> S | epsilon`.

The construction is rename + recovery (the spec's hygiene discipline),
implemented on the projection machinery of `Abbreviate`:

  Step A  openness fixpoint        `open_types` (the $free-marked derivable
                                   types of the type analysis)
  Step B  closed/open expansion +  `Abbreviate` (type-chart join; fresh
          projection + recovery     functors; recovery rules)
  Step C  multiplicity correction  `Abbreviate.__dropped_var_correction`
                                   (Semiring.multiple(inf), threaded guard)
  Step D  residue isolation        `residual_layer` (surviving rules that
                                   fail the refined range-restriction check)
  Step E  active-domain escape     `adom=...` (splice `adom(V)`; witness
                                   counts become |adom|; residue empties)

Dead recovery rules — recovery rules whose original item no consumer reads and
that feed no output — are removed by reachability pruning.  Recovery rules are
always value-exact (only pass-through openness is ever projected), so pruning
is load-bearing for *confinement*, not soundness: a dead recovery rule is
non-range-restricted, and left in place it would pollute the residual layer
and break its output-feeding form (DoD #3).

Irreducibility caveat (spec Section 6): without `adom`, the residual layer is
non-empty whenever a free variable reaches an output, and a rule whose head
variable is constrained *only by tests* (spec E5: `f(X) += g(Y) * (X > Y)`)
is irreducibly non-range-restricted: its value genuinely depends on the test
variable, so it is not pass-through and must not be projected.  Such rules
also land in `residual_layer`; under `adom` they become range-restricted like
everything else.
"""

import warnings

from dyna import Program, TransformedProgram, Rule, Term, term_vars, snap
from dyna.analyze.range_restriction import (
    bindable_vars, is_rule_range_restricted, open_types, TEST_FNS,
)


class RangeRestrictionNormalization(TransformedProgram):

    def __init__(self, program, adom=None, input_type=None, max_passes=4, prune=True):
        self.adom = adom
        self._max_passes = max_passes
        # the active domain is a new input relation: the user supplies it
        adom_input = Program(f'{adom}(_).') if adom is not None else None

        if input_type is not None and input_type.inputs is None:
            # a user-supplied input type may omit its own type parameters;
            # Abbreviate requires them to be declared (possibly empty)
            input_type = input_type.set_input_types(Program([]))

        q = program
        converged = False
        for i in range(max_passes):
            # Stop when the only rules left that fail the refined
            # range-restriction check are residue: recovery/open rules whose
            # openness is irreducible without an active domain.
            #
            # `input_type` (Section 3.1): input types may declare a position
            # open by `$free` — a Step A base case with no deriving rule.  It
            # describes the *original* inputs, so it seeds the first pass
            # only; later passes see the abbreviated inputs that Abbreviate
            # installs via set_input_types.
            types = q.type_analysis(input_type=input_type if i == 0 else None)
            if not open_types(q, types=types):
                converged = True
                break
            new = q.abbreviate(types=types, adom=adom)
            if adom is not None:
                new.set_input_types((new.inputs or Program([])) + adom_input)
            if prune: new = new.prune_very_fast()
            if len(new.rules) == len(q.rules) and all(
                    str(a) == str(b) for a, b in zip(new.rules, q.rules)):
                converged = True
                break   # no progress; remaining openness is residual
            q = new
            # A second pass would re-project the recovery rules themselves
            # (their reintroduced free variable is open by construction), so
            # iterate only while the *engine layer* still has non-residual
            # openness — i.e. while some non-range-restricted rule is not in
            # recovery form.  One projection pass plus pruning normalizes the
            # engine layer; the loop guard is a safety net, not the workhorse.
            if all(is_rule_range_restricted(q, r) or self._is_recovery(q, r)
                   for r in q):
                converged = True
                break

        self.converged = converged
        rules = list(q)

        if adom is not None:
            # Step E: re-bind every remaining unbindable variable over the
            # active domain.  This removes the residue entirely (DoD #5).
            rules = [self._splice_adom(q, r) for r in rules]

        super().__init__('rr-normalize', program, rules)
        if adom is not None:
            self.set_input_types((self.inputs or Program([])) + adom_input)

        # Step D: the residual layer is what survives the refined check.
        self.residual_layer = self.spawn(
            [r for r in self.rules if not is_rule_range_restricted(self, r)])
        self.engine_layer = self.spawn(
            [r for r in self.rules if is_rule_range_restricted(self, r)])

        self._check_postconditions()

    def _check_postconditions(self):
        """Warn on the detectable silent-failure modes (values are correct
        regardless — these are confinement, not soundness, conditions).

        (1) Non-convergence: the projection loop hit `max_passes` without a
            clean break, so the engine layer may still consume open items that
            were never projected and `residual_layer` may hold unprocessed
            rules rather than genuine residue.  Raise `max_passes`.

        (2) Residue shape (Theorem (c)): every residual rule must be a
            recovery rule (`output(.., V, ..) += q\\j`) or a delayed-test rule
            (spec E5).  A residual rule that is neither is a tell that the loop
            gave up, not that the program has irreducible residue.  With `adom`
            the residue must be empty outright (Step E removed it).
        """
        if not self.converged:
            warnings.warn(
                f'RangeRestrictionNormalization did not converge in '
                f'{self._max_passes} passes; the result may be only partially '
                f'normalized (raise max_passes). Ground-query values are still '
                f'correct.')

        if self.adom is not None:
            if self.residual_layer.rules:
                warnings.warn(
                    f'RangeRestrictionNormalization was given adom={self.adom!r} '
                    f'but the residual layer is non-empty '
                    f'({len(self.residual_layer.rules)} rule(s)); Step E should '
                    f'have removed it. This indicates a variable the adom splice '
                    f'missed.')
            return

        unexpected = [
            r for r in self.residual_layer.rules
            if not (self._is_recovery(self, r) or self._is_delayed_test(self, r))
        ]
        if unexpected:
            warnings.warn(
                f'RangeRestrictionNormalization residual layer contains '
                f'{len(unexpected)} rule(s) that are neither recovery nor '
                f'delayed-test form — expected only confined residue '
                f'(Theorem (c)): ' + '; '.join(str(r) for r in unexpected))

    @staticmethod
    def _is_delayed_test(program, rule):
        """A delayed-test rule (spec E5, Section 4 case 2): the head variables
        that make the rule non-range-restricted occur only in tests, so they
        are not pass-through (the value depends on them) and cannot be
        projected — irreducible residue without an active domain."""
        unbound = term_vars(rule.head) - bindable_vars(program, rule)
        if not unbound: return False
        test_vars = set()
        for b in rule.body:
            b = snap(b)
            if isinstance(b, Term) and b.fn in TEST_FNS:
                test_vars |= term_vars(b)
        return unbound <= test_vars

    @staticmethod
    def _is_recovery(program, rule):
        """A recovery rule: a single non-builtin body item whose variables all
        appear in the head (the reintroduced free position is in the head
        only).  This is the residue form of spec Step D."""
        body = [b for b in rule.body if not program.is_const(b)]
        if len(body) != 1: return False
        [b] = body
        if program.is_builtin(b): return False
        return term_vars(b) <= term_vars(rule.head)

    def _splice_adom(self, program, rule):
        unbound = (term_vars(rule.head) | term_vars(rule.body)) - bindable_vars(program, rule)
        if not unbound: return rule
        return Rule(rule.head, *rule.body,
                    *[Term(self.adom, v) for v in sorted(unbound, key=str)])
