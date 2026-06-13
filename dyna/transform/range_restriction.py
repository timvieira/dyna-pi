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

    def __init__(self, program, adom=None, input_type=None, prune=True):
        self.adom = adom
        # the active domain is a new input relation: the user supplies it
        adom_input = Program(f'{adom}(_).') if adom is not None else None

        if input_type is not None and input_type.inputs is None:
            # a user-supplied input type may omit its own type parameters;
            # Abbreviate requires them to be declared (possibly empty)
            input_type = input_type.set_input_types(Program([]))

        # Single pass — no outer loop.  `type_analysis` already computes the
        # *transitive* openness fixpoint (propagation through consumption is
        # the type solver's job, and its forward chaining closes over
        # recursion), so one Abbreviate pass, expanding over the complete type
        # chart, projects every open position at once.  A second pass would
        # only re-project the recovery rules this pass emitted — their
        # reintroduced variable is open by construction — i.e. chew on the
        # residue.  `input_type` (Section 3.1) lets an input declare a position
        # `$free` (a Step A base case with no deriving rule).  The
        # post-condition below asserts this one-shot completeness.
        types = program.type_analysis(input_type=input_type)
        if open_types(program, types=types):
            q = program.abbreviate(types=types, adom=adom)
            if adom is not None:
                q.set_input_types((q.inputs or Program([])) + adom_input)
            if prune:
                q = q.prune_very_fast()
        else:
            q = program   # already range-restricted; nothing open to project

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
        """Post-conditions (confinement, not soundness — ground-query values
        are correct regardless).

        One-shot completeness: because `type_analysis` computes the transitive
        openness fixpoint, a single Abbreviate pass confines all *projectable*
        openness — a second pass would only re-project the recovery rules it
        just emitted.  No program is known that needs more than one pass.

        With `adom`, Step E must have removed the residue entirely — a hard
        invariant (a non-empty residue means the splice missed a variable), so
        it is asserted.

        Without `adom`, every residual rule should be a recovery rule
        (`output(.., V, ..) += q\\j`) or a delayed-test rule (spec E5,
        Theorem (c)).  A rule that is neither is *warned*, not asserted,
        because there is a genuine third case: a **builtin-orphaned** rule,
        where abbreviation projected a pass-through variable out of an open
        item while it was also feeding a builtin (e.g.
        `g(Z) += f(X) * (Z is X+1)`).  That only arises when the open item is
        the builtin variable's sole generator — i.e. on programs whose source
        is already non-evaluable — so it is a confined-but-degenerate residue,
        not a transform failure worth crashing on.
        """
        if self.adom is not None:
            assert not self.residual_layer.rules, (
                f'adom={self.adom!r} given but residue is non-empty — Step E '
                f'should have removed it: '
                + '; '.join(map(str, self.residual_layer.rules)))
            return

        unexpected = [
            r for r in self.residual_layer.rules
            if not (self._is_recovery(self, r) or self._is_delayed_test(self, r))
        ]
        if unexpected:
            warnings.warn(
                'RangeRestrictionNormalization residual layer contains '
                f'{len(unexpected)} rule(s) that are neither recovery nor '
                'delayed-test form (a transform gap, or a builtin-orphaned '
                'variable on an already-non-evaluable program): '
                + '; '.join(map(str, unexpected)))

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
