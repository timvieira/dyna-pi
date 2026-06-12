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
that feed no output — are removed by reachability pruning; this is load-bearing
for soundness bookkeeping, not just hygiene (a pruned recovery rule is exactly
one whose possible imprecision is unobservable).

Irreducibility caveat (spec Section 6): without `adom`, the residual layer is
non-empty whenever a free variable reaches an output, and a rule whose head
variable is constrained *only by tests* (spec E5: `f(X) += g(Y) * (X > Y)`)
is irreducibly non-range-restricted: its value genuinely depends on the test
variable, so it is not pass-through and must not be projected.  Such rules
also land in `residual_layer`; under `adom` they become range-restricted like
everything else.
"""

from dyna import Program, TransformedProgram, Rule, Term, term_vars
from dyna.analyze.range_restriction import (
    bindable_vars, is_rule_range_restricted, open_types,
)


class RangeRestrictionNormalization(TransformedProgram):

    def __init__(self, program, adom=None, max_passes=4, prune=True):
        self.adom = adom
        # the active domain is a new input relation: the user supplies it
        adom_input = Program(f'{adom}(_).') if adom is not None else None

        q = program
        for _ in range(max_passes):
            # Stop when the only rules left that fail the refined
            # range-restriction check are residue: recovery/open rules whose
            # openness is irreducible without an active domain.
            types = q.type_analysis()
            if not open_types(q, types=types): break
            new = q.abbreviate(types=types, adom=adom)
            if adom is not None:
                new.set_input_types((new.inputs or Program([])) + adom_input)
            if prune: new = new.prune_very_fast()
            if len(new.rules) == len(q.rules) and all(
                    str(a) == str(b) for a, b in zip(new.rules, q.rules)):
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
                break

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
