"""
Range-restriction normalization, v2 — projection gated by a *provably sound*
phantom-position analysis instead of the `$free` / `ALLOW_FREE_MERGE` heuristic.

Motivation (see the startpath3 counterexample): the abbreviate-based projection
decides "is this position pass-through" with a type-merge heuristic whose
soundness is asserted, not proven, and which demonstrably drops the reflexive
diagonal `path(I,I)` (computing all-zero paths). This module replaces that
decision with a syntactic condition that *provably implies* pass-through, and is
conservative (it refuses to project anything it cannot prove safe).

Phantom position (the sound projectability condition).  A position `(p, i)` is
*phantom* iff, in **every** rule deriving `p`, the i-th head argument is a
variable `V` such that:

  (1) `V` occurs exactly once in the head (this excludes diagonals: in
      `path(I,I)` the variable occurs twice, so the position is never phantom);
  (2) `V` occurs in no test/builtin/constraint;
  (3) every occurrence of `V` in a positive body literal is itself at a
      top-level phantom position (propagation); a *nested* occurrence is refused.

Soundness (sketch).  By induction on the phantom least-fixpoint: a head-only,
single-occurrence, unconstrained `V` whose body occurrences sit only at phantom
positions cannot influence the rule's value — substituting any constant for `V`
leaves every body literal's value unchanged (base: `V` absent from the body;
step: each body literal is phantom at `V`'s position, so independent of it).
Hence `p`'s value is independent of coordinate `i`: pass-through holds.  The
fixpoint is built upward from base phantoms, so every member has a finite
soundness derivation; it is conservative, never aggressive.
"""

from dyna import TransformedProgram, Rule, Term, term_vars, snap, is_var, fresh
from dyna.term import Var
from dyna.builtin import is_builtin


def _is_var_eq(a, V):
    "True iff term `a` is exactly the variable `V` (a top-level occurrence)."
    a = snap(a)
    return is_var(a) and a == V


def _pos_phantom_in_rule(program, r, i, P):
    "Condition (1)-(3) for head position i of rule r, given phantom set P."
    head = snap(r.head)
    if i >= len(head.args):
        return False
    V = snap(head.args[i])
    if not is_var(V):
        return False
    # (1) single occurrence in the head
    for j, a in enumerate(head.args):
        if j == i:
            continue
        if V in term_vars(a):
            return False
    # (2) not in any constraint/builtin, and (3) body occurrences only at phantom positions
    for b in r.body:
        if program.is_const(b):
            continue
        if is_builtin(b):
            if V in term_vars(b):
                return False           # (2) appears in a test/builtin
            continue
        # positive literal
        if V not in term_vars(b):
            continue
        for k, a in enumerate(b.args):
            if _is_var_eq(a, V):
                if (b.fn, b.arity, k) not in P:
                    return False       # (3) body occurrence at a non-phantom position
            elif V in term_vars(a):
                return False           # (3) nested occurrence -> refuse (conservative)
    return True


def phantom_positions(program):
    "The least-fixpoint set of provably-phantom positions `(fn, arity, index)`."
    groups = {}
    for r in program.rules:
        h = snap(r.head)
        groups.setdefault((h.fn, h.arity), []).append(r)

    def is_input_pred(fn, arity):
        # any declared-input predicate arrives ground -> not phantom (safe)
        return program.inputs is not None and any(
            snap(t.head).fn == fn and snap(t.head).arity == arity for t in program.inputs)

    P = set()
    changed = True
    while changed:
        changed = False
        for (fn, arity), rules in groups.items():
            if is_input_pred(fn, arity):
                continue
            for i in range(arity):
                if (fn, arity, i) in P:
                    continue
                if all(_pos_phantom_in_rule(program, r, i, P) for r in rules):
                    P.add((fn, arity, i))
                    changed = True
    return P


def _project_term(t, P, names):
    "Drop t's phantom argument positions, renaming to the projected functor."
    t = snap(t)
    if not isinstance(t, Term) or is_builtin(t):
        return t
    drop = {i for i in range(t.arity) if (t.fn, t.arity, i) in P}
    if not drop:
        return t
    kept = [t.args[i] for i in range(t.arity) if i not in drop]
    return Term(names[(t.fn, t.arity)], *kept)


class RangeRestrictionPhantom(TransformedProgram):
    """Range-restriction normalization driven by the provably-sound phantom
    analysis.  Projects only phantom positions (never a diagonal or a
    constrained position), so it is value-preserving by construction."""

    def __init__(self, program, adom=None):
        self.adom = adom
        P = phantom_positions(program)
        self._phantoms = P

        # one fresh functor per predicate that loses at least one position
        preds = {(fn, arity) for (fn, arity, _) in P}
        names = {key: program._gen_functor(f'{key[0]}_proj') for key in preds}
        self._names = names

        new_rules = []

        # projected program rules
        for r in program.rules:
            r = fresh(r)
            head = snap(r.head)
            new_head = _project_term(head, P, names)
            new_body = [_project_term(b, P, names) for b in r.body]
            r2 = Rule(new_head, *new_body)
            # multiplicity: a variable that vanished and was *summed* (not a
            # surviving head key) ranged over the universe -> witness factor
            vanished = term_vars(r) - term_vars(r2)
            summed = vanished - term_vars(head)
            for v in sorted(summed, key=str):
                if adom is not None:
                    r2 = Rule(r2.head, *r2.body, Term(adom, v))   # |adom| per var
                else:
                    r2 = Rule(r2.head, *r2.body, program.Semiring.multiple(float('inf')))
            new_rules.append(r2)

        # recovery rules (the residue): re-express each projected predicate
        for (fn, arity), newfn in names.items():
            drop = sorted(i for i in range(arity) if (fn, arity, i) in P)
            allvars = [Var() for _ in range(arity)]   # fresh var per position
            kept = [allvars[i] for i in range(arity) if i not in drop]
            rec_head = Term(fn, *allvars)
            rec_body = Term(newfn, *kept)
            if adom is not None:
                guards = [Term(adom, allvars[i]) for i in drop]
                new_rules.append(Rule(rec_head, rec_body, *guards))
            else:
                new_rules.append(Rule(rec_head, rec_body))

        super().__init__('rr-phantom', program, new_rules)

        from dyna.analyze.range_restriction import is_rule_range_restricted
        self.residual_layer = self.spawn(
            [r for r in self.rules if not is_rule_range_restricted(self, r)])
        self.engine_layer = self.spawn(
            [r for r in self.rules if is_rule_range_restricted(self, r)])
