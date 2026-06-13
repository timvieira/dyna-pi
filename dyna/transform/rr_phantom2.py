"""
Path-based phantom range-restriction normalization — the sound *and* invariant
version.

The flat phantom analysis (rr_phantom.py) is provably sound but not invariant:
wrapping a phantom variable in a functor (`g(w(X))`, `item(distraction, f(X))`)
defeats it, because it keys on top-level argument index and requires the head
argument to be a bare variable.

This module keys phantom-ness on **paths** instead.  A phantom is a variable
that occurs exactly once in the head (at any depth), is unconstrained, and whose
body occurrences are themselves at phantom paths.  Single-occurrence still
excludes diagonals (`path(I,I)`: the variable occurs twice), so soundness is
unchanged; but because the condition and the projection both work on the head's
*tree structure*, wrapping no longer hides the phantom.

Projection drops the phantom subterm at its path and encodes the surrounding
ground skeleton in a fresh functor (anti-unification, spec 3.2): `g(w(X))`
projects to a scalar `g\` with recovery `g(w(V)) += g\`.  No disjoint
case-splitting is performed, so no equality/disequality heuristic is needed —
the transform only acts when every rule of a predicate shares one head skeleton
with the phantom at a fixed path, and conservatively refuses (leaves as residue)
anything else.
"""

from dyna import TransformedProgram, Rule, Term, term_vars, snap, is_var
from dyna.term import Var
from dyna.builtin import is_builtin


# --------------------------------------------------------------- path utilities

def walk(t, prefix=()):
    "Yield (path, subterm) for every node of term `t`, root first."
    t = snap(t)
    yield prefix, t
    if isinstance(t, Term) and not is_builtin(t):
        for i, a in enumerate(t.args):
            yield from walk(a, prefix + (i,))


def var_leaf_paths(t):
    "Map each variable in `t` to the list of paths at which it occurs as a leaf."
    out = {}
    for path, node in walk(t):
        if is_var(node):
            out.setdefault(node, []).append(path)
    return out


def subterm_at(t, path):
    t = snap(t)
    for i in path:
        t = snap(t.args[i])
    return t


def ground_skeleton(t):
    "The head's ground structure, every variable leaf collapsed to a hole."
    t = snap(t)
    if is_var(t):
        return '#var'
    if isinstance(t, Term) and not is_builtin(t):
        return (t.fn, tuple(ground_skeleton(a) for a in t.args))
    return ('const', t)


def _matches_ground(lit, gs):
    """True iff `lit` reads a predicate consistently with definition skeleton
    `gs`.  A definition variable ('#var') is open, so a consumer may read
    anything there; a definition constant requires the consumer to supply
    exactly that constant (a variable would read beyond the definition)."""
    lit = snap(lit)
    if gs == '#var':
        return True
    if isinstance(gs, tuple) and gs and gs[0] == 'const':
        return not (isinstance(lit, Term) and not is_builtin(lit)) and lit == gs[1]
    if isinstance(gs, tuple) and len(gs) == 2 and isinstance(gs[1], tuple):
        fn, subs = gs
        if not isinstance(lit, Term) or is_builtin(lit) or lit.fn != fn or lit.arity != len(subs):
            return False
        return all(_matches_ground(lit.args[i], subs[i]) for i in range(len(subs)))
    return False


def skeleton_key(head, phantom_paths):
    """A hashable skeleton key: the head's ground structure with every variable
    leaf replaced by a hole, and phantom paths distinguished from kept paths.
    Two heads with the same key share structure and phantom layout."""
    def rec(t, path):
        t = snap(t)
        if is_var(t):
            return ('#phantom' if path in phantom_paths else '#kept')
        if isinstance(t, Term) and not is_builtin(t):
            return (t.fn, tuple(rec(a, path + (i,)) for i, a in enumerate(t.args)))
        return ('const', t)
    return rec(head, ())


# ------------------------------------------------------------- phantom analysis

def _rule_groups(program):
    groups = {}
    for r in program.rules:
        h = snap(r.head)
        if isinstance(h, Term):
            groups.setdefault((h.fn, h.arity), []).append(r)
    return groups


def _is_input_pred(program, fn, arity):
    return program.inputs is not None and any(
        isinstance(snap(t.head), Term) and snap(t.head).fn == fn and snap(t.head).arity == arity
        for t in program.inputs)


def _phantom_path_in_rule(program, r, path, P, gskel):
    """Is `path` a phantom-variable path of rule r's head, given phantom set P
    and per-predicate ground skeletons `gskel`?"""
    head = snap(r.head)
    try:
        V = subterm_at(head, path)
    except (IndexError, AttributeError):
        return False
    if not is_var(V):
        return False
    # (1) single occurrence in the head
    if len(var_leaf_paths(head).get(V, [])) != 1:
        return False
    # (2) not in any constraint/builtin
    for b in r.body:
        if program.is_const(b):
            continue
        if is_builtin(b):
            if V in term_vars(b):
                return False
            continue
        # (3) every body occurrence of V is at a phantom path of a literal that
        #     actually reads its predicate's projected skeleton.  The skeleton
        #     match is load-bearing: a predicate defined with a constant in an
        #     argument position (`b(X,a)`) read at a general position
        #     (`b(X,Y)`) is NOT projectable there, so V is not phantom -- else
        #     V is left as a free summed variable and the rule blows up to inf.
        if V not in term_vars(b):
            continue
        bh = snap(b)
        gs = gskel.get((bh.fn, bh.arity))
        if gs is None or not _matches_ground(bh, gs):
            return False
        for p2 in var_leaf_paths(bh).get(V, []):
            if (bh.fn, bh.arity, p2) not in P:
                return False
    return True


def phantom_paths(program):
    """Least-fixpoint set of provably-phantom `(fn, arity, path)` triples, where
    every rule of the predicate has a single-occurrence unconstrained variable
    at that path, with phantom body occurrences."""
    groups = _rule_groups(program)
    # candidate paths: variable-leaf paths appearing in some head of the group
    candidates = {}
    # per-predicate uniform ground skeleton (None if rules disagree -> not projectable)
    gskel = {}
    for key, rules in groups.items():
        paths = set()
        for r in rules:
            for p, node in walk(r.head):
                if is_var(node):
                    paths.add(p)
        candidates[key] = paths
        gs = {ground_skeleton(snap(r.head)) for r in rules}
        gskel[key] = next(iter(gs)) if len(gs) == 1 else None

    P = set()
    changed = True
    while changed:
        changed = False
        for (fn, arity), rules in groups.items():
            if _is_input_pred(program, fn, arity) or gskel[(fn, arity)] is None:
                continue
            for path in candidates[(fn, arity)]:
                if (fn, arity, path) in P:
                    continue
                if all(_phantom_path_in_rule(program, r, path, P, gskel) for r in rules):
                    # require a uniform skeleton across rules (sound, conservative)
                    keys = {skeleton_key(snap(r.head),
                                         {p for (f, a, p) in P | {(fn, arity, path)}
                                          if (f, a) == (fn, arity)})
                            for r in rules}
                    if len(keys) == 1:
                        P.add((fn, arity, path))
                        changed = True
    return P


# --------------------------------------------------------------- the transform

def _matches_skeleton(literal, sk):
    "True iff `literal`'s ground structure matches skeleton key `sk`."
    literal = snap(literal)
    if sk in ('#phantom', '#kept'):
        return True
    if isinstance(sk, tuple) and sk and sk[0] == 'const':
        return not isinstance(literal, Term) and literal == sk[1]
    if isinstance(sk, tuple) and len(sk) == 2 and isinstance(sk[1], tuple):
        fn, subs = sk
        if not isinstance(literal, Term) or literal.fn != fn or literal.arity != len(subs):
            return False
        return all(_matches_skeleton(literal.args[i], subs[i]) for i in range(len(subs)))
    return False


class RangeRestrictionPhantomPath(TransformedProgram):
    """Sound *and* invariant range-restriction normalization: phantom positions
    are identified and projected on the head's tree structure (paths), so
    wrapping cannot hide a phantom, and single-occurrence still excludes
    diagonals so soundness is preserved."""

    def __init__(self, program, adom=None):
        self.adom = adom
        P = phantom_paths(program)
        self._phantoms = P

        groups = _rule_groups(program)
        pred_phantoms = {}
        for (fn, arity, path) in P:
            pred_phantoms.setdefault((fn, arity), set()).add(path)

        names, kept_paths, skel = {}, {}, {}
        for key, paths in pred_phantoms.items():
            rep = snap(groups[key][0].head)
            names[key] = program._gen_functor(key[0] + '_p')
            allvar = {p for p, n in walk(rep) if is_var(n)}
            kept_paths[key] = sorted(allvar - paths)
            skel[key] = skeleton_key(rep, paths)

        def project_literal(t):
            "Rewrite a literal reading a projected predicate; return (term, phantom_vars)."
            t = snap(t)
            if not isinstance(t, Term) or is_builtin(t):
                return t, set()
            key = (t.fn, t.arity)
            if key not in names or not _matches_skeleton(t, skel[key]):
                return t, set()
            kargs = [subterm_at(t, k) for k in kept_paths[key]]
            pv = set()
            for ph in pred_phantoms[key]:
                pv |= term_vars(subterm_at(t, ph))
            return Term(names[key], *kargs), pv

        new_rules = []
        for r in program.rules:
            head = snap(r.head)
            new_head, _ = project_literal(head)
            new_body = []
            for b in r.body:
                nb, _ = project_literal(b)
                new_body.append(nb)
            r2 = Rule(new_head, *new_body)
            # multiplicity: a phantom var that vanished and was *summed* (not a
            # surviving head key) ranged over the universe
            vanished = term_vars(r) - term_vars(r2)
            summed = vanished - term_vars(head)
            for v in sorted(summed, key=str):
                if adom is not None:
                    r2 = Rule(r2.head, *r2.body, Term(adom, v))
                else:
                    r2 = Rule(r2.head, *r2.body, program.Semiring.multiple(float('inf')))
            new_rules.append(r2)

        # recovery rules (the residue): reconstruct the original head shape
        for key, paths in pred_phantoms.items():
            rep = snap(groups[key][0].head)
            kpaths = kept_paths[key]
            kept_vars = {k: Var() for k in kpaths}
            adom_guards = []

            def rebuild(t, path):
                t = snap(t)
                if is_var(t):
                    if path in paths:
                        v = Var()
                        if adom is not None:
                            adom_guards.append(Term(adom, v))
                        return v
                    return kept_vars[path]
                if isinstance(t, Term) and not is_builtin(t):
                    return Term(t.fn, *[rebuild(a, path + (i,)) for i, a in enumerate(t.args)])
                return t

            rec_head = rebuild(rep, ())
            rec_body = Term(names[key], *[kept_vars[k] for k in kpaths])
            new_rules.append(Rule(rec_head, rec_body, *adom_guards))

        super().__init__('rr-phantom-path', program, new_rules)
        from dyna.analyze.range_restriction import is_rule_range_restricted
        self.residual_layer = self.spawn(
            [r for r in self.rules if not is_rule_range_restricted(self, r)])
        self.engine_layer = self.spawn(
            [r for r in self.rules if is_rule_range_restricted(self, r)])
