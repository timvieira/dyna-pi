"""
Range-restriction analysis and normalization
(docs/range-restriction-normalization.md).

This module holds two things, both syntactic and sound — there is no dependence
on the type analysis's `$free`/`ALLOW_FREE_MERGE` machinery, which is unsound on
diagonals (it drops `path(I,I)`; see `test_abbreviate.py::todo_startpath3`):

- **The refined range-restriction check** — `bindable_vars(program, rule)`: the
  per-rule dataflow computing which variables a bottom-up firing can bind
  (variables of range-generating subgoals, closed under the binder builtins
  `=`/`is`; tests generate nothing).  It refines the purely syntactic
  `Program.is_range_restricted` (`head_vars ⊆ body_vars`), which wrongly accepts
  `f(X) += g(Y) * (X > Y)` — a test-only variable is non-bindable, hence not
  range-restricted, even though it occurs in the body.

- **The sound normalization** — `phantom_paths`, `PhantomProjection`,
  `ValueSplit`, and the `RangeRestrictionNormalizer` entry point (reached by
  `Program.normalize_range_restriction`).  Projection is gated by a *verifiable*
  condition (a phantom is a variable occurring exactly once in the head,
  unconstrained, with phantom body occurrences — single occurrence excludes
  diagonals), so it is sound by construction and invariant under wrapping.
  Overlapping constant/variable cases (`f(1)`/`f(X)`) are handled by a
  default+exception decomposition (sound by linearity of `+`).
"""


from dyna import TransformedProgram, Rule, Term, term_vars, snap, is_var, fresh
from dyna.term import Var
from dyna.builtin import is_builtin, cmps

# Builtins that only test their (already bound) arguments — they never bind.
TEST_FNS = frozenset(cmps) | {'$not_matches', '$free', '$bound'}

# Builtins that bind: `=` is unification; `is` evaluates and, in the engine,
# inverts (e.g. `X is Y + 1` runs with either side bound), so propagation
# through both is bidirectional.
BINDER_FNS = frozenset({'=', 'is'})


def _binder_equation(b):
    "Return the (lhs, rhs) pair of a binder builtin, else None."
    if isinstance(b, Term) and b.arity == 2 and b.fn in BINDER_FNS:
        return b.args
    return None


def bindable_vars(program, rule):
    """
    Variables of `rule` that a bottom-up firing can bind: variables occurring
    in a range-generating subgoal (a positive non-builtin body item), closed
    under propagation through the binder builtins.
    """
    bound = set()
    equations = []
    for b in rule.body:
        b = snap(b)
        if program.is_const(b):
            continue
        if is_var(b):
            # a variable subgoal evaluates an item already named elsewhere;
            # it binds nothing by itself
            continue
        if is_builtin(b):
            eq = _binder_equation(b)
            if eq is not None:
                equations.append(eq)
            # tests bind nothing
        else:
            bound |= term_vars(b)
    changed = True
    while changed:
        changed = False
        for lhs, rhs in equations:
            lv, rv = term_vars(lhs), term_vars(rhs)
            if rv <= bound and not (lv <= bound):
                bound |= lv
                changed = True
            if lv <= bound and not (rv <= bound):
                bound |= rv
                changed = True
    return bound


def is_rule_range_restricted(program, rule):
    """
    The refined per-rule range-restriction check: every head variable is
    bindable by a range-generating subgoal.  Strictly stronger than the
    syntactic `head_vars ⊆ body_vars` (tests and unbound builtin inputs do
    not generate).
    """
    return term_vars(rule.head) <= bindable_vars(program, rule)


def is_range_restricted(program):
    "Program-level version of the refined check."
    return all(is_rule_range_restricted(program, r) for r in program)


#______________________________________________________________________________
# Sound range-restriction normalization (the trustworthy sibling of
# `abbreviate`).  `abbreviate`'s projection decides pass-through with the
# `$free`/`ALLOW_FREE_MERGE` heuristic, which is unsound on diagonals
# (todo_startpath3 drops `path(I,I)`).  This projects only what a verifiable
# condition proves safe and conservatively refuses the rest.  Layers:
#   phantom_paths             - sound + invariant projectability analysis
#   PhantomProjection         - path-based projection (sees through wrapping)
#   ValueSplit                - default+exception for constant overlaps
#   RangeRestrictionNormalizer- entry: value-split then project

# =============================================================== path utilities

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


# =========================================================== phantom analysis
# Path-based (the projection gate) and a flat positional specialization (used by
# the value-split's per-position classification).

def _phantom_path_in_rule(program, r, path, P, gskel):
    """Is `path` a phantom-variable path of rule r's head, given phantom set P
    (of (fn, arity, path) triples) and per-predicate ground skeletons `gskel`?"""
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
    for b in r.body:
        if program.is_const(b):
            continue
        if is_builtin(b):
            if V in term_vars(b):
                return False           # (2) appears in a test/builtin
            continue
        if V not in term_vars(b):
            continue
        # (3) body occurrences at phantom paths of a literal that reads the
        #     predicate's ground skeleton.  The skeleton match is load-bearing:
        #     a predicate defined with a constant arg (`b(X,a)`) read at a
        #     general position (`b(X,Y)`) is not projectable there, else V is
        #     left summed and the rule blows up to inf.
        bh = snap(b)
        gs = gskel.get((bh.fn, bh.arity))
        if gs is None or not _matches_ground(bh, gs):
            return False
        for p2 in var_leaf_paths(bh).get(V, []):
            if (bh.fn, bh.arity, p2) not in P:
                return False
    return True


def phantom_paths(program):
    """Least-fixpoint set of provably-phantom `(fn, arity, path)` triples."""
    groups = _rule_groups(program)
    candidates, gskel = {}, {}
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


def _pos_phantom_in_rule(program, r, i, P):
    """Flat positional phantom check (top-level index `i`), used by the
    value-split's per-rule classification.  `P` is a set of (fn, arity, index)."""
    head = snap(r.head)
    if i >= len(head.args):
        return False
    V = snap(head.args[i])
    if not is_var(V):
        return False
    if any(V in term_vars(a) for j, a in enumerate(head.args) if j != i):
        return False
    for b in r.body:
        if program.is_const(b):
            continue
        if is_builtin(b):
            if V in term_vars(b):
                return False
            continue
        if V not in term_vars(b):
            continue
        bh = snap(b)
        for k, a in enumerate(bh.args):
            a = snap(a)
            if is_var(a) and a == V:
                if (bh.fn, bh.arity, k) not in P:
                    return False
            elif V in term_vars(a):
                return False
    return True


def phantom_positions(program):
    "Flat least-fixpoint of phantom `(fn, arity, index)` positions."
    groups = _rule_groups(program)
    P = set()
    changed = True
    while changed:
        changed = False
        for (fn, arity), rules in groups.items():
            if _is_input_pred(program, fn, arity):
                continue
            for i in range(arity):
                if (fn, arity, i) in P:
                    continue
                if all(_pos_phantom_in_rule(program, r, i, P) for r in rules):
                    P.add((fn, arity, i))
                    changed = True
    return P


# =============================================================== projection

class PhantomProjection(TransformedProgram):
    """Project every phantom path (path-based), encoding skeletons in fresh
    functors so the rewrite is invariant under wrapping and never touches a
    diagonal."""

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
            new_body = [project_literal(b)[0] for b in r.body]
            r2 = Rule(new_head, *new_body)
            # multiplicity: a phantom var that vanished and was *summed* (not a
            # surviving head key) ranged over the universe
            for v in sorted((term_vars(r) - term_vars(r2)) - term_vars(head), key=str):
                factor = Term(adom, v) if adom is not None else program.Semiring.multiple(float('inf'))
                r2 = Rule(r2.head, *r2.body, factor)
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

        super().__init__('phantom-projection', program, new_rules)
        self.residual_layer = self.spawn(
            [r for r in self.rules if not is_rule_range_restricted(self, r)])
        self.engine_layer = self.spawn(
            [r for r in self.rules if is_rule_range_restricted(self, r)])


# =============================================================== value-split

def _drop_arg(t, i, newfn):
    return Term(newfn, *[t.args[j] for j in range(t.arity) if j != i])


def _classify(program, rules, i, P):
    """Classify position i across a predicate's rules: every rule must have a
    constant ('spec') or a single-occurrence unconstrained variable ('gen') at
    position i, with at least one of each.  `P` is the flat phantom set."""
    spec, gen = [], []
    for r in rules:
        arg = snap(snap(r.head).args[i])
        if is_var(arg):
            if _pos_phantom_in_rule(program, r, i, P):
                gen.append(r)
            else:
                return None
        elif program.is_const(arg) or (isinstance(arg, Term) and not is_var(arg)):
            if term_vars(arg):
                return None            # structured-with-vars -> out of scope
            spec.append(r)
        else:
            return None
    return (spec, gen) if (spec and gen) else None


class ValueSplit(TransformedProgram):
    """Default+exception decomposition for constant/variable overlaps
    (`f(1)`/`f(X)`): f = f_default + f_spec, sound by linearity of `+`."""

    def __init__(self, program):
        groups = _rule_groups(program)
        P = phantom_positions(program)

        splits = {}   # (fn,arity) -> (i, spec_rules, gen_rules)
        for key, rules in groups.items():
            if _is_input_pred(program, *key):
                continue
            for i in range(key[1]):
                c = _classify(program, rules, i, P)
                if c is not None:
                    splits[key] = (i, c[0], c[1])
                    break

        default_fn = {k: program._gen_functor(k[0] + '_dft') for k in splits}
        spec_fn = {k: program._gen_functor(k[0] + '_spc') for k in splits}

        def split_read(t):
            "If t reads a split predicate at a variable position, return (default_lit, spec_lit)."
            t = snap(t)
            if not isinstance(t, Term) or is_builtin(t):
                return None
            key = (t.fn, t.arity)
            if key not in splits:
                return None
            i = splits[key][0]
            if not is_var(snap(t.args[i])):
                return None            # constant read -> leave reading recovered f
            return _drop_arg(t, i, default_fn[key]), Term(spec_fn[key], *t.args)

        new_rules = []

        # 1. definitions: default (projected) + spec (renamed) + recovery
        for key, (i, spec, gen) in splits.items():
            fn, arity = key
            for r in gen:
                head = snap(fresh(r).head)
                new_rules.append(Rule(_drop_arg(head, i, default_fn[key]), *fresh(r).body))
            for r in spec:
                r = fresh(r)
                new_rules.append(Rule(Term(spec_fn[key], *snap(r.head).args), *r.body))
            fvars = [Var() for _ in range(arity)]
            new_rules.append(Rule(Term(fn, *fvars),
                                  Term(default_fn[key], *[fvars[j] for j in range(arity) if j != i])))
            new_rules.append(Rule(Term(fn, *fvars), Term(spec_fn[key], *fvars)))

        # 2. consumers: split each body read of a split predicate at a variable
        for r in program.rules:
            head = snap(r.head)
            if (head.fn, head.arity) in splits:
                continue
            positions = [k for k, b in enumerate(r.body) if split_read(b) is not None]
            if not positions:
                new_rules.append(fresh(r))
                continue
            k = positions[0]
            dft_lit, spc_lit = split_read(r.body[k])
            body_d = list(r.body); body_d[k] = dft_lit
            rd = Rule(head, *body_d)
            for v in sorted((term_vars(r) - term_vars(rd)) - term_vars(head), key=str):
                rd = Rule(rd.head, *rd.body, program.Semiring.multiple(float('inf')))
            new_rules.append(rd)
            body_s = list(r.body); body_s[k] = spc_lit
            new_rules.append(Rule(head, *body_s))

        super().__init__('value-split', program, new_rules)
        self._splits = splits
        self.residual_layer = self.spawn(
            [r for r in self.rules if not is_rule_range_restricted(self, r)])
        self.engine_layer = self.spawn(
            [r for r in self.rules if is_rule_range_restricted(self, r)])


# =============================================================== entry point

class RangeRestrictionNormalizer(TransformedProgram):
    """Sound, invariant range-restriction normalization: value-split the
    constant overlaps, then project the phantom positions."""

    def __init__(self, program, adom=None):
        projected = PhantomProjection(ValueSplit(program), adom=adom)
        super().__init__('rr-normalize-sound', program, list(projected))
        self.residual_layer = self.spawn(
            [r for r in self.rules if not is_rule_range_restricted(self, r)])
        self.engine_layer = self.spawn(
            [r for r in self.rules if is_rule_range_restricted(self, r)])
