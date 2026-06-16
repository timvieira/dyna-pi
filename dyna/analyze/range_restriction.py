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


from itertools import combinations

from dyna import TransformedProgram, Rule, Term, term_vars, snap, is_var, fresh
from dyna.term import Var, Subst
from dyna.builtin import is_builtin, cmps

# Builtins that only test their (already bound) arguments — they never bind.
TEST_FNS = frozenset(cmps) | {'$not_matches', '$free', '$bound'}

# Builtins that bind.  `=` is unification, so it propagates *both* ways (either
# side bound binds the other).  `is` only evaluates its right side and assigns
# the result to its left, so it propagates one way (RHS bound -> LHS bound); it
# does not invert in general -- `6 is Y * Z` cannot solve for Y, Z and faults at
# runtime -- so a head variable reachable only by inverting `is` is *not*
# bindable.
BINDER_FNS = frozenset({'=', 'is'})


def _binder_equation(b):
    "Return the (fn, lhs, rhs) triple of a binder builtin, else None."
    if isinstance(b, Term) and b.arity == 2 and b.fn in BINDER_FNS:
        return (b.fn, b.args[0], b.args[1])
    return None


def bindable_vars(program, rule):
    """
    Variables of `rule` that a bottom-up firing can bind: variables occurring
    in a range-generating subgoal (a positive non-builtin body item), closed
    under propagation through the binder builtins (`=` both ways, `is` only
    RHS -> LHS).
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
        for fn, lhs, rhs in equations:
            lv, rv = term_vars(lhs), term_vars(rhs)
            # forward (RHS evaluated -> LHS assigned): both `=` and `is`
            if rv <= bound and not (lv <= bound):
                bound |= lv
                changed = True
            # backward (LHS -> RHS): only unification `=`, never `is`
            if fn == '=' and lv <= bound and not (rv <= bound):
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
    """The **greatest**-fixpoint set of phantom `(fn, arity, path)` triples:
    assume every head variable position is phantom, then remove any that
    violates the condition given the current set.  The greatest fixpoint (vs a
    least one) is what captures *self-recursive* phantoms — e.g. the lifted
    geometric series `x(I) += 1. x(I) += 0.5*x(I)`, where `I` is phantom only
    because `x`'s position is phantom.  Soundness is unchanged on diagonals:
    single-occurrence (condition (1)) excludes them regardless of fixpoint
    direction."""
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

    # start optimistic: every candidate position of a projectable predicate
    P = {(fn, arity, path)
         for (fn, arity), rules in groups.items()
         if not _is_input_pred(program, fn, arity) and gskel[(fn, arity)] is not None
         for path in candidates[(fn, arity)]}

    changed = True
    while changed:
        changed = False
        for (fn, arity), rules in groups.items():
            for path in list(candidates[(fn, arity)]):
                if (fn, arity, path) in P and not all(
                        _phantom_path_in_rule(program, r, path, P, gskel) for r in rules):
                    P.discard((fn, arity, path))
                    changed = True
            # a predicate must keep a uniform skeleton across rules given P;
            # if not, none of its positions is projectable
            keys = {skeleton_key(snap(r.head),
                                 {p for (f, a, p) in P if (f, a) == (fn, arity)})
                    for r in rules}
            if len(keys) > 1:
                for path in list(candidates[(fn, arity)]):
                    if (fn, arity, path) in P:
                        P.discard((fn, arity, path))
                        changed = True
    return P


def _leaf_paths(t):
    "Paths of the var/const leaves of `t` -- the positions a projection keeps as args."
    return sorted(p for p, n in walk(t)
                  if is_var(n) or not (isinstance(n, Term) and not is_builtin(n)))


def _droppable_var_at(program, r, p, P):
    """The variable at tree path `p` of rule `r`'s head is droppable: it occurs
    exactly once in the head, is unconstrained by any builtin/test, and its body
    occurrences (if any) sit at droppable paths `P` (a set of (fn, arity, path)).
    The path generalization of the value-split's old flat positional check --
    used to classify the `gen` (variable) rules at any depth."""
    head = snap(r.head)
    try:
        V = subterm_at(head, p)
    except (IndexError, AttributeError):
        return False
    if not is_var(V):
        return False
    if len(var_leaf_paths(head).get(V, [])) != 1:
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
        for p2 in var_leaf_paths(bh).get(V, []):
            if (bh.fn, bh.arity, p2) not in P:
                return False
    return True


def _path_classify(program, rules, p, P):
    """Classify a predicate's rules at tree path `p`: each rule has a *ground*
    subterm there (`spec`) or a single-occurrence droppable variable (`gen`),
    with at least one of each, and the `gen` rules share a structural shape so
    the default projection (drop `p`, keep the rest) is well-defined.  Returns
    `(spec, gen)` or None."""
    spec, gen, gen_shapes = [], [], set()
    for r in rules:
        head = snap(r.head)
        try:
            sub = snap(subterm_at(head, p))
        except (IndexError, AttributeError):
            return None
        if is_var(sub):
            if not _droppable_var_at(program, r, p, P):
                return None
            gen.append(r)
            gen_shapes.add(_shape(head))
        elif not term_vars(sub):              # ground constant or ground compound
            spec.append(r)
        else:
            return None                       # structured-with-vars -> out of scope
    if not (spec and gen) or len(gen_shapes) != 1:
        return None
    return spec, gen


# ===================================================== sound pattern derivation
# A position can be value-relevant for a predicate yet still soundly droppable
# from a *quotient* item that the predicate appears in: a slash item `g/d` whose
# numerator and denominator share that position has the position cancel under the
# division (and it is re-supplied by the denominator when the quotient is
# multiplied back -- the slash recovery rule).  The sharing is a *derived*
# invariant (the raw slash rule writes distinct span variables; only the fixpoint
# shows `g` and `d` always agree there), so we recover it with a sound abstract
# forward chaining over term patterns -- `Program.step` (the engine's consequence
# operator) widened by depth truncation and deduplicated by subsumption.  No type
# analysis, no `$free`: every ground derivable item matches some derived pattern,
# and the only approximation (truncation/subsumption) widens, so the cover stays
# sound.  This is the trustworthy replacement for what the type analysis derived.

def _truncate(x, depth):
    "Depth-bounded widening: terms below `depth` collapse to a fresh variable."
    x = snap(x)
    if depth <= 0:
        return Var()
    if is_var(x):
        return x
    if isinstance(x, Term) and not is_builtin(x):
        return Term(x.fn, *[_truncate(a, depth - 1) for a in x.args])
    return x


def _one_way_match(g, s, sub):
    "Return a binding of g's variables making g == s (s an instance of g), or None."
    g, s = snap(g), snap(s)
    if is_var(g):
        if g in sub:
            return sub if sub[g] == s else None
        sub = dict(sub)
        sub[g] = s
        return sub
    if is_var(s):
        return None
    if isinstance(g, Term) and isinstance(s, Term):
        if g.fn != s.fn or g.arity != s.arity:
            return None
        for a, b in zip(g.args, s.args):
            sub = _one_way_match(a, b, sub)
            if sub is None:
                return None
        return sub
    return sub if g == s else None


def _subsumes(g, s):
    "True iff pattern `g` covers `s` (i.e. `s` is an instance of `g`)."
    return _one_way_match(fresh(g), s, {}) is not None


def _mgs_add(heads, h, max_depth):
    "Insert head pattern `h` into the most-general set `heads` (in place)."
    h = fresh(_truncate(h, max_depth))
    if any(_subsumes(g, h) for g in heads):
        return False
    heads[:] = [g for g in heads if not _subsumes(h, g)]
    heads.append(h)
    return True


def _reachable_patterns(program, input_type=None, max_depth=6, max_iters=200):
    """Core of `reachable_patterns`; returns `(heads, converged)`.  `converged`
    is False if the cap was hit before the fixpoint stabilized -- the truncated
    pattern lattice is finite so this never happens in practice, but a caller
    that relies on completeness (`quotient_cancelling_paths`) must refuse rather
    than trust a partial cover (an undrived pattern could be the one that breaks
    a num/den agreement)."""
    src = input_type if input_type is not None else program.inputs
    heads = []
    if src is not None:
        for t in src:
            _mgs_add(heads, snap(t.head), max_depth)
    for _ in range(max_iters):
        chart = program.spawn([Rule(fresh(h)) for h in heads])
        changed = False
        for r in program.step(chart):
            if _mgs_add(heads, snap(r.head), max_depth):
                changed = True
        if not changed:
            return heads, True
    return heads, False


def reachable_patterns(program, input_type=None, max_depth=6, max_iters=200):
    """A sound over-approximation of the program's derivable items as a set of
    head term-patterns: every ground derivable item is an instance of some
    returned pattern.  Computed by abstract forward chaining (`Program.step`)
    over a chart of patterns, widened by depth-`max_depth` truncation and kept
    as a most-general set under subsumption.  `input_type` (default
    `program.inputs`) seeds the input predicates."""
    return _reachable_patterns(program, input_type, max_depth, max_iters)[0]


# =============================================== quotient-cancellation analysis
# A `/` (slash/quotient) item `num / den` divides `den` out of `num`.  A position
# that the derived patterns show is *always shared* between `num` and `den` at the
# same sub-path therefore cancels: the item's value does not depend on it (the
# engine's own open solver returns such items with that position a free variable),
# and the denominator re-supplies it on recovery.  Dropping it is sound.  Crucially
# this fires *only* for `/` items -- a plain diagonal like `path(I,I)` is not a
# quotient, nothing cancels, and it is correctly left alone (the startpath3 trap).

def _link_classes(patterns):
    """Partition the variable leaf-paths of a predicate's head patterns into
    classes that carry the *same* variable in *every* pattern (union-find over
    pairwise agreement)."""
    paths = sorted({p for h in patterns for p, n in walk(h) if is_var(n)})
    parent = {p: p for p in paths}

    def find(x):
        root = x
        while parent[root] != root:
            root = parent[root]
        while parent[x] != root:
            parent[x], x = root, parent[x]
        return root

    def same_var_at(h, p1, p2):
        try:
            a, b = subterm_at(h, p1), subterm_at(h, p2)
        except (IndexError, AttributeError):
            return False
        return is_var(a) and is_var(b) and a == b

    for p1, p2 in combinations(paths, 2):
        if all(same_var_at(h, p1, p2) for h in patterns):
            parent[find(p1)] = find(p2)
    classes = {}
    for p in paths:
        classes.setdefault(find(p), set()).add(p)
    return [frozenset(c) for c in classes.values()]


def _shape(t):
    "Structural shape of `t`: functor tree with every var/const leaf collapsed."
    t = snap(t)
    if isinstance(t, Term) and not is_builtin(t):
        return (t.fn, tuple(_shape(a) for a in t.args))
    return '#leaf'


def _is_slash(x):
    x = snap(x)
    return isinstance(x, Term) and x.fn == '/' and x.arity == 2


def _count_var(t, v):
    "Number of times variable `v` occurs in `t` (including inside builtins)."
    t = snap(t)
    if is_var(t):
        return 1 if t == v else 0
    if isinstance(t, Term):
        return sum(_count_var(a, v) for a in t.args)
    return 0


def _at_cancel_count(rule_terms, v, P):
    "Occurrences of `v` at cancelling positions of any `/` item (per `P`)."
    c = 0
    for x in rule_terms:
        if not _is_slash(x):
            continue
        paths = P.get(_shape(x))
        if not paths:
            continue
        for p in paths:
            try:
                if snap(subterm_at(x, p)) == v:
                    c += 1
            except (IndexError, AttributeError):
                pass
    return c


def _bad_cancel_subpaths(program, shape, P):
    """The num/den sub-paths of `shape` that do NOT cancel soundly: in some
    **definition** rule (head a `/` item of `shape`), after unifying the num/den
    pairs of every still-cancelling `/` item, the variable at that position also
    occurs at a non-cancelling position -- so the value depends on it.  A
    cancelled variable may pass through cancelling positions of *another* quotient
    (the CCG head word flows constit/rconstit -> rconstit/rconstit), but reaching
    an ordinary factor (`(p(X)/p(X)) += g(X)`, or `rewrite(X:H,...)` for the head
    word) is value-determining and unsound.  Returned as sub-paths so both the
    numerator and denominator occurrence of a bad class are dropped together."""
    cancel = P[shape]

    def cancel_paths_of(x):
        return P.get(_shape(x)) if _is_slash(x) else None

    bad = set()
    for r in program.rules:
        if not (_is_slash(snap(r.head)) and _shape(snap(r.head)) == shape):
            continue              # only the quotient's own definitions constrain its value
        r = fresh(r)
        terms = [snap(r.head), *map(snap, r.body)]
        sub = Subst()
        for x in terms:
            paths = cancel_paths_of(x)
            if not paths:
                continue
            for s in sorted({p[1:] for p in paths}):
                try:
                    a, b = subterm_at(x, (0,) + s), subterm_at(x, (1,) + s)
                except (IndexError, AttributeError):
                    continue
                sub = sub.mgu(a, b)
                if sub is Subst.FAIL:
                    return {p[1:] for p in cancel}      # whole shape unsound
        rt = [sub(x) for x in terms]
        for p in cancel:
            for x in rt:
                if not (_is_slash(x) and _shape(x) == shape):
                    continue
                try:
                    node = snap(subterm_at(x, p))
                except (IndexError, AttributeError):
                    continue
                for v in term_vars(node):
                    if sum(_count_var(t, v) for t in rt) != _at_cancel_count(rt, v, P):
                        bad.add(p[1:])
    return bad


def quotient_cancelling_paths(program, input_type=None):
    """Map each `/`-item shape to the set of paths that are soundly droppable: a
    path that the derived patterns prove is shared between the numerator (sub-path
    under arg 0) and the denominator (the matching sub-path under arg 1) in every
    pattern of that shape, *and* whose cancelled variable does not also drive the
    value through an ordinary factor (`_bad_cancel_subpaths`, a greatest fixpoint
    over all shapes, refined per sub-path: e.g. the CCG `constit/rconstit` cancels
    the right span but not the head word).  Keyed by shape so distinct slash items
    (`c/c` vs `goal/c`) are analyzed separately.  A quotient that is itself a
    declared output is skipped (projecting it loses recovery)."""
    heads, converged = _reachable_patterns(program, input_type)
    if not converged:
        return {}                # incomplete cover -> refuse (sound)
    pats = [h for h in heads
            if isinstance(h, Term) and h.fn == '/' and h.arity == 2]
    groups = {}
    for h in pats:
        groups.setdefault(_shape(h), []).append(h)

    # candidate cancel set per shape (num/den shared), skipping output quotients
    P = {}
    for shape, group in groups.items():
        if any(program.is_output(h) for h in group):
            continue             # a queried quotient has no recovery -- leave it
        cancel = set()
        for cls in _link_classes(group):
            num = {p[1:] for p in cls if p and p[0] == 0}
            den = {p[1:] for p in cls if p and p[0] == 1}
            shared = num & den                  # same sub-path in num and den
            if shared:
                cancel |= {p for p in cls if p and p[1:] in shared}
        if cancel:
            P[shape] = frozenset(cancel)

    # greatest fixpoint: drop any sub-path whose cancelled variable escapes the
    # (shrinking) cancelling set into a value-determining factor
    changed = True
    while changed:
        changed = False
        for shape in list(P):
            bad = _bad_cancel_subpaths(program, shape, P)
            if bad:
                P[shape] = frozenset(p for p in P[shape] if p[1:] not in bad)
                if not P[shape]:
                    del P[shape]
                changed = True
    return dict(P)


# =================================================== quotient projection
# Degree reduction for slash/LCT items, justified by the cancellation analysis
# rather than the unsound `$free` heuristic.

class QuotientProjection(TransformedProgram):
    """Drop the positions that cancel under a `/` quotient (the num/denom-shared
    positions found by `quotient_cancelling_paths`): in every rule, unify each
    cancelling numerator/denominator pair (the sharing the derivation proved
    always holds), then replace each `/` item by a lower-arity item that keeps
    only the non-cancelling subterms, encoding the dropped skeleton in a fresh
    functor.  Sound -- the dropped position cancels in the division and is
    re-supplied by the surviving factors -- and strictly degree-reducing.  A
    no-op when the program has no quotient (e.g. `startpath3`)."""

    def __init__(self, program, input_type=None):
        cancel_by_shape = quotient_cancelling_paths(program, input_type)
        self._cancelling = cancel_by_shape

        names, kept = {}, {}

        def cancel_of(x):
            "The cancelling paths for `/` item `x`, or None if it does not reduce."
            return cancel_by_shape.get(_shape(x)) if _is_slash(x) else None

        def name_skeleton(x, cancel):
            def rec(t, path):
                if path in cancel:
                    return '#drop'
                t = snap(t)
                if isinstance(t, Term) and not is_builtin(t):
                    return (t.fn, tuple(rec(a, path + (i,)) for i, a in enumerate(t.args)))
                return '#keep'
            return rec(x, ())

        def project_item(x):
            x = snap(x)
            cancel = cancel_of(x)
            if cancel is None:
                return x
            sk = name_skeleton(x, cancel)
            if sk not in names:
                names[sk] = program.gen_functor('slash')   # globally-unique functor
                kept[sk] = sorted(
                    p for p, n in walk(x)
                    if p not in cancel
                    and (is_var(n) or not (isinstance(n, Term) and not is_builtin(n))))
            return Term(names[sk], *[subterm_at(x, k) for k in kept[sk]])

        def project_rule(r):
            r = fresh(r)
            sub = Subst()
            for x in [snap(r.head), *map(snap, r.body)]:
                cancel = cancel_of(x)
                if cancel is None:
                    continue
                for s in sorted({p[1:] for p in cancel}):   # shared num<->den sub-paths
                    try:
                        a, b = subterm_at(x, (0,) + s), subterm_at(x, (1,) + s)
                    except (IndexError, AttributeError):
                        continue
                    sub = sub.mgu(a, b)
                    if sub is Subst.FAIL:
                        return fresh(r)        # inconsistent (never, given the analysis)
            uhead = sub(snap(r.head))
            ubody = [sub(snap(b)) for b in r.body]
            r2 = Rule(project_item(uhead), *[project_item(b) for b in ubody])
            # multiplicity: a cancelled variable that vanished and was *summed* by
            # this rule (not a surviving head key) ranged over the universe -- the
            # quotient analogue of PhantomProjection's `inf` correction.  E.g.
            # `goal += (p(X)/p(X))` sums X over an open quotient, so goal = inf.
            unified = Rule(uhead, *ubody)
            for v in sorted((term_vars(unified) - term_vars(r2)) - term_vars(uhead), key=str):
                r2 = Rule(r2.head, *r2.body, program.Semiring.multiple(float('inf')))
            return r2

        new_rules = ([project_rule(r) for r in program.rules]
                     if cancel_by_shape else list(program.rules))
        super().__init__('quotient-projection', program, new_rules)
        self.residual_layer = self.spawn(
            [r for r in self.rules if not is_rule_range_restricted(self, r)])
        self.engine_layer = self.spawn(
            [r for r in self.rules if is_rule_range_restricted(self, r)])


# =============================================================== projection

class PhantomProjection(TransformedProgram):
    """Project every phantom path (path-based), encoding skeletons in fresh
    functors so the rewrite is invariant under wrapping and never touches a
    diagonal."""

    def __init__(self, program):
        P = phantom_paths(program)
        self._phantoms = P

        groups = _rule_groups(program)
        pred_phantoms = {}
        for (fn, arity, path) in P:
            pred_phantoms.setdefault((fn, arity), set()).add(path)

        names, kept_paths, skel = {}, {}, {}
        for key, paths in pred_phantoms.items():
            rep = snap(groups[key][0].head)
            # include the arity so f/1 and f/2 get distinct names (`_gen_functor`
            # only avoids the original program's symbols, not other fresh names)
            names[key] = program._gen_functor(f'{key[0]}_{key[1]}_p')
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
            # surviving head key) ranged over the universe -- an `inf` witness count
            for v in sorted((term_vars(r) - term_vars(r2)) - term_vars(head), key=str):
                r2 = Rule(r2.head, *r2.body, program.Semiring.multiple(float('inf')))
            new_rules.append(r2)

        # recovery rules (the residue): reconstruct the original head shape.  A
        # dropped phantom position becomes a fresh, unconstrained variable, so the
        # recovery rule is open -- that is the irreducible residual layer, kept as
        # is (the normalizer is strictly semantics-preserving; it does not splice
        # an active domain).
        for key, paths in pred_phantoms.items():
            rep = snap(groups[key][0].head)
            kpaths = kept_paths[key]
            kept_vars = {k: Var() for k in kpaths}

            def rebuild(t, path):
                t = snap(t)
                if is_var(t):
                    return Var() if path in paths else kept_vars[path]
                if isinstance(t, Term) and not is_builtin(t):
                    return Term(t.fn, *[rebuild(a, path + (i,)) for i, a in enumerate(t.args)])
                return t

            rec_head = rebuild(rep, ())
            rec_body = Term(names[key], *[kept_vars[k] for k in kpaths])
            new_rules.append(Rule(rec_head, rec_body))

        super().__init__('phantom-projection', program, new_rules)
        self.residual_layer = self.spawn(
            [r for r in self.rules if not is_rule_range_restricted(self, r)])
        self.engine_layer = self.spawn(
            [r for r in self.rules if is_rule_range_restricted(self, r)])


# =============================================================== value-split

class ValueSplit(TransformedProgram):
    """Default+exception decomposition for constant/variable overlaps, sound by
    linearity of `+`: `f = f_default + f_spec`.  Path-based, so it splits a
    constant against a variable at *any* tree depth -- `f(1)`/`f(X)` and
    `f(g(1))`/`f(g(X))` alike -- by dropping the variable subterm and keeping the
    surrounding skeleton in `f_default` (the `gen` rules must share that
    skeleton)."""

    def __init__(self, program):
        groups = _rule_groups(program)
        P = phantom_paths(program)

        splits = {}   # (fn,arity) -> (path, spec_rules, gen_rules)
        for key, rules in groups.items():
            if _is_input_pred(program, *key):
                continue
            candidates = sorted({p for r in rules
                                 for p, n in walk(snap(r.head)) if is_var(n)})
            for p in candidates:
                c = _path_classify(program, rules, p, P)
                if c is not None:
                    splits[key] = (p, c[0], c[1])
                    break

        # include the arity so distinct (fn, arity) predicates never share a name
        default_fn = {k: program._gen_functor(f'{k[0]}_{k[1]}_dft') for k in splits}
        spec_fn = {k: program._gen_functor(f'{k[0]}_{k[1]}_spc') for k in splits}
        # leaf paths kept by the default item (the gen skeleton minus the split path)
        kept = {key: [q for q in _leaf_paths(snap(gen[0].head)) if q != p]
                for key, (p, spec, gen) in splits.items()}
        gen_shape = {key: _shape(snap(gen[0].head)) for key, (p, spec, gen) in splits.items()}

        def project_default(t, key):
            "The default item: keep the leaf subterms of `t` except the split path."
            return Term(default_fn[key], *[subterm_at(t, q) for q in kept[key]])

        def split_read(t):
            "If t reads a split predicate at a variable (at the split path), split it."
            t = snap(t)
            if not isinstance(t, Term) or is_builtin(t):
                return None
            key = (t.fn, t.arity)
            if key not in splits or _shape(t) != gen_shape[key]:
                return None            # not the gen shape -> reads recovered f
            p = splits[key][0]
            if not is_var(snap(subterm_at(t, p))):
                return None            # constant read -> leave reading recovered f
            return project_default(t, key), Term(spec_fn[key], *t.args)

        new_rules = []

        # 1. definitions: default (projected) + spec (renamed) + recovery
        for key, (p, spec, gen) in splits.items():
            fn, arity = key
            for r in gen:
                r = fresh(r)               # one fresh copy: head and body must share variables
                new_rules.append(Rule(project_default(snap(r.head), key), *r.body))
            for r in spec:
                r = fresh(r)
                new_rules.append(Rule(Term(spec_fn[key], *snap(r.head).args), *r.body))
            # default recovery: rebuild the gen skeleton with a fresh var at every
            # leaf (the dropped path's var is open -- the value-split residue)
            rep = snap(gen[0].head)
            leafvar = {q: Var() for q in _leaf_paths(rep)}

            def rebuild(t, path):
                t = snap(t)
                if path in leafvar:
                    return leafvar[path]
                if isinstance(t, Term) and not is_builtin(t):
                    return Term(t.fn, *[rebuild(a, path + (i,)) for i, a in enumerate(t.args)])
                return t

            new_rules.append(Rule(rebuild(rep, ()),
                                  Term(default_fn[key], *[leafvar[q] for q in kept[key]])))
            fvars = [Var() for _ in range(arity)]
            new_rules.append(Rule(Term(fn, *fvars), Term(spec_fn[key], *fvars)))

        # 2. consumers: split each body read of a split predicate at the split path
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
    """Strictly semantics-preserving range-restriction normalization: value-split
    the constant overlaps, reduce slash/LCT quotients by cancellation, then
    project the phantom positions.  Each step is sound by a verifiable condition
    (no `$free` heuristic): `QuotientProjection` is a no-op without `/` items, so
    non-slash programs are unaffected.  Irreducibly open rules are kept in
    `residual_layer` and summed-away open variables keep their `inf` witness
    count -- the transform never restricts witnesses to an active domain (that
    would change answers under Dyna's open-universe semantics; if you want it,
    use a separate, explicitly named active-domain transform)."""

    def __init__(self, program):
        projected = PhantomProjection(QuotientProjection(ValueSplit(program)))
        super().__init__('rr-normalize-sound', program, list(projected))
        self.residual_layer = self.spawn(
            [r for r in self.rules if not is_rule_range_restricted(self, r)])
        self.engine_layer = self.spawn(
            [r for r in self.rules if is_rule_range_restricted(self, r)])
