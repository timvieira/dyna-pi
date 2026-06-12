"""
Range-restriction analysis (docs/range-restriction-normalization.md, Step A).

Two analyses live here:

- `bindable_vars(program, rule)`: the per-rule dataflow computing which
  variables a bottom-up firing can bind — variables of range-generating
  subgoals, closed under propagation through the binder builtins (`=`, `is`).
  Tests (the comparison builtins, `$not_matches`) generate nothing, so a
  test-only variable is *not* bindable even though it occurs in the body.
  This refines the purely syntactic `Program.is_range_restricted`
  (`head_vars ⊆ body_vars`), which wrongly accepts `f(X) += g(Y) * (X > Y)`.

- `open_types(program)`: the openness fixpoint — the `$free`-marked derivable
  item types of the program, computed by the existing type analysis over the
  booleanized, `$free`-instrumented program (`to_type_program`).  The carrier
  is term patterns, so openness is tracked at any depth and intra-term sharing
  is preserved; there is no (functor, position) carrier anywhere.

Note the deliberate asymmetry between the two notions (this is where the spec's
E5 is sharpened): a `$free` mark asserts *pass-through* — the item's value is
independent of the marked variable — which licenses projection.  A test-only
variable is non-bindable (the rule is not range-restricted) but it is NOT
pass-through: in `f(X) += g(Y) * (X > Y)` the value of `f(X)` depends on `X`.
Projecting it would corrupt ground queries (`f(2)` must be 0 when `g(3)=1`),
so such a rule is irreducibly non-range-restricted without an active domain;
under Step E, splicing `adom(X)` makes it range-restricted.
"""

from dyna import Term, term_vars, snap, is_var
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


def has_free(t):
    "True iff type `t` carries a `$free` mark (the type is open)."
    return any(isinstance(c, Term) and c.fn == '$free' for c in t.body)


def open_types(program, types=None, **kwargs):
    """
    The openness fixpoint (Step A): the `$free`-marked derivable item types of
    `program`.  `types` may be a precomputed `TypeAnalyzer`; otherwise the
    standard one is run (booleanization adds the `$free` base case per rule;
    input declarations participate through the analyzer's input types — a
    declared input arrives `$bound` unless its input type says `$free`;
    propagation through consumption is the type solver's job).
    """
    if types is None:
        types = program.type_analysis(**kwargs)
    return [t for t in types.chart if has_free(t)]
