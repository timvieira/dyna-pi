# Range-Restriction Normalization

A rule is **range-restricted** when every head variable also occurs in a
*range-generating* body subgoal (a positive non-builtin item that evaluation can
produce ground). Range restriction keeps bottom-up firing ground, which is what
McAllester's runtime bound assumes. `Program.normalize_range_restriction()`
rewrites an arbitrary program into an equivalent one whose non-range-restriction
is confined to an explicit **residual layer** — the way ε-elimination in a CFG
pushes the one unavoidable case into a single `S0 → S | ε` rule.

Everything lives in one module, `dyna/analyze/range_restriction.py`, and depends
on **no** type analysis.

## The refined check

`bindable_vars(program, rule)` is the per-rule dataflow of the variables a
bottom-up firing can bind: variables of the positive non-builtin subgoals, closed
through the binder builtins — `=` both directions (unification), `is` only
right→left (it evaluates its RHS and cannot invert in general; `6 is Y*Z` faults).
Tests (`X > Y`, …) bind nothing. `is_rule_range_restricted` / `is_range_restricted`
refine the purely syntactic `head_vars ⊆ body_vars`, which wrongly accepts
`f(X) += g(Y) * (X > Y)` (a test-only variable is not bindable).

## The normalizer

`RangeRestrictionNormalizer` is `PhantomProjection(QuotientProjection(ValueSplit(p)))`.
Each step is sound by a *verifiable condition*, never a heuristic, and is
**path-keyed** — it keys on tree paths, not top-level argument indices, so it
handles depth, shared subterms, and recursive structure (no flatness assumption).

- **`ValueSplit`** — constant/variable overlap (`f(1)`/`f(X)`, or nested
  `f(g(1))`/`f(g(X))`) → `f = f_default + f_spec`, sound by linearity of `+`.
  Path-based: the overlap may sit at any depth; the variable subterm is dropped
  and the surrounding skeleton kept in `f_default` (the `gen` rules must share
  that skeleton).

- **`QuotientProjection`** — degree reduction for slash/LCT items, justified by
  *division*. A `/` item `num/den` cancels a position the derived patterns prove
  is shared between `num` and `den` at the same sub-path (it divides out and is
  re-supplied by the surviving factors). The sharing is a *derived* invariant —
  the raw slash rule
  writes distinct span variables — recovered by `reachable_patterns`, a sound
  abstract forward chaining (`Program.step` widened by depth truncation,
  deduplicated by subsumption). Three gates make the drop verifiable:
  - **pass-through** (`_bad_cancel_subpaths`, a greatest fixpoint per sub-path): a
    shared position cancels only if, in every quotient *definition* rule, its
    variable reaches only cancelling positions of `/` items — of any shape (the
    CCG head word flows `constit/rconstit → rconstit/rconstit`). If it reaches an
    ordinary factor the value depends on it (`(p(X)/p(X)) += g(X)`, or the head
    word in `rewrite(X:H,…)`) and the class is refused (so the CCG
    `constit/rconstit` cancels the right span but keeps the head word);
  - **multiplicity**: a summed-away cancelled variable keeps an `inf` witness
    count (`goal += (p(X)/p(X))` stays `inf`);
  - **recovery**: a quotient that is itself a declared output is left alone (it
    has no recovery), and distinct slash skeletons get distinct `gen_functor`
    names so independent closures never merge.
  Fires **only** for `/` items, so a plain diagonal like `path(I,I)` is left alone.

- **`PhantomProjection`** — drops a *phantom*: a variable occurring exactly once
  in the head, unconstrained, with body occurrences at phantom paths. Single
  occurrence excludes diagonals structurally; path-keying makes it invariant
  under wrapping (`f(X)` vs `w(f(X))`). The fresh functor name includes the arity
  so `f/1` and `f/2` never collide.

`residual_layer` / `engine_layer` are exposed.

## Strictly semantics-preserving

The normalizer preserves semiring values on every ground query. It does **not**
restrict witnesses to an active domain — that would change answers under Dyna's
open universe. Irreducibly open rules (e.g. the phantom recovery `x(I) += x_p`, or
a test-only-variable rule `f(X) += g(Y)*(X>Y)`) stay in `residual_layer`, and
summed-away open variables keep their `Semiring.multiple(inf)` witness count.
`normalize_range_restriction()` takes no arguments. If active-domain
"safe-ification" is ever wanted, it belongs in a *separate, explicitly named*
transform.

## Soundness

Every drop is justified by a verifiable condition, never a guess. A transform
either **proves non-overlap** (a single-occurrence phantom; a quotient position
that genuinely cancels under division) or **decomposes additively** (the
value-split, by linearity of `+`). When it cannot prove a drop safe it refuses,
leaving the rule in the residual layer.

Tests: `test/test_range_restriction_normalize.py` (and the slash/CKY/LCT
optimization cases in `test/test_abbreviate.py`, `test/test_lct.py`,
`test/test_type_analysis.py`).
