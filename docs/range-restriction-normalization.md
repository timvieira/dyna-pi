# Range-Restriction Normalization

> **Goal (for `/goal`).** Implement a semantics-preserving transform
> `RangeRestrictionNormalization` that rewrites an arbitrary Dyna program into an
> equivalent program that is range-restricted everywhere except for a single,
> explicitly identified residual layer at the outputs. The transform must
> preserve semiring values on every ground query, must terminate, and must be
> accompanied by tests that lock down both the engine equivalence and the shape
> of the residue. Acceptance criteria are in the "Definition of Done" section
> (Section 11); the milestones (Section 10) are ordered and each is
> independently verifiable.

This is a self-contained spec. It does not require reading
`abbreviation-design.md`, but the two are related: range-restriction
normalization and abbreviation are the same operation seen from two sides (see
"Relation to abbreviation"). Where this document and `abbreviation-design.md`
disagree, this document is the authority for the normalization transform only.

## 1. Problem

A rule is **range-restricted** when every variable in the head also occurs in a
range-generating subgoal of the body. Operationally: starting from ground facts,
a range-restricted program only ever asserts ground items; it never asserts an
"open" item (one containing a free variable). McAllester's meta-complexity
result assumes range restriction so that bottom-up firing stays ground and the
runtime bound (number of prefix firings) holds.

McAllester states that non-range-restricted rules can be avoided but, as far as
we can tell, does not develop the elimination. Dyna currently does not eliminate
them either: `dyna/transform/rule_elimination.py` detects the hard case and the
multiplicity-correcting branch is commented out (lines 64-94). The runtime
sidesteps the issue by switching to a non-ground solver
(`Program.is_range_restricted`, `dyna/program.py:858`, selects solver 1 vs 2).

We want the missing transform: take any program and produce an equivalent one
whose non-range-restriction is pushed into a single superficial layer at the
top, exactly the way ε-production elimination in a CFG pushes the one
unavoidable case into a single `S0 -> S | epsilon` rule.

## 2. The CFG correspondence (the mental model)

The construction is a term-by-term translation of ε-elimination. Keep this table
in mind; every step below is one of these rows.

```text
epsilon-elimination (CFG)            range-restriction normalization (Dyna)
-----------------------------------  -----------------------------------------
terminal alphabet                    universe / active domain of constants
nonterminal A                        item type t (a type-chart entry)
A is nullable  (A =>* epsilon)       t is open (carries a $free-marked variable)
epsilon-production A -> epsilon       non-range-restricted rule (free head var)
inline nullable occurrences,         split each open occurrence into a
  expand over subsets                  closed reading and an open reading
L(G') = L(G) \ {epsilon}             P' range-restricted, equals P on ground queries
residual S0 -> S | epsilon           single open output layer
  (S0 -> epsilon the only eps-rule)    (weighted: the inf * one factor)
```

The load-bearing fact in both settings: nullability/openness is a **least
fixpoint over a finite abstraction** — nonterminals there, the widened type
chart here — so the rewrite is a bounded, terminating, one-shot expansion. It is
*not* unbounded unfolding, which is why recursion is not a problem. Note the
finiteness argument: in a CFG the carrier (the nonterminal set) is finite by
fiat; in Dyna the carrier is item *types* (term patterns, Section 3.2) and
finiteness comes from the type analysis's widening — **not** from any finite set
of top-level argument slots.

## 3. Definitions

Fix a program `P` over semiring `S` with one-element `one` and a notion of
"witness multiplicity" already present in the engine (`Program.multiple`,
`Semiring.multiple`).

**Range-generating subgoal.** A positive body item occurrence that can be produced
ground by evaluation. Tests (`X < Y`, `X == Y` with both sides bound) and the
unbound inputs of builtins (the `Y` in `X is Y + 1`) are *not* range-generating.
Constants and ground subterms are fine.

**Range-restricted rule.** Every head variable occurs in some range-generating
subgoal of the body. `Program.is_range_restricted` is the existing program-level
predicate; the per-rule version is `not (term_vars(r.head) - term_vars(r.body))`
refined to "generating" occurrences.

**Item type.** The unit of openness analysis is an *item type*: a term pattern
`t` (a type-chart entry) describing a set of derivable items, with `$free(X)`
constraints marking the variables of `t` that some derivation leaves unbound.
This is the existing type-analysis representation (`to_type_program`,
`dyna/analyze/types.py:43`). A `$free` mark sits on a *variable occurrence in a
term*, at any depth — never on a top-level argument index (Section 3.2).

**Open occurrence.** An occurrence in an item is open iff some derivable type
of that item marks the variable there `$free` — some derivation leaves that
subterm unbound. An occurrence is **only-open** (a pure projection) if *every*
derivable type marks it `$free`: no derivation ever grounds it. An occurrence
is **groundable** iff it is not only-open.

**Bindable head variable.** A head variable `X` of rule `r` is bindable iff it
occurs in a body subgoal at a groundable occurrence, or as the output of a
generator builtin. A non-bindable head variable is the source of
non-range-restriction.

### 3.1 Input/output annotations

The terms "input" and "output" above are the program's *declared* annotations,
not informal labels. A `Program` carries two type sub-programs, `program.inputs`
and `program.outputs` (set from `input:`/`output:` syntax, `program.py:118-127`).
Membership is tested by head-unification: `is_output(x)` is true iff `x` unifies
with some declared output head (`program.py:517`), and likewise `is_input`.
Throughout this document, **output** means "matches `program.outputs` under
`is_output`" and **input** means "matches `program.inputs` under `is_input`";
the residual layer `R` (Step D) is precisely the set of surviving
non-range-restricted rules whose head `is_output`.

Inputs are not merely passive — they carry range-restriction information and so
participate in the analysis on both ends:

- **Inputs as a binding source.** An input declaration states which occurrences
  arrive ground. An occurrence fixed ground by an input declaration is therefore
  *groundable* (Section 3) and binds any head variable that consumes it, exactly
  like a range-generating subgoal. Step A and the "bindable head variable" test
  must count input-declared ground occurrences, not only occurrences produced by
  rule bodies.

- **Inputs as a source of openness.** Conversely, an input declared with a free
  variable (e.g. `input: f(X)` with `X` unconstrained) makes that occurrence of
  `f` open *by declaration* — a `$free`-marked input type with no rule deriving
  it. This is a **base case for the Step A fixpoint** that the body-only seeds
  miss: `add_free_constraints` (`types.py:34`) and `freebies`
  (`abbreviate.py:20`) are purely syntactic over a single rule
  (`term_vars(head) − term_vars(body)`) and never consult the declarations, so
  they capture failure-case 1 only. Step A must additionally seed the open set
  from input-declared free occurrences.

**Approximation caveat.** `is_input`/`is_output` unify against the declared head
only and do not check delayed constraints (`program.py:515`, marked `XXX:
approximate`). The crisp guarantees in Theorem (c) ("feeds only outputs",
non-recursive) and DoD #3/#4 inherit this imprecision. For milestone purposes
head-unification is adequate; if a declared output head carries a delayed guard
that the residue test must respect, route the check through the `Program` query
methods instead of `is_output` and note it at the call site.

### 3.2 Term structure (no flatness assumption)

Dyna terms are trees, not flat tuples. **Nothing in this spec may key on a
top-level argument index.** The unit of openness is a `$free`-marked variable
occurrence in a derivable item type, which handles the three cases a flat
`(functor, position)` analysis cannot:

- **Depth.** `f(g(X)) += 3.` puts the open variable inside a structured
  argument. Projection must abstract the open subterm while *retaining the
  ground skeleton* (`g(...)`), not drop a top-level slot and lower the arity.
- **Sharing.** `temp(pair(X0, X0)) += 1.` has one threaded variable spanning
  two paths inside a single argument. The analysis must see one open variable,
  not two independently open slots; splitting them breaks the `X0 = X0`
  equality (the nested form of E2's diagonal).
- **Recursive structure.** Openness in a list lives at unbounded-depth tail
  paths; there is no fixed finite set of "positions" at all. Any projection
  that disconnects recursive tail structure is unsound (see the list-beta
  audit in `abbreviation-design.md`).

Consequently the analysis and the transform must be **invariant** under (a)
renaming functors, (b) wrapping items in a dummy functor (`f(X)` → `w(f(X))`),
and (c) threading a dummy argument — the metamorphic perturbations of the
invariance critic. These are acceptance tests (M1, DoD #8), not aspirations.

Where the text writes `(q, j)` or `q\j` below, read `j` as naming an **open
occurrence** (a `$free`-marked variable in `q`'s type, at any depth), not an
argument index; the flat notation is kept only for its ε-elimination
resonance, and the examples use top-level occurrences only for readability.

## 4. Failure taxonomy

A head variable `X` is unbound in exactly three ways. They all reduce to the
first, propagated through consumption:

1. **Projection / pure free.** `X` in head, absent from body: `f(X) += 3`. The
   only primitive source. Makes the occurrence of `X` in `f`'s type only-open.
   This is the *pass-through* case: the rule's value is independent of `X`, so
   projection + recovery is exact.
2. **Test-only.** `X` occurs only in tests: `f(X) += g(Y) * (X > Y)`. A test
   cannot generate, so the rule is **not range-restricted** — but `X` is **not
   pass-through** either: the value of `f(X)` genuinely depends on `X` (with
   `g(3)=1`, `f(5)` is 1 but `f(2)` is 0). Projecting it would corrupt ground
   queries, so case 2 must **not** be collapsed into case 1 (this sharpens an
   earlier draft of this spec; see E5 and the implementation note in Section
   8). Such a rule is irreducibly non-range-restricted without an active
   domain; under Step E, splicing `adom(X)` makes it range-restricted.
   (Unbound builtin *inputs* are different again: the engine inverts binder
   builtins — `X is Y + 1` runs with either side bound — so a variable
   reachable through `=`/`is` from generating subgoals is bindable, not open.
   Only tests bind nothing.)
3. **Propagated.** `X` is "bound" only by consuming another item at a position
   that is itself open. Handled by the fixpoint in Section 5.

## 5. Algorithm

### Hygiene: rename + recovery (the governing discipline)

Every step below is a **conservative definitional rewrite**: it must never
redefine an existing functor's meaning in place. In-place elimination
(`Program.elim` / `LinearRuleElimination`) violates this — eliminating
`temp(X0,X0) += 1` from E2 overwrites `temp` with a relation that has lost its
reflexive diagonal, so the denotation silently drifts. The fix is the discipline
ε-elimination already uses, in two parts:

1. **Rename.** When an occurrence is projected away, the projected relation gets
   a *fresh* functor `q\j` (written `q_open_j` below). The original `q` keeps its
   meaning; `q\j` is what the transform produces.
2. **Recover.** Re-express the original relation from the fresh one with a
   **recovery rule** that reintroduces the dropped occurrence:
   ```text
   q(.., V, ..) += q\j                  # open / implicit domain (V free)
   q(.., V, ..) += adom(V) * q\j        # under Step E
   ```

The load-bearing identity: **the recovery rule *is* the residue.** Whatever an
in-place elimination would silently drop reappears as a recovery rule. The CFG
analog is exact — `S0 -> S | epsilon` is *rename* (`S → S0`, the ε-free relation)
plus *recovery* (`S0 -> epsilon`). The residual layer `R` (Step D) is then
nothing more than **the set of recovery rules that remain non-range-restricted**
(no `adom`). Because the original relations are always recoverable, every step is
value-preserving by construction — there is no separate per-step soundness
argument to discharge.

This is why the implementation is **not** based on `rule_elimination`'s in-place
rewrite (Section 8): projection + recovery, not elimination.

### Step A — openness fixpoint (the "nullable set")

Compute the set of open occurrences, represented as derivable item types
carrying `$free` marks. Per Section 3.2 the carrier is **term patterns**, not
`(functor, position)` pairs; concretely this is the existing type analysis run
on a `$free`-instrumented program, not a new fixpoint engine:

```text
base:    booleanize the program and add $free(X) for each head variable X
         not bindable in the body (X absent, or test/builtin-input-only) —
         add_free_constraints / to_type_program (types.py:34,43);
         failure-cases 1-2.

seed:    add a $free-marked input type for each input declared with a free
         variable; treat input-declared ground occurrences as binding
         (Section 3.1). The body-only base misses both.

step:    run the type solver. Propagation through consumption (failure-case
         3) is the solver's job: a rule that fills a head variable only from
         $free-marked occurrences (or tests) derives a head type with that
         variable $free.
```

This is the nullable-nonterminal fixpoint. It terminates because the type
analysis's widening keeps the type chart finite — the finiteness lives in the
abstraction, not in a finite set of argument slots. Because the carrier is
term patterns, depth, sharing, and list tails are representable (Section 3.2).

**Precision canary.** Representable is not retained: the analysis must *keep*
intra-term sharing through widening — `temp(pair(X0, X0))` must come out as
one threaded `$free` variable, not be widened to `temp(pair(X, Y))` with two.
Losing the sharing is the nested form of the E2 failure (drops the diagonal).
This is the first thing to prototype and lock down with an M1 test; if the
current widening is too coarse here, fixing it is in scope for M1.

### Step B — rule expansion (the production rewrite)

For each rule `r`, find every body subgoal whose item has an open occurrence
`(q, j)` (an open derivable type, Section 3.2). Like ε-elimination expanding
over subsets of nullable occurrences, emit one copy of `r` per assignment of
{closed, open} to each such occurrence:

```text
closed reading of q(.., V, ..):
    keep the subgoal; require V ground here (the closed derivable types).
    If (q, j) is only-open (never groundable), this reading is DEAD -> drop it.
    If an active domain adom is available, the closed reading is
        q(.., V, ..) * adom(V).

open reading of q(.., V, ..):
    q's value is independent of V at occurrence j (that is what "open" means).
    Replace q(.., V, ..) by the projected item  q_open_j : abstract the open
    subterm at j, RETAINING the surrounding ground skeleton (Section 3.2) --
    only when the open occurrence is a whole top-level argument does this
    lower the arity.
```

`q\j` (written `q_open_j`) is `q` with the open occurrence `j` projected away,
defined by projecting every rule that derives `q` — **not** by inlining `q`'s
definition. Projecting the definition keeps the rewrite a conservative,
recursion-safe rename (see "Hygiene" above); inlining unfolds the recursion and,
as E2 shows, silently drops values. Alongside the fresh `q\j`, emit the recovery
rule `q(.., V, ..) += q\j` so the original `q` stays derivable for any consumer
that still reads it ground or outputs it.

The mechanism has a precedent in `Abbreviate` (`dyna/analyze/abbreviate.py`):
its type-chart join over body occurrences (`join_f`, line 71) is this
closed/open expansion, and its `__abbrev` (line 114) builds the projected head
by dropping the `$free`-marked variables of the type. But the precedent **fell
short** — see Section 8: its decision of *what* to drop is justified only by
the `$free` marks plus rewrite artifacts, with no explicit projection proof.
Here every drop must be gated by Step A's openness verdict *and* the
pass-through obligation (Section 9); nothing may be dropped merely because the
current abbreviation machinery happens to drop it.

### Step C — multiplicity correction (the residue accounting)

After Step B, a variable may have vanished from a rule. If a vanished variable
was **summed** (local to the rule, not in the head), the rule must be multiplied
by its witness count:

```text
witness count = |universe|        = inf                 (open / implicit domain)
              = |adom|            (finite, if adom supplied)
```

Use `Semiring.multiple(inf)` (the same construct the non-ground forward-chaining
solver already uses). In idempotent semirings (e.g. max-plus, Boolean) `inf`
copies of one value collapse to one value, so the factor is `one`; the
correction code must defer to the semiring rather than hard-coding `inf`.

A vanished variable that appears in **both** head and body (dropped consistently)
needs **no** correction — it is renamed away on both sides.

This step has a working precedent: `Abbreviate.__dropped_var_correction`
(`abbreviate.py:107`) attaches `Semiring.multiple(inf)` exactly when the set of
free local variables changed, comparing `freebies − head_vars` before and after
— which is precisely the E2 threaded-variable guard (a variable dropped from
head and body together changes neither side, so no factor). The correction
*shape* is right and should be reused even where the surrounding drop decisions
are not (Section 8).

### Step D — residue isolation (collecting the recovery rules)

After Steps B-C the only non-range-restricted rules left are **recovery rules**
(see "Hygiene" above) whose reintroduced free occurrence is never bound by any
consumer above them — i.e. it reaches an **output** (per Section 3.1). These are
already in recovery form; Step D merely *collects* them into the labeled residual
layer `R`:

```text
q(.., V, ..) += q\j               # a surviving recovery rule, V free
```

No new wrapper is fabricated — `R` is exactly { recovery rules that remain
non-range-restricted }. Each is non-recursive (it consumes only the
range-restricted `q\j`), feeds only outputs, and carries the one irreducible bit
of non-range-restriction. `R` is the analog of `S0 -> S | epsilon`.

### Step E — optional residue elimination

If `adom` is supplied (or the universe is declared finite), splice `adom(X)` into
every closed reading and into each residual rule. `R` then disappears: the
program is fully range-restricted and every `inf` witness count becomes `|adom|`.
This is the database "safe-ification"; it is opt-in because it commits to
active-domain semantics and pays to materialize the domain.

## 6. Theorem (what the implementation must achieve)

**Range-Restriction Normalization.** For every program `P` there is a program
`P†` with:

- **(a) Engine equivalence.** For every ground query `q`, `value_{P†}(q) =
  value_P(q)`.
- **(b) Confinement.** Every rule of `P†` is range-restricted — under the
  refined generating-occurrence check — except those in a residual layer `R`.
- **(c) Superficiality.** `R` contains rules of exactly two kinds: (i)
  **recovery rules** `output(.., V, ..) += q\j` — pass-through openness
  reaching an output — each non-recursive and output-feeding; and (ii)
  **delayed-test rules** (E5 / Section 4 case 2) — rules whose head variable
  is constrained only by tests, which are not pass-through and survive
  verbatim. `R` is empty whenever `P` has no free variable that reaches an
  output and no test-only head variable.
- **(d) Escape hatch.** Given an active-domain predicate `adom` (or a finite
  universe), `R` can be removed entirely, yielding a fully range-restricted `P‡`,
  at the cost of replacing each `inf` witness count by `|adom|`.

The construction terminates (Step A terminates by the type analysis's widening,
which keeps the type chart finite; Step B is a one-shot expansion bounded by the
size of that chart) and preserves semiring values by construction: each step is a
conservative rename + recovery (Section 5), so the original relations stay
recoverable, and the only value-bearing addition is the `Semiring.multiple`
witness factor, sound in any semiring.

**Irreducibility (the caveat).** When the universe is infinite and the program is
domain-independent, `R` is non-empty and cannot be removed without `adom`, for
the same reason `epsilon in L(G)` cannot be expressed with zero ε-rules. This is
the intended, minimal residue — the analog of the single top-level ε-rule.

## 7. Worked examples (use these as tests)

**E1 — canonical projection + summation (residue = scalar inf).**

```dyna
f(X) += 3.          % f's argument only-open
goal += f(X).       % X local, occurs only at the open occurrence of f
```
`f`'s argument is only-open; in `goal += f(X)`, `X` is bindable nowhere, so the
closed reading is dead and only the open reading survives; `X` was summed, so:
```dyna
f_open += 3.
goal   += inf * f_open.
```
`R` is empty (`goal` is the output and is ground). This must reproduce the
existing `test_infinite_multiplicity` value.

**E2 — recursion through an open occurrence (no infinite unfolding).**

```dyna
temp(X0, X0) += 1.
temp(X, X0)  += rewrite(X, Y) * temp(Y, X0).
```
The open variable `X0` is *threaded* (preserved on both head and body), not
summed, so Step C adds **no** multiplicity factor. The reflexive base rule is the
sole non-range-restriction; it is already in recovery form and stays as residue:
```dyna
temp(X, X0)  += rewrite(X, Y) * temp(Y, X0).   % engine layer
temp(X0, X0) += 1.                              % residual R (or += adom(X0), Step E)
```
The expansion is one-shot; recursion does not cause a loop.

Contrast in-place elimination, which is **wrong** here: `p.elim(0)` returns
```dyna
temp(X, X0) += rewrite(X, X0).                 % Y bound to X0; the *1 is dropped
temp(X, X0) += rewrite(X, Y) * temp(Y, X0).
```
overwriting `temp` and dropping the reflexive diagonal — `temp(a,a)` loses its
`+1`. This is exactly the hygiene violation Section 5 forbids. (The commented
example at `rule_elimination.py:75-78` also mistypes this body as `rewrite(X,Y)`;
the unification binds `Y` to `X0`.)

**E3 — open variable reaches an output (residue = single open rule).**

```dyna
f(X) += 3.
out(X) += f(X).      % out is an output; X reaches it unbound
```
After Step B, `out(X) += f_open` is still non-range-restricted and feeds an
output. Step D isolates it:
```dyna
f_open += 3.
out(X) += f_open.    % the residual layer R, exactly one rule
```
This is the `S0 -> epsilon` analog: one superficial open output rule, engine
fully range-restricted beneath it.

**E4 — active-domain escape (residue removed).**

Same as E1/E3 but with `adom` supplied. E3 becomes:
```dyna
f_open += 3.
out(X) += f_open * adom(X).    % range-restricted; R empty
```
and E1's `inf` becomes `|adom|`.

**E5 — test-only variable (irreducible without adom).**

```dyna
f(X) += g(Y) * (X > Y).
goal += f(X).
```
`X` occurs only in a test, so it is non-bindable — but it is **not**
pass-through (Section 4, case 2): with `g(3)=1`, `f(5)=1` while `f(2)=0`, so
projecting `X` away (an `f_open` with recovery `f(X) += f_open`) would assign
every `f(_)` the same value, corrupting ground queries. The normalization
therefore leaves this rule untouched: it is residue of the *delayed-test* kind
(not recovery form), irreducible without an active domain — the engine runs it
on the non-ground solver, deriving `f(X) += (X > 3)` with the test delayed.
Under Step E it becomes range-restricted like everything else:
```dyna
f(X) += g(Y) * (X > Y) * adom(X).    % range-restricted; R empty
```
Two regression points: (a) the purely syntactic `Program.is_range_restricted`
calls the `f` rule restricted (`X` does occur in the body) — the refined
generating-occurrence check (Section 8) must report it; (b) the transform's
stop condition must not loop trying to project it.

**E6 — nested sharing (the no-flatness canary).**

```dyna
temp(pair(X0, X0)) += 1.
temp(pair(X, X0))  += rewrite(X, Y) * temp(pair(Y, X0)).
```
E2 with both positions folded inside one argument: the open variable sits at
depth, and the diagonal sharing lives inside a single top-level slot. The
normalized result must be exactly E2's — the diagonal base rule survives as the
recovery rule / residue, with **no** multiplicity factor — and any analysis
keyed to top-level argument indices fails here (it sees one opaque open slot
and loses the `X0 = X0` equality). Together with the metamorphic variants —
functor renaming, wrapping (`f(X)` → `w(f(X))` in E1/E3), dummy-argument
threading — this locks down the invariance requirement of Section 3.2. It is
also the precision canary for Step A: the type analysis must not widen the
shared `X0` into two independent variables.

## 8. Relation to existing code

- **Do not** base the transform on `dyna/transform/rule_elimination.py`
  (`LinearRuleElimination` / `Program.elim`). It is an *in-place* rewrite that
  redefines the eliminated relation, violating the rename+recovery hygiene
  (Section 5), and it is lossy on the target class: `p.elim(0)` on E2 drops the
  reflexive diagonal, and its disabled multiplicity branch (lines 64-94) would
  not have caught it (the var-preservation guard correctly says "no factor"). Use
  it, if at all, only as a throwaway check on the trivial non-recursive case (E1);
  it is not in the critical path.
- The structural precedent for Step B is `Abbreviate`
  (`dyna/analyze/abbreviate.py`). It already exercises the right *discipline*:
  fresh functors (`_gen_functor`, line 56), explicit recovery rules (line 49),
  the closed/open expansion via the type-chart join (`join_f`, line 71),
  projection by dropping `$free` variables of the type (`__abbrev`, line 114),
  and the multiplicity correction with the threaded-variable guard
  (`__dropped_var_correction`, line 107). No linearization precondition is
  needed — it projects definitions, it does not unfold them.

  **But Abbreviate fell short of solving range restriction — that shortfall is
  the reason this spec exists.** Per the audit in `abbreviation-design.md`
  (Options A–D): its drop decisions carry no explicit projection proof; what is
  retained vs dropped depends on rewrite artifacts of the type analysis (the
  slashed-CKY compaction), so the projection behavior is accidental rather than
  specified; and soundness for generalized structure (list tails, shared
  subterms) is unexplained — retention happens to occur on the list-beta audit
  but nothing guarantees it. So: reuse the discipline and the correction shape;
  do **not** inherit the drop heuristics. Every drop in this transform must be
  justified by Step A's openness verdict plus the pass-through obligation
  (Section 9) — the Option C direction of the abbreviation doc — and the
  invariance tests (Section 3.2, E6) are the regression net for exactly the
  cases where Abbreviate's behavior was accidental.
- `Program.is_range_restricted` (`dyna/program.py:857`) is **purely syntactic**
  (`head_vars ⊆ body_vars`) and is *not* the per-rule check Section 3 defines: on
  E5 it reports restricted while `X` is test-only and open. Used as the M3 stop
  condition it terminates early and silently fails DoD #3. The transform needs
  the refined per-rule predicate — every head variable occurs in a
  *range-generating* subgoal (tests and unbound builtin inputs do not generate)
  — with the syntactic check as a necessary-but-insufficient fast path. The
  refined check is small to write but must exist before M3, not be discovered
  during it.
- `Semiring.multiple` / `Program.multiple` (`dyna/program.py:1198`) is the
  existing witness-multiplicity construct; do not invent a new one.
- `add_free_constraints` (`dyna/analyze/types.py:34`) and `freebies`
  (`dyna/analyze/abbreviate.py:20`) already mark non-range-restricted variables;
  reuse them to seed Step A rather than re-deriving openness from scratch — but
  they are body-only and miss openness declared via `program.inputs`, so add the
  input-declaration base case from Section 3.1.

### 8.1 Implementation (as built)

Everything range-restriction lives in **one module, `dyna/analyze/range_restriction.py`**
(next to `abbreviate.py`, mirroring it): the refined check, the spec transform,
and the sound normalizer.

- The refined check — Step A: `open_types(program)` (the `$free`-marked
  derivable types, via the standard type analysis), plus
  `bindable_vars(program, rule)` (the per-rule dataflow — variables of
  non-builtin subgoals, closed bidirectionally through the binder builtins
  `=`/`is`; tests bind nothing) and `is_rule_range_restricted` /
  `is_range_restricted`.
- The spec transform —
  `RangeRestrictionNormalization(program, adom=None, input_type=None)`, also
  reachable as `Program.normalize_range_restriction(...)`.  **Single pass, no
  outer loop:** `type_analysis` already computes the *transitive* openness
  fixpoint (propagation through consumption is the type solver's job, closed
  over recursion), so one `Abbreviate` pass — expanding over the complete type
  chart — projects every open position at once; a second pass would only
  re-project the recovery rules it just emitted.  An adversarial sweep (deep
  nesting, mutual recursion, long open chains, lists) found no program that
  needs more than one pass.  Steps B-C run on `Abbreviate`; dead recovery
  rules are removed by `prune_very_fast` (reachability from the outputs),
  load-bearing for *confinement* rather than soundness: a dead recovery rule
  is non-range-restricted and would pollute the residual layer's output-feeding
  form (DoD #3).  Step D exposes `residual_layer` and `engine_layer` (both
  `Program`s).  An explicit `input_type` (e.g. `h(X) += $free(X).`) supplies
  open-by-declaration inputs (Section 3.1).  Step E (`adom=<functor>`) splices
  `adom(V)` for every remaining unbindable variable and declares `adom(_)` an
  input; inside `Abbreviate`, the dropped-var correction emits `adom(V)` for
  each lost variable instead of `Semiring.multiple(inf)`, so witness counts
  become `|adom|` with the *original* variable re-bound (E4's
  `out(X) += f_open * adom(X)` falls out with the right `X`).
- **Post-condition checks** (`_check_postconditions`).  With `adom`, Step E
  must have emptied the residue — a hard invariant, so it is **asserted**.
  Without `adom`, every `residual_layer` rule should be a recovery rule or a
  delayed-test rule (Theorem (c)); a rule that is neither is **warned**, not
  asserted, because of a genuine third case found by the adversarial sweep:
  a **builtin-orphaned** rule.  When abbreviation projects a pass-through
  variable out of an open item that *also* feeds a builtin
  (`g(Z) += f(X) * (Z is X+1)`), the variable is orphaned in the builtin.
  This only arises when the open item is the builtin variable's sole generator
  — i.e. on programs whose source is *already* non-evaluable (the source
  itself raises `InstFault`) — so values are preserved (both fail identically)
  and the rule is confined to the residual layer; crashing would be wrong, so
  it warns.  The original open-input gap (an input that arrives open but is
  declared ground) is *not* warnable — the transform has no signal for it — so
  it is handled by Section 3.1 / `input_type`, not a runtime check.
- One notable non-change: `add_free_constraints` needed no refinement — the
  `$free` mark is reserved for pass-through variables, and `head_vars −
  body_vars` is exactly that set (Section 4 case 2 must *not* be marked).
  The E5 fix lives entirely in the refined check + residue classification.
- Tests: `test/test_range_restriction.py` (M1-M5, DoD #2/#6, the metamorphic
  invariance suite, and the E6 sharing canary — which the existing widening
  passes without modification).

### 8.2 Module map (as built — read this first)

There are two normalization implementations, by design. **`abbreviate`
(`dyna/analyze/abbreviate.py`) is untouched pre-existing infrastructure** — a
general type-specialization transform used by CKY/geom/benchmarks — and is part
of this feature only because the spec transform calls it.

Everything range-restriction is in **one module**, `dyna/analyze/range_restriction.py`,
next to `abbreviate.py` (which is likewise a single analyze-module transform).
It holds three things:

| in `dyna/analyze/range_restriction.py` | role | status |
|---|---|---|
| the refined check (`bindable_vars`, `is_rule_range_restricted`, `open_types`) | shared analysis used by both transforms below | — |
| `RangeRestrictionNormalization` — the spec transform, built on `abbreviate` | **canonical**: `Program.normalize_range_restriction` routes here; meets the DoD | inherits abbreviate's substrate (the startpath3 caveat, §9.1) |
| the **sound** normalizer (`phantom_paths`, `PhantomProjection`, `ValueSplit`, `RangeRestrictionNormalizer`) | provably-sound + invariant projection | not the entry point; the trustworthy alternative (§9.1) |

`abbreviate` (`dyna/analyze/abbreviate.py`) is untouched pre-existing
infrastructure, used here only because the spec transform calls it.

**Frontier (not done):** the sound module is conservative — it refuses (soundly,
unprojected) the diagonal value-split (`q(X,X)`/`q(X,Y)`), recursive overlap,
and nested value-splits. Its soundness is a rigorous argument, not a mechanized
proof. The two transforms are not unified; the sound one is the basis for any
future migration off the abbreviate substrate.

## 9. Relation to abbreviation

The projected item `q_open_j` in Step B is the **abbreviated item with the open
occurrence dropped**. So range-restriction normalization and abbreviation are the
same operation from two sides: abbreviating an open occurrence makes its consumers
range-restricted, and the `inf * one` correction is the residue when the dropped
occurrence was summed over an infinite domain. The soundness obligation for the
open reading is exactly the abbreviation doc's `PassThroughWitness` proof: the
open value must be independent of the dropped occurrence. There is no *separate*
proof debt — but shared debt is not zero debt: the pass-through audit is the
abbreviation doc's *chosen but unbuilt* direction (Option C), not an existing
guarantee, which is precisely how Abbreviate fell short (Section 8). Building
that gate is part of M2, and once built it discharges both transforms at once.

This retires the worry in `abbreviation-design.md` Option D (lines 2235-2244)
that range-restriction normalization needs a *separate* semiring-preservation
proof: it does not — it shares abbreviation's.

### 9.1 The startpath3 caveat (why the phantom line exists)

Sharing abbreviation's projection means sharing its soundness boundary, and
that boundary is **not sound everywhere**. `test_abbreviate.py::todo_startpath3`
is a checked-in counterexample: abbreviating the reflexive-transitive closure
against refined usefulness types **drops the diagonal base `path(I,I)`** and
computes all-zero paths. The mechanism is the `ALLOW_FREE_MERGE` projectability
decision merging the diagonal (`I=I`) into the general (independent-positions)
type, losing the equality. The spec transform avoids this only because
`Program.normalize_range_restriction` uses the *plain* type analysis, which
preserves the diagonal on the cases tested — it dodges the bug, it does not
defeat it.

The sound normalizer in `dyna/analyze/range_restriction.py` (§8.2) is the response: a
projection gate that is sound *by a verifiable condition* (single-occurrence
excludes diagonals structurally) rather than by the merge heuristic, validated
sound on startpath3 and ~2000 randomized differential programs. It is
conservative and not yet the canonical entry point; it is kept as the
trustworthy alternative and the basis for any future migration.

## 10. Implementation plan (ordered milestones)

Each milestone is independently testable. Do not start the next until the
current one's tests pass.

```text
M1  Openness fixpoint (Step A) on the type substrate.
    - Add `open_occurrences(program)` exposing the $free-marked derivable
      types: type analysis over the booleanized, $free-instrumented program
      (add_free_constraints / to_type_program), additionally seeded from
      input-declared free occurrences, with input-declared ground occurrences
      treated as binding (Section 3.1). NO (functor, position) carrier
      anywhere (Section 3.2).
    - Pure analysis, no codegen. Unit-test on E1, E2, E3, E5, an
      input-declared open occurrence, an input-declared ground occurrence,
      AND the no-flatness suite: E6 (sharing survives widening — the
      precision canary; fixing the widening is in scope if it is too coarse),
      a depth case (f(g(X))), a list-tail case, and the metamorphic variants
      (rename / wrap / thread) giving invariant verdicts.

M2  Single-occurrence projection (Steps B-C core).
    - Project one open occurrence (q,j) to a fresh q\j: fresh functor +
      recovery rule q(..,V,..) += q\j + Semiring.multiple(inf) factor when a
      summed variable vanished, with the head/body-consistency guard from E2
      (no factor when V is threaded). Reuse Abbreviate's discipline and its
      __dropped_var_correction shape, but gate the drop on M1's openness
      verdict + pass-through (Section 9) — never on the current abbreviation
      heuristics (Section 8).
    - Test: E1 reproduces test_infinite_multiplicity; E2 adds no factor and
      keeps the diagonal as a recovery rule; E6 behaves identically to E2.

M3  Rule expansion (Step B) as a standalone transform
    RangeRestrictionNormalization(program) -> TransformedProgram.
    - closed/open reading split over open occurrences; drop dead closed
      readings; project open occurrences to q\j via the M2 machinery (never
      inline).
    - Add the refined per-rule range-restriction check (generating
      occurrences, Section 8) and iterate to fixpoint using IT — not the
      syntactic Program.is_range_restricted — as the stop condition
      (regression: E5 must not terminate the loop early).

M4  Residue isolation (Step D).
    - Move surviving non-range-restricted output-feeding rules into a labeled
      residual layer; expose it (e.g. program.residual_layer) for tests.
    - Test: E3 yields exactly one residual rule; E1 yields an empty residue.

M5  Active-domain escape (Step E), opt-in via an adom argument.
    - Test: E4 removes the residue and replaces inf by |adom|.
```

## 11. Definition of Done (acceptance criteria)

```text
1. RangeRestrictionNormalization(P) exists as a TransformedProgram and
   terminates on every test program.

2. For every example E1-E5 and every existing test program, the normalized
   program returns identical semiring values on all ground queries
   (assert_equal against the source program's solve()).

3. After normalization, the engine layer passes the refined per-rule
   range-restriction check (generating occurrences, Section 8) — the syntactic
   program.is_range_restricted() is implied but is not the criterion (E5); the
   only non-range-restricted rules are in the exposed residual layer, each
   either a recovery rule (output(...) += open_item, non-recursive,
   output-feeding) or a delayed-test rule (Theorem (c), E5).

4. The residual layer is empty exactly when no free variable reaches an output
   (verified on E1 vs E3).

5. With adom supplied, the residual layer is empty and is_range_restricted() is
   True for the whole program; inf factors are replaced by |adom| (E4).

6. The multiplicity factor is produced via Semiring.multiple, not a literal inf,
   and collapses correctly in an idempotent semiring (add a Boolean/max-plus
   regression).

7. No reliance on variable names or truncation markers as evidence; openness is
   decided by the Step A fixpoint over $free-marked types, with no
   (functor, position) carrier anywhere in the analysis (Section 3.2).

8. Invariance: analysis verdicts and normalized values are unchanged under
   functor renaming, dummy-functor wrapping, and dummy-argument threading;
   E6 (nested shared diagonal) normalizes identically to E2.
```

## 12. Non-goals

- Do not change general rewrite/intersection semantics.
- Do not implement functional-dependency or structural-quotient dropping here;
  those are abbreviation proof cases, deferred in `abbreviation-design.md`.
- Do not require an active domain by default; Step E is opt-in.
- Do not attempt to remove the irreducible residue without `adom` — it is the
  intended caveat, not a bug.

## 13. References

- McAllester, "On the Complexity Analysis of Static Analyses", JACM 2002 —
  range restriction and prefix firings.
- Hopcroft & Ullman, ε-production elimination — the structural template.
- `abbreviation-design.md` (this repo) — the projection/pass-through proof that
  Step B's open reading reuses.
- `dyna/transform/rule_elimination.py`, `dyna/program.py`,
  `dyna/analyze/abbreviate.py`, `dyna/analyze/types.py` — existing machinery.
<!-- chat Tim Vieira 2026-06-03 09:56
does this spec have enough detail about input/output annotations?
-->
<!-- chat claude 2026-06-03 09:57
No — "output" is the load-bearing term in the spec (Step D, Theorem (c), DoD #3/#4, the whole "residue at the outputs" framing) but it's never tied to the actual annotation machinery, and "input" never appears in the algorithm at all. Concretely:

1. **"Output" is left primitive.** The codebase already has declared outputs: `program.outputs` is a `Program` of type heads, and `is_output(x)` tests head-unification against it (`program.py:517`). Step D writes `output(X,..) += open_item` as if `output` were a fresh wrapper functor it introduces — but that's a different thing from "x matches a declared output." The spec needs to say which: is the residual layer keyed off `is_output`, or off "no rule consumes this item"? DoD #4 ("residue empty exactly when no free variable reaches an output") is untestable until "output" = `is_output` (or whatever) is pinned down.

2. **Inputs are ignored, but they're range-restriction information.** A declaration like `input: word(I,W)` says those positions arrive ground — that's exactly a range-generating source, and Section 3's "groundable position" / "bindable head variable" should count an input-declared position as binding. Conversely, an input declared with a free position is *open by declaration*, not by derivation — a base case Step A's fixpoint misses. Right now Step A seeds only from `add_free_constraints`/`freebies`, and I checked both (`types.py:34`, `abbreviate.py:20`): they're purely syntactic (`head_vars − body_vars`), with no view of `program.inputs`/`outputs`. So §8's "reuse them to seed Step A" captures only failure-case 1, not openness arising from input annotations.

3. **The annotation tests are approximate.** `is_input`/`is_output` only unify against the declared head and explicitly skip delayed constraints (`# XXX: approximate` at `program.py:515`). Theorem (c)'s crisp guarantees ("feeds only outputs", non-recursive) and DoD #3 inherit that imprecision; the spec should state whether head-unification is adequate or whether the residue test needs `Program`'s query methods.

So I'd add a short subsection — say in §3 or a new §3.1 — that (a) defines "output"/"input" as the declared `program.outputs`/`program.inputs` via `is_output`/`is_input`, (b) makes input declarations a binding source in "groundable position" and a base case in Step A, and (c) notes the head-unify approximation. Want me to draft it?
-->
<!-- chat Tim Vieira 2026-06-03 09:57
yes
-->
<!-- chat claude 2026-06-03 09:58
Done. Added a new **§3.1 Input/output annotations** subsection and threaded two consistency references to it.

The new §3.1 covers:
- **Definition** — "output"/"input" now mean declared `program.outputs`/`program.inputs` tested via `is_output`/`is_input` (head-unification, `program.py:517`), and `R` is pinned to "surviving non-range-restricted rules whose head `is_output`."
- **Inputs as a binding source** — input-declared ground positions count as groundable/binding in Step A and the bindable-head-variable test.
- **Inputs as a source of openness** — a free input position is an openness base case the syntactic seeds (`add_free_constraints`/`freebies`, which I confirmed are body-only) miss.
- **Approximation caveat** — `is_output`/`is_input` skip delayed constraints; head-unify is fine for milestones, otherwise route through `Program` query methods.

Consistency edits: §8's seeding bullet now notes the body-only gap and points to §3.1, and M1 gains the input-declaration seeding plus two new unit-test cases (an input-declared open position and an input-declared ground position).
-->
<!-- chat Tim Vieira 2026-06-03 09:59
What is the expected output of E2?
-->
<!-- chat claude 2026-06-03 10:01
The spec gives **no output block for E2** — it's the only worked example that shows just the input program and a property claim ("Step C adds no correction; one-shot expansion"), with no normalized program written down. So the literal answer is: it's unspecified.

What the spec *intends* is recoverable from the code it points at — the commented block in `rule_elimination.py:75-78` is E2 verbatim:

```dyna
% temp(X0,X0) += 1.
% temp(X,X0) += rewrite(X,Y) * temp(Y,X0).
% ==>
% temp(X,X0) += rewrite(X,Y) * 1.
```

i.e. inline the base rule into the recursive consumer's `temp(Y,X0)` call. The unification `temp(Y,X0) = temp(Z,Z)` forces `Y = X0`, and the guard at line 80 (`term_vars(s) ⊆ term_vars(t)`) holds — the eliminated rule's variable survives in the result — so **no `multiple(inf)` factor is attached**. That's the entire point of E2: contrast with E1, where the same guard fails and you get the `inf`.

But that's one inlining step, not a full normalized program, and E2 is exactly where the gaps bite — especially after the §3.1 edits:

1. **The base rule survives and has nowhere to go.** `temp(X0,X0) += 1` is itself non-range-restricted (`X0` free) and isn't eliminated — `temp(X0,X0)` is a real answer (reflexivity), so you can't drop the fact. Under Theorem (b)/(c) it must end up either range-restricted or in residual layer `R` as `output(...) += open_item`. But E2 declares no `output:`, so per §3.1 the residue test has nothing to match and `R` has nowhere to land. E2 needs an output declaration (or `adom`, Step E) for the theorem to even apply.

2. **The diagonal makes both positions jointly open.** `temp(X0,X0)` leaves positions 1 and 2 *both* free but *equal*. A naive per-position open/closed split (Step B) would treat `(temp,1)` and `(temp,2)` as independently open and risk breaking the `X0=X0` equality. The spec should state the diagonal is one threaded variable, not two independent open positions.

So E2 demonstrates a negative (no inf correction, no unfolding loop) but never shows the resulting program, and the "real" full output depends on choices the example leaves blank. Want me to add a `==>` block to E2 — say, declaring `temp` an output so the diagonal lands in `R` as `temp(X0,X0) += 1` with the engine layer beneath it — plus a one-line note that the diagonal is threaded, not split per-position?
-->
<!-- chat Tim Vieira 2026-06-03 10:02
I don't think this looks right: % temp(X0,X0) += 1.
% temp(X,X0) += rewrite(X,Y) * temp(Y,X0).
% ==>
% temp(X,X0) += rewrite(X,Y) * 1.
-->
<!-- chat claude 2026-06-03 10:02
You're right — that `==>` line is wrong. Inlining the base rule `temp(X0,X0)` into the consumer's `temp(Y,X0)` subgoal unifies the base head's two (equal) positions against `Y` and `X0`, which forces **Y = X0**. So `Y` has to be substituted by `X0` in the surviving body; it can't stay as a free `Y`. The correct result is:

```dyna
temp(X0,X0) += 1.
temp(X,X0)  += rewrite(X,Y) * temp(Y,X0).
% ==>
temp(X,X0)  += rewrite(X,X0).      % Y bound to X0; the *1 is identity, drop it
```

Writing `rewrite(X,Y)` makes `Y` and `X0` look like distinct variables when the inlining has actually collapsed them — that's the error. (This is the same loose binding I flagged loosely last turn; you're correct to call it out as just wrong, not just sloppy.)

Two things worth noting beyond the typo:

1. The `* 1` is multiplication by the semiring `one`, so it's identity and should simplify away — leaving plain `temp(X,X0) += rewrite(X,X0)`. The comment keeps the `* 1` only to visually mark "this is where the base rule's value got spliced in."

2. More substantively: this `==>` shows the *contribution* of inlining the base case, but eliminating the fact `temp(X0,X0) += 1` outright is **not** value-preserving — it drops the reflexive diagonal (`temp(A,A)` loses its `+1`). That's exactly why the base rule is irreducible residue and has to survive (or be wrapped as an output / guarded by `adom`), which loops back to the E2 gap from before.

This block lives in `rule_elimination.py:75-78` (commented-out code). I won't touch it unless you want me to — and if E2 in the spec ends up showing an `==>`, I'd write it as `temp(X,X0) += rewrite(X,X0)` to avoid repeating the same mistake. Want me to add the corrected E2 output to the doc?
-->
<!-- chat Tim Vieira 2026-06-03 10:03
In [4]: p = dyna.Program("""
   ...: temp(X0, X0) += 1.
   ...: temp(X, X0)  += rewrite(X, Y) * temp(Y, X0).
   ...: """)

In [5]: p.elim(0)
Out[5]: 
{
  0: temp(X,X0) += rewrite(X,X0).
  1: temp(X,X0) += rewrite(X,Y) * temp(Y,X0).
-->
<!-- chat claude 2026-06-03 10:03
That output confirms the correction: `elim(0)` gives `temp(X,X0) += rewrite(X,X0)` (Y bound to X0, `*1` dropped) — not the `rewrite(X,Y)` the source comment claimed. So the comment at `rule_elimination.py:75-78` is just wrong on that line.

But notice what `elim(0)` actually produced as a whole:

```dyna
temp(X,X0) += rewrite(X,X0).              % was: temp(X0,X0) += 1
temp(X,X0) += rewrite(X,Y) * temp(Y,X0).
```

The base fact `temp(X0,X0) += 1` is **gone**, and with it the reflexive diagonal. Check `temp(a,a)`:

- original: `temp(a,a) = 1 + Σ_Y rewrite(a,Y)·temp(Y,a)`
- after `elim(0)`: `temp(a,a) = rewrite(a,a) + Σ_Y rewrite(a,Y)·temp(Y,a)`

The `1` became `rewrite(a,a)`. So **`elim(0)` is not value-preserving on this program** — it silently drops the open diagonal answers. That's the lossy step exactly, the reason the multiplicity branch was commented out and the reason this base rule is irreducible residue.

The consequence for the spec: `elim(0)`'s output is **not** the expected normalized E2. It's the raw unfold step that Steps C/D have to repair — and here the repair isn't a `multiple(inf)` factor (the var-preservation guard correctly says no factor needed), it's *not eliminating the rule at all*: `temp(X0,X0) += 1` must be retained as the residual open rule. So the correct normalized E2 keeps the diagonal:

```dyna
temp(X,X0)  += rewrite(X,Y) * temp(Y,X0).   % engine layer
temp(X0,X0) += 1.                            % residual R (or += adom(X0) under Step E)
```

This is a good catch to bake into the doc, because the "obvious" `==>` (just run elim) is both mistyped *and* semantically wrong as a normalization. Want me to add E2's `==>` block to the spec as the value-preserving version above, with a one-line note that plain `elim(0)` is lossy here (drops the reflexive diagonal) so it's not the normalized result?
-->
<!-- chat Tim Vieira 2026-06-03 10:04
That said, I'm not sure that rule_elimination is a good strategy to base any of this on.
-->
<!-- chat claude 2026-06-03 10:05
Agreed — and I think the spec half-knows it. `rule_elimination` is a weak foundation for three concrete reasons, all of which we just hit:

1. **It's lossy on exactly the target class.** The programs that need normalizing are the non-range-restricted ones, and that's precisely where `elim` misbehaves: `elim(0)` dropped the diagonal, and the correction meant to fix it (`rule_elimination.py:64-94`) is commented out and, as we saw, wouldn't even fire here (the var-preservation guard says "no factor"), so the loss is silent. Basing a *semantics-preserving* transform on a primitive whose safety code is disabled and wrong-for-this-case is backwards.

2. **It needs linearization first** (`count > 1` → `assert False, 'call linearize before elim!'`). So Step B can't just call `elim`; it has to linearize, which constrains inputs and adds machinery for what should be a local rewrite.

3. **It's the wrong operation conceptually.** Inlining is query-unfolding — "compute q's value here." What Step B actually wants is **projection**: drop position j from q's *definition*, everywhere q is derived, under the pass-through guarantee. That's recursion-safe by construction (you rewrite the defining rules, you never unfold the recursion), which is the whole "one-shot, not unbounded unfolding" claim in Section 2. Inlining gets there only by accident on the simplest cases and diverges (lossily) the moment there's recursion or summation.

The good news: the spec already names the right substrate. Section 9 says `q_open_j` *is* the abbreviated item with the open position dropped, defined by projecting every rule deriving q, with `PassThroughWitness` as the soundness obligation. So this isn't a redesign — it's a re-weighting:

- **Demote** `rule_elimination` from "the inlining engine for Step B" (Section 8, bullet 1) to at most an M1 expedient for the trivial non-recursive case (E1) — or cut it.
- **Promote** the projection/abbreviation machinery (`dyna/analyze/abbreviate.py` + the openness fixpoint) to *the* basis for Steps B/C.
- **Reorder the milestones** so the foundation we trust is load-bearing first. Right now M2 is "re-enable `rule_elimination.py:64-94`" and M3 falls back to "inline via M2 for now" — i.e. the shakiest piece is the early dependency. Better: M1 openness fixpoint, M2 *project a single open position* (abbreviation of one position + the multiplicity accounting done in the projection, not in the inliner), M3 the closed/open split over occurrences.

Net: openness analysis decides *which* positions to drop; abbreviation/projection *drops* them soundly; `multiple` handles the summed-vanished-variable factor; residue isolation wraps what's left. `elim` doesn't need to be in the critical path at all.

Want me to rewrite Section 8 and the milestone list (M2/M3) along these lines, and recast Step B to lead with projection rather than inlining?
-->
<!-- chat Tim Vieira 2026-06-03 10:06
rule elimination is a transformation that has bad hygene it ought to rename the transformed relation since it messes with the semantics and it should add recovery rules.
-->
<!-- chat claude 2026-06-03 10:07
Yes — that's the right diagnosis, and it's stronger than "elim is lossy." The principle is **conservativity**: a definitional transform must not redefine an existing functor's meaning in place. `elim` does exactly that — it overwrites `temp` with a different relation — so of course the semantics drift. Proper hygiene is two-part, and you named both:

1. **Rename** the transformed relation to a fresh functor (`temp'`, `q_open_j`, …). The original symbol keeps its meaning; the new symbol is what the transform actually produces.
2. **Add recovery rules** bridging old to new, so the original relation is still derivable. The program stays conservative over the original signature.

The payoff for this spec is bigger than fixing a tool: **the recovery rule *is* the residue.** The diagonal `elim` silently dropped reappears, by construction, as the recovery rule. So:

- The CFG analogy was always about hygiene. `S0 -> S | epsilon` is literally *rename* (`S → S0`, the ε-free relation) plus *recovery* (`S0 -> epsilon`). ε-elimination is conservative precisely because it does rename+recover; `elim` is unhygienic because it does neither. The spec's own mental model (Section 2) already encodes the discipline — it just hasn't been applied to the implementation.

- Abbreviation already does half of it: it introduces a fresh projected symbol `q_open_j`. The missing half is the systematic recovery rule for `q` — which is `q(..,V,..) += q_open_j` (open residue), or `q(..,V,..) += adom(V) * q_open_j` under Step E. That recovery rule, when it stays non-range-restricted, is exactly `R`.

This collapses Steps B/C/D into one schema instead of three ad-hoc moves: every projection step emits (a) a fresh range-restricted definition and (b) a recovery rule; multiplicity (`multiple`) rides on the recovery rule when a summed variable vanished; and `R` is simply *the set of recovery rules that remain non-range-restricted*. Each step is value-preserving by construction because the original relations are always recoverable — which is the soundness argument the spec currently has to make separately.

And it settles the foundation question from last turn cleanly: don't re-enable `elim`'s in-place rewrite at all. The basis is **hygienic fold/project**: openness fixpoint picks the positions, projection introduces fresh `q\j`, recovery rules re-express the originals, `R` is the leftover non-range-restricted recovery rules. `elim` isn't in the critical path.

For E2 this reads naturally: the diagonal base rule isn't eliminated — it *is* the recovery rule `temp(X0,X0) += 1` (the `S0 -> epsilon` of this program), irreducible without `adom`, and the rest sits above it.

This is worth promoting to a first-class principle in the doc — a "Hygiene" subsection stating rename+recovery, then recasting Steps B–D as "project to fresh symbol + emit recovery rule," with `R` defined as the surviving non-range-restricted recovery rules. Want me to draft that and rework Sections 5 and 8 accordingly?
-->
<!-- chat Tim Vieira 2026-06-03 10:09
do it
-->
<!-- chat Tim Vieira 2026-06-03 10:11
do ti
-->
<!-- chat Tim Vieira 2026-06-03 10:14
Is this doc making a flatness assumption about items?
-->
<!-- chat claude 2026-06-03 10:15
Yes — pervasively, and it's load-bearing. The operative unit of analysis throughout is the **top-level predicate-position `(p, i)`**: a functor/arity plus an argument *index* `i ∈ 1..arity`. That's a flat-term notion. Concretely:

- The openness fixpoint's carrier is "the finite set of predicate-positions" / "(functor/arity, position) pairs" (Step A line 189, M1 line 418). Index, not tree path.
- `groundable`/`open`/`only-open` are all defined on `(p,i)` (lines 80–85).
- `q\j` is "the projected **lower-arity** item ... `q` projected to drop position `j`" (lines 212, 216). This assumes the open content fills a whole top-level slot that you can excise and decrement the arity.

The doc gestures at structure exactly once — "Track *positions*, not just variables, so that list/structured heads are handled per position" (lines 193–195) — but that only says "don't conflate a head's several top-level slots into one variable." It does **not** handle a variable buried *inside* one position. So it's still flat, just not variable-keyed.

Where the flatness assumption breaks:

1. **Open variable nested in a structured argument.** `f(g(X)) += 3.` The open `X` sits at path `1.1`, not at top-level position 1. "Drop position 1" throws away the `g(...)` skeleton too — wrong. You want to *abstract the open subterm at a path while keeping the surrounding ground skeleton* (anti-unification), not lower the arity.

2. **Internal sharing across one position.** This is the structured twin of E2. `temp(X0,X0)` works only because the diagonal happens to span two *top-level* positions. Write it as `temp(pair(X0,X0)) += 1.` and the `X0=X0` equality lives *inside* position 1; a top-level-position fixpoint can't see it — it marks `(temp,1)` open and projects the whole pair away, losing the sharing.

3. **Lists / recursive structure.** `p([H|T])` has openness at unbounded-depth paths in the tail; the "positions" of a list aren't a fixed finite top-level set at all.

4. **Invariance.** A top-level-index analysis is *not* invariant under wrapping in a dummy functor (`f(X)` → `w(f(X))` relocates the open content into a path inside `(w,1)`) or threading a dummy argument (shifts arities/indices). Those are exactly the metamorphic perturbations the `dyna-invariance-critic` skill checks — the analysis would give different answers under them, which is the over-indexing-on-functor-arity antipattern.

Note there's also an internal mismatch: Step B leans on the abbreviation/projection machinery for `q\j`, and abbreviation in dyna is (or should be) path-based — but Step A's carrier is flatter than the projection it feeds, so the analysis can't even *name* the positions the projector could drop.

The fix is a short "Term structure" note that (a) states the flatness assumption explicitly, (b) generalizes the carrier from top-level positions `(p,i)` to **tree paths** into head/body terms, (c) recasts `q\j` as "abstract the open subterm at a path, retaining the ground skeleton" rather than "lower the arity," and (d) adds an explicit invariance requirement + metamorphic tests (`temp(pair(X0,X0))`, `w(f(X))`, list-tail openness) per the invariance-critic. Want me to draft that and thread "path" through Step A / Step B / M1?
-->
<!-- chat Tim Vieira 2026-06-03 10:16
no flatness assumptions allowed - dyna is not datalog and we don't want parital soltiions
-->
<!-- chat Tim Vieira 2026-06-12 (paraphrased)
note that abbreviate has some issues -- the whole point for this new version is
that abbreviate was supposed to solve this issue, but fell short.
-->
<!-- chat claude 2026-06-12
Revised the spec to resolve both standing comments.

Flatness removed: new §3.2 (term structure / no flatness) states that nothing
may key on a top-level argument index; §3's definitions are recast from
(p, i) pairs to $free-marked variable occurrences in derivable item types (the
existing type-analysis representation); Step A is recast as the type analysis
over the $free-instrumented program (with the §3.1 input seeding), terminating
by widening rather than by a finite slot set; §2's table and the termination
arguments updated to match. The q\j notation is retained but explicitly
reinterpreted as "open occurrence at any depth," and projection is "abstract
the open subterm, retain the ground skeleton," not arity lowering. Added E6
(temp(pair(X0,X0)) — nested shared diagonal) as the precision canary: the type
analysis must keep the sharing through widening, and fixing the widening is in
scope for M1 if it's too coarse. M1 and DoD #7/#8 now require the metamorphic
invariance tests (rename / wrap / thread).

Abbreviate repositioned per the 2026-06-12 note: it is the structural
precedent, not the foundation. §8 now says explicitly that Abbreviate fell
short — no explicit projection proof, drop/retention behavior dependent on
rewrite artifacts, generalized structure unexplained (the abbreviation doc's
Option A–D audit) — and that this transform reuses its discipline (fresh
functors, recovery rules, __dropped_var_correction's threaded-variable guard)
while gating every drop on Step A's openness verdict + the pass-through
obligation, never on the current heuristics. §9 adds that the pass-through
audit is chosen-but-unbuilt (Option C), so building it is part of M2.

Also fixed a correctness trap: Program.is_range_restricted (program.py:857) is
purely syntactic and calls E5 restricted; §8, M3, and DoD #3 now require the
refined generating-occurrence per-rule check as the stop condition, with the
syntactic predicate demoted to a necessary-but-insufficient fast path.
-->
