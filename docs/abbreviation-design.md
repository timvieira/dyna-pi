# Abbreviation Design Notes

This note is a reset point for the abbreviation transformation.  The goal is to
derive a sound transformation before changing code.  In particular, `$free`
should not have special behavior in the rewrite engine.  It may remain a
notation for an analysis result, but rewrites should operate on ordinary type
constraints.

## Executive Summary

The central conclusion is that `$free` should not carry special semantics in
the rewrite engine.  It should be evidence consumed by a separate
projection/mode analysis.  Rewrites should compute ordinary type closure and
consistency; abbreviation should decide which item positions can be dropped.

The first implementation should be conservative:

```text
type analysis -> projection audit -> abbreviation code generation
```

The projection audit should retain every position by default and drop a
position only with an explicit proof.  The proof cases are:

```text
PassThroughWitness:
    The position is carried through without being inspected.  If a local
    witness is dropped, add the multiplicity correction.

DeterminedBy:
    The retained key determines the omitted position.  This is a functional
    dependency proof, not a multiplicity proof.

StructuralQuotient:
    The projection preserves structural and recursive behavior.  This is the
    proof needed for list tails and slash-item compaction.
```

The recommended first milestone supports only `PassThroughWitness`; all other
positions are retained.  This may abbreviate less than the current
implementation, especially for slashed CKY, but it gives a sound proof surface
and avoids encoding heuristics in `$free` or rewrite intersection.

Evidence so far:

- The current abbreviation and slashed-type tests pass, but they mostly check
  selected output values rather than projection soundness.
- The infinite-multiplicity example is a genuine pass-through witness case.
- List beta currently retains generalized tail structure, but this should be
  guaranteed by a structural blocker rather than an accident of current types.
- Slashed CKY is the main stress test: branch-local `$free` evidence cannot
  justify current slash compaction; it needs rule-instance flow proof.

A related transform, range-restriction normalization, is now spec'd as a
standalone goal-directed document in `range-restriction-normalization.md`.  It
constructs McAllester's "eliminate non-range-restricted rules" claim by analogy
to CFG epsilon-production removal: non-range-restriction is pushed into a single
superficial residual layer at the outputs.  Its open-position projection is the
same operation as abbreviation, and it reuses this document's
`PassThroughWitness` proof, so the two efforts share one soundness obligation
rather than two.

## Problem Statement

Abbreviation partitions items by simple type and replaces each typed item with a
type-specific item whose arguments are only the variables needed to preserve the
program's observable meaning.

The transformation should preserve values for the original outputs.  Recovery
rules may restore original item names from abbreviated items, but the
abbreviated program must not undercount, overcount, or silently prune valid
derivations.

The difficult case is dropping variables.  A dropped variable can be sound only
when the projection is proved compatible with rule evaluation and the variable's
contribution is accounted for by one of the following proof cases:

1. The variable is functionally determined by retained variables and retained
   constraints.
2. The variable is not semantically inspected, the quotient identifies only
   indistinguishable witnesses, and any remaining witness count is represented
   by the multiplicity correction.
3. The variable is absent from all relevant derivations after a semantics-
   preserving specialization.

If none of these is proved, the variable must be retained.  Multiplicity
correction is not a license to drop a variable; it is only the final accounting
step after the projection has already been justified.

## Things That Must Stay Separate

The current discussion has repeatedly mixed together several notions.  A sound
design should keep them separate.

**Type constraints**

These are ordinary constraints such as `n(I)`, `$bound(I)`, shape constraints,
equalities, and user-supplied type facts.  They participate in propagation and
intersection.  They prove which typed branch a term belongs to.

**Pass-through evidence**

This is evidence that a variable is carried through a derivation without being
instantiated or inspected.  `$free(X)` may be the surface notation for this
evidence, but it is not a normal type constraint.  In particular, it should not
change intersection semantics in the rewrite engine.

**Projection**

Projection is the choice of arguments for the abbreviated item.  Projection is
where variables may be omitted.  Projection should be driven by explicit proof
obligations, not by artifacts of type propagation.

**Multiplicity**

Multiplicity is a semantic correction for summing over omitted local variables.
It is not a proof that dropping was valid.  It applies only after a separate
argument says that the omitted variable is semantically irrelevant except for
the number of witnesses.

## Current Dissertation Model

The dissertation's abbreviation pseudocode describes abbreviation as a
type-indexed naming scheme:

- pick a disjoint simple type `t`,
- define a fresh symbol for that type,
- use the variables of the typed item as the abbreviation arguments,
- optionally omit completely free variables,
- add recovery rules and transformed rules,
- apply multiplicity correction when free variables are summed away.

Two phrases need sharpening before implementation:

- "necessary arguments"
- "completely free variables"

The implementation cannot infer these by looking at variable names, truncation
markers, or accidental interactions with rewrites.  They need formal meaning.

### Dissertation Source Check

Local source checked:

```text
/home/timv/projects/thesis/overleaf/types/specialization.tex
/home/timv/projects/thesis/overleaf/transformations/hoist.tex
/home/timv/projects/thesis/overleaf/types/runtime.tex
```

The abbreviation section in `types/specialization.tex` matches the current
implementation's broad shape:

```text
Abbreviate(program, type chart):
    assert simple types are pairwise disjoint
    assign a fresh item name to each simple type
    add input dispatch or output recovery rules
    enumerate typed source-rule instances
    propagate body constraints
    check head constraints
    replace head and body items with type-specific abbreviations
```

Two dissertation notes are exactly where this design document needs to sharpen
the story:

```text
Completely free variables may be omitted from the abbreviation tuple.

If free variables are summed in the abbreviation, multiply the generated rule
by infinity times the semiring one.
```

Those notes identify the intended consumer of "free" information, but they do
not define a proof obligation for "completely free."  The current design fills
that gap with `PassThroughWitness`.

The hoist chapter makes the dependency on abbreviation more concrete.  In the
unary-chain CKY example, the dissertation says specialization recognizes shared
span equalities such as `I = I'` and `K = K'`, then drops span variables that
are always free in the slashed items.  In the vertical-fold example, it says
speculation's slashed item is effectively a naming scheme for a smaller `tmp`
item, and abbreviation should automate that naming.

This supports two conclusions:

1. `$free` exists here primarily to serve abbreviation, not because rewrite
   intersection needs special free-variable semantics.
2. Slashed items are the important stress test.  They are exactly where
   "free" span variables can be reusable dimensions, but the equality and
   numerator/denominator structure must be proved, not guessed.

The runtime chapter independently points toward the same missing abstraction:
it lists a more sophisticated mode system, citing Overton and NWF, as future
work for reasoning about variable instantiation states and delayed constraints.
That is consistent with replacing rewrite-level `$free` behavior with a
separate mode/projection analysis.

## Soundness Invariant

Let `A_t(x)` be the abbreviated item for original item `x` under type branch
`t`.  Let `pi_t` be the projection from `x`'s variables to the retained
arguments of `A_t`.

For each generated rule, every concrete grounding of the source rule should map
to exactly the correct contribution in the target program:

- If two source groundings have the same projected target grounding, then either
  they are semantically the same contribution or the target rule includes the
  correct multiplicity factor.
- If a source grounding satisfies the selected type branch, the target program
  must have a corresponding derivation unless the original contribution is
  provably zero.
- If a target grounding is generated, it must correspond to at least one source
  grounding of the selected typed source rule.

This suggests proving abbreviation as a quotient of typed derivations.  The
projection is sound only if the quotient is compatible with rule evaluation.

## Candidate Analysis: Pass-Through Variables

We want an analysis that identifies variables that are uninstantiated in a
stronger sense than "not mentioned by a constraint."

A variable is pass-through in a typed derivation when:

1. It may appear in heads and selected body atoms.
2. It is never constrained by a non-pass-through type constraint.
3. It is never unified with a non-variable term or with a variable that is
   inspected.
4. It is not required to preserve a functional dependency or equality among
   retained variables.

This can be viewed as a dataflow problem over variables in rule/type instances.
The analysis should produce explicit evidence such as:

```text
pass(t, X)
```

where `t` is a simple type branch and `X` is a variable of that branch.  If the
analysis cannot prove `pass(t, X)`, then `X` is retained.

Design decision for the first implementation: run pass-through analysis after
type analysis as a separate projection/audit pass.  Extending type analysis to
carry modes internally remains a future option, but a separate pass is the
smallest change that isolates `$free` from type rewriting.

## Relation To Magic Sets Adornment

Magic sets uses adornments such as bound/free modes to track how information
flows from a query into rule bodies.  That is close to what we need, but the
purpose differs:

- Magic adornment is demand-driven: which arguments are known from the query?
- Abbreviation pass-through is quotient-driven: which arguments can be omitted
  from an item representation without changing output values?

The useful connection is sideways information passing.  A variable that becomes
bound or inspected by a preceding subgoal is not pass-through.  A variable that
only moves through item arguments, and never affects a constraint, may be
pass-through.

Reading result: magic-template adornment gives a useful model of sideways
information flow, but it does not by itself prove that variables can be omitted
from Dyna table keys.

### Magic Templates Reading Notes

Primary source checked:

- [Ramakrishnan, "Magic Templates: A Spellbinding Approach To Logic
  Programs"](https://www.sciencedirect.com/science/article/pii/074310669190026L)

The relevant points from the paper abstract are:

```text
Magic Templates generalizes magic sets to allow bottom-up evaluation with
nonground facts.

It treats an argument as bound when it contains a function symbol or a variable
that appears more than once in the argument list, even if the rules do not
provide ground bindings for that argument.

The generated magic predicates compute the goals reached by a top-down
exploration, then restrict bottom-up evaluation to those goals.

The price is storing nonground facts and using unification rather than only
equijoins during bottom-up evaluation.
```

This is useful for Dyna abbreviation, but only indirectly.  Magic Templates is
about demand propagation and avoiding redundant bottom-up work under a chosen
sideways information-passing strategy.  It is not itself a proof that a Dyna
table key can quotient away a variable while preserving semiring values.

Transferable idea:

```text
Use SIPS/adornment-style flow edges to decide whether a variable is produced,
inspected, or merely passed through a typed rule instance.
```

Non-transferable as-is:

```text
Do not equate "free in a magic template" with "safe to omit from an
abbreviated item."
```

This matches the Eisner-Blatz discussion: variable dropping/term abbreviation
is best kept as a separate optional transformation after magic/slash-like
rewrites have introduced reusable nonground structure.

## Relation To Eisner & Blatz

The dissertation notes that Eisner & Blatz allude to abbreviation but do not
describe it in detail, and characterizes that transform as shape inference plus
modes, without functional dependencies or domain-size polynomials.

This suggests a possible decomposition:

1. Shape inference determines which structural branch an item belongs to.
2. Mode/adornment inference determines which variables are needed.
3. Abbreviation names the pair `(shape, mode)` and projects accordingly.

Reading result: Eisner-Blatz is useful mostly because it separates
abbreviation from magic/slash-like transformations.  The assumptions that
matter for this document are:

- Do they require range restriction?
- Do they rely on ground forward chaining?
- Do they allow structured terms with truncation or generalization?
- Is their abbreviation only a representation optimization, or does it change
  which items are computed?

## Relation To McAllester's Meta Theorem

McAllester's meta theorem is based on range restriction and prefix firings.  The
dissertation notes that McAllester allows structured terms but requires range
restriction.  This is directly relevant: our most problematic examples involve
non-range-restricted behavior or variables that are effectively not grounded.

One possible route is to treat abbreviation as downstream of a normalization
that eliminates non-range-restricted rules:

1. Transform or compile away non-range-restricted rules in a semantics-
   preserving way.
2. Run ordinary type/usefulness analysis on the range-restricted program.
3. Abbreviate only with respect to the resulting range-restricted proof.

This would reduce the burden on `$free`: instead of making `$free` carry
semantic meaning through rewrites, non-range restriction would be handled by a
separate transformation with its own proof.

Reading result: McAllester supports the importance of the range-restricted,
ground-assertion boundary, but does not provide a ready-made Dyna semiring
abbreviation proof.  Range-restriction normalization remains a future research
track, not the first implementation strategy.

The constructive form of this normalization is now spec'd separately in
`range-restriction-normalization.md`.  It models the elimination on CFG
epsilon-production removal: non-range-restriction is pushed into a single
superficial residual layer at the outputs, and the projected open item it
produces is exactly the abbreviated item with the open position dropped.  That
document shares this one's `PassThroughWitness` proof rather than introducing a
separate semiring-preservation proof, which softens the Option D objection
(lines 2235-2244).

## External Literature Checks

Sources checked:

- [Eisner and Blatz, "Program Transformations for Optimization of Parsing
  Algorithms and Other Weighted Logic Programs"](https://languagelog.ldc.upenn.edu/myl/slides/www.cs.jhu.edu/~jason/papers/eisner%2Bblatz.fg06.pdf)
- [FG 2006 proceedings copy of the Eisner-Blatz
  paper](https://web.stanford.edu/group/cslipublications/cslipublications/FG/2006/FG.pdf)
- [McAllester, "On the Complexity Analysis of Static
  Analyses"](https://www.cs.cmu.edu/~fp/courses/lp/handouts/mcallester02jacm.pdf)

Eisner-Blatz evidence:

```text
Their formalism starts from CKY-style weighted logic programs and explicitly
allows transformations to introduce rules that are not dynamic/range-restricted.
They say such rules can often be eliminated, but do not systematically develop
that elimination there.
```

The most relevant passage is in their magic-template discussion.  They contrast
dropping variables with leaving variables free, then defer term abbreviation to
an optional later transformation.  They say this is the same optional
transformation they would use for slash items introduced by speculation.

This supports the current design choice:

```text
abbreviation should be a separate projection proof pass
```

and not a behavior baked into magic, slash, or rewrite intersection.

McAllester evidence:

```text
The key termination and complexity lemmas assume range-restricted rules and
ground input data.  Under those assumptions, the algorithm never asserts open
atoms.
```

This is useful, but it does not by itself solve Dyna abbreviation.  It suggests
a possible normalization route:

```text
non-range-restricted program
    -> semantics-preserving range-restriction normalization
    -> ordinary type/usefulness analysis
    -> abbreviation with fewer free-variable obligations
```

But until such a normalization is defined for semiring-weighted Dyna programs,
McAllester should be treated as support for a conservative boundary, not as a
license to erase `$free`.

## Relation To Mercury Modes

Mercury's mode system is another useful point of comparison.  Mercury describes
the instantiation state of terms using instantiatedness trees with `free` and
`bound` states at type-tree nodes.  Standard modes such as `in` and `out` are
mappings from an initial instantiation state to a final one, e.g. `ground >>
ground` and `free >> ground`.  Mercury also has richer modes for partially
instantiated structures, such as known list skeletons whose elements are still
free variables.

For solver types, Mercury additionally has an `any` instantiation state.  The
exact solver-type semantics may not transfer directly, but the shape of the
idea is relevant: `any` behaves like an approximation that may stand for either
free or bound.  That suggests a small lattice for our analysis:

```text
          any
         /   \
      free  bound
         \   /
      impossible
```

or, depending on the order we need for dataflow, the dual lattice where
`unknown/any` is the least precise element and contradictions sit separately.
The key point is that `any` should mean "the analysis cannot distinguish free
from bound here," not "safe to treat as free."

This could help sharpen `$free`:

- `free`: proved pass-through/uninstantiated under the relevant mode.
- `bound`: proved instantiated or inspected.
- `any`: not enough information to choose; retain the variable.

Mercury also suggests that structure matters.  A term can be partially
instantiated: the outer list skeleton may be bound while the elements remain
free.  This is closely related to the list-beta example, where preserving or
dropping the tail cannot be decided by a single variable-level bit.  We may need
mode information over term structure, not just over variables.

Reading result: Mercury's `free/bound/any` discipline supports a conservative
term-position abstraction.  In particular, `any` should mean retain unless a
separate proof applies, and `free` should include a distinctness/no-aliasing
obligation.

## Toward A Dyna Mode System

Mercury and Prolog modes are usually described from a call perspective: at the
time a predicate is invoked, which arguments are input, output, free, ground, or
partially instantiated?  Dyna needs a related but different notion because Dyna
programs are normally evaluated bottom-up and memoize item values by default.

For Dyna, a mode system should probably describe table entries and rule
firings, not just calls.  A mode for an item could answer questions such as:

- Which parts of the item are represented in the table key?
- Which parts are known ground when the item is produced?
- Which parts are unconstrained/pass-through dimensions?
- Which parts are partially known structure, such as a list skeleton?
- Which variables are local witnesses that affect multiplicity but not the
  stored key?

That suggests a Dyna mode judgment shaped more like:

```text
mode[p/t](shape, key, inst, witnesses)
```

where:

- `shape` describes the structural type branch of the item;
- `key` is the projection used for table identity;
- `inst` maps variables or term positions to `free`, `bound`, or `any`;
- `witnesses` records variables that are not in the table key but are still
  counted by rule evaluation.

In a bottom-up setting, "bound" should not mean "provided by a caller."  It
should mean something closer to "the table entry or rule instance has enough
information to determine this part."  Similarly, "free" should not merely mean
"unbound at call time"; it should mean "not determined or inspected by the
derivation, and safe to quotient only if the witness accounting is correct."

This reframes abbreviation as a table-key optimization:

```text
original item:      p(X, Y, Z)
typed mode says:    X, Z are key; Y is pass-through witness
abbreviated item:   p_mode(X, Z)
rule correction:    account for omitted Y when it is local
```

The mode system would also help explain why bottom-up tabling differs from
Prolog/Mercury execution.  In a top-down mode system, a mode can reject a call
whose inputs are not instantiated enough.  In Dyna, the analogous failure mode
is that a proposed table key is too small: it merges entries whose future rule
firings are not equivalent.  That is exactly the unsound abbreviation failure
we want to avoid.

Design decision for the first implementation: infer projection facts for simple
type branches, with rule-instance flow used to validate drops.  Global item
modes are too coarse for abbreviation, and fully instance-local modes are a
larger design than the first milestone needs.

Design decision: keep `any` as an explicit conservative mode state in the
planning model.  If a position is `any`, abbreviation should retain it in the
key unless another proof, such as a functional dependency, justifies dropping
it.

## Mercury/Overton Reading Notes

These notes are an initial reading pass, not a full literature review.

Sources checked:

- [Mercury reference manual: modes](https://mercurylang.org/information/doc-latest/mercury_reference_manual/Modes.html)
- [Mercury reference manual: the `any` inst](https://mercurylang.org/information/doc-release/mercury_ref/The-any-inst.html)
- [Mercury papers page: Overton thesis summary](https://mercurylang.org/documentation/papers.html)
- [Overton thesis PDF mirror](https://citeseerx.ist.psu.edu/document?doi=9af5ab3ad5133b2fd4359083295ba364fbcfe26f&repid=rep1&type=pdf)

What seems directly useful:

1. Mercury modes are transitions between instantiation states.  The standard
   examples are `in == ground >> ground` and `out == free >> ground`.  This is
   a good reminder that a mode is not just a label on a variable; it is a
   before/after judgment about a computation.
2. Mercury's mode checker needs to know which conjuncts produce which variables
   and may reorder conjuncts so producers precede consumers.  Dyna's bottom-up
   evaluation does not use this call-order discipline, but we still need the
   producer/consumer distinction to know whether an item argument is part of a
   table key or only a witness.
3. Mercury instantiations are structural.  They can describe partially
   instantiated terms, not just whole variables.  This matters for lists: the
   list skeleton and the list elements may have different instantiation states.
4. Mercury solver types introduce `any`.  The important takeaway for us is
   conservative: `any` is not the same as "safe to drop."  It represents a state
   where ordinary groundness/free-ness reasoning is not precise enough.

Potential transfer to Dyna:

```text
Mercury "producer before consumer"
    -> Dyna rule-instance flow edge

Mercury instantiation tree
    -> Dyna mode tree over item term positions

Mercury free >> ground
    -> a relation/builtin can determine a variable

Mercury any
    -> Dyna must retain the position unless a separate proof applies

Mercury mode error
    -> Dyna projection proof failure
```

One important mismatch:

Mercury mode checking is primarily about whether a procedure call is legal and
how a procedure body can be scheduled.  Dyna abbreviation is about whether a
memoized item key can quotient multiple concrete items without changing
semiring values.  So we should borrow the abstract domain and producer/consumer
discipline, not the operational top-down call model wholesale.

Initial design constraint from this reading:

```text
If mode_join(position) = any,
then position must remain in the abbreviated key
unless a non-mode proof, such as a functional dependency,
justifies dropping it.
```

This is likely the right conservative interpretation of `any` for abbreviation.

Follow-up check from the official Mercury reference:

```text
Mercury instantiation trees attach free/bound information to type-tree nodes.
If a node is free, its descendants are free, and the corresponding variable is
distinct.  Modes are transitions between initial and final instantiation trees.
The standard modes are:
    in  = ground >> ground
    out = free  >> ground
```

This strengthens the structural part of the Dyna design.  A Dyna
`PassThroughWitness` cannot merely say "this variable is absent from ordinary
constraints."  It should also say that the omitted position does not introduce
aliasing/equality obligations.  Mercury's distinctness condition is the
analogous top-down restriction.

The official solver-type documentation says solver variables may have `free`,
`ground`, or `any` insts, and describes `any` as a state that may not yet be
semantically ground.  For Dyna abbreviation, the conservative transfer is:

```text
any -> retain unless a separate proof applies
```

not:

```text
any -> free enough to drop
```

This matches the current `DropProof` split: a mode join that yields `any` is
not itself a proof.  It may be a signal that `DeterminedBy` or
`StructuralQuotient` is needed.

## Structural Terms And Generalization

The list example exposes a separate issue: type generalization/truncation can
lose structural relationships.  If abbreviation projects variables based on a
generalized type, it may accidentally remove variables needed to keep recursive
definitions connected.

This is not a reason to add a syntactic truncation check.  The sound condition
should be semantic:

> A generalized type may be used for abbreviation only if the projection is a
> homomorphism from concrete type instances to abbreviated instances and the
> generated rules preserve that homomorphism.

If this cannot be proved, the type branch is not eligible for projection-based
dropping.  It may still be eligible for renaming with all variables retained.

Design decision for the first implementation: generalized type branches do not
provide enough evidence for structural dropping.  They should retain the
relevant positions unless a future `StructuralQuotient` proof supplies a
concretization relation.

## Proposed Conservative Algorithm Shape

This is not yet an implementation plan.  It is a target shape for a proof.

1. Compute disjoint simple types.
2. Compute a pass-through/adornment analysis over typed rule instances.
3. For each type branch `t`, choose retained variables:
   - retain variables inspected by constraints,
   - retain variables needed for head equality/shape,
   - retain variables needed by functional dependencies,
   - drop only variables with explicit pass-through evidence.
4. Generate recovery and transformed rules.
5. For each generated rule, compute whether dropped local variables introduce
   multiplicity; apply correction only for variables already proven
   pass-through.
6. Reject or retain all arguments for any branch where the projection proof is
   not available.

The key point is that step 6 is based on missing proof, not a syntactic
exception.

## Pseudocode Sketch

This pseudocode is intentionally proof-oriented.  It distinguishes the analyses
from the code-generation step, and it treats every omitted argument as a proof
obligation.

```text
Abbreviate(P, Types):
    require disjoint(Types)

    Flow = PassThroughAnalysis(P, Types)
    Proj = {}

    for each type branch t in Types:
        Proj[t] = ChooseProjection(t, Flow)
        require ProjectionSound(t, Proj[t], Flow)

    Q = empty program

    for each type branch t in Types:
        define fresh item A_t(args = Proj[t])

        if t.head is input:
            Q[A_t(Proj[t])] += t.head * retained_input_constraints(t)
        else:
            Q[t.head] += A_t(Proj[t])

    for each source rule r in P:
        for each typed instance inst of r under Types:
            if not InstanceSound(inst, Proj, Flow):
                Proj = RetainMoreArguments(inst, Proj)
                restart from projection-soundness checks

            rule = ProjectRule(inst, Proj)
            rule *= MultiplicityCorrection(inst, rule, Proj, Flow)
            Q.add(rule)

    return Q
```

The important part is that `RetainMoreArguments` is monotone: it may make the
abbreviation less compact, but it cannot invent a new projection.  If retaining
all variables is still not enough to justify a typed instance, then the issue is
not abbreviation; it is the type/specialization proof.

### Pass-Through Analysis

This is a candidate shape for a separate analysis pass.  It is deliberately
conservative: start with variables tentatively pass-through, then remove them
when there is evidence they are inspected or structurally needed.

```text
PassThroughAnalysis(P, Types):
    pass = { (t, X) | X in vars(t.head) and X is marked pass-through by Types }

    repeat until fixed point:
        for each typed rule instance inst:
            inspected = InspectedVars(inst)
            needed = EqualityAndShapeVars(inst)
            fd_needed = FunctionalDependencyVars(inst)

            for X in inspected union needed union fd_needed:
                remove all pass facts equivalent to X in inst

            for each variable equality X = Y in inst:
                if X is not pass-through:
                    remove pass(Y)
                if Y is not pass-through:
                    remove pass(X)

            for each flow edge X -> Y through a body/head item:
                if source side is not pass-through:
                    remove pass(target side)

    return pass
```

`InspectedVars` includes every variable mentioned by an ordinary type constraint
or builtin constraint.  `$free` is not an ordinary type constraint here; it is
only one possible source of initial pass-through evidence.

`EqualityAndShapeVars` includes variables needed to preserve equalities such as
`path(I,I)` and structural relationships such as list tails.  This is where the
list example forces precision: a tail variable cannot be dropped merely because
it appears under a generalized shape.

### Projection Choice

```text
ChooseProjection(t, Flow):
    keep = ordered vars(t.head)

    for X in ordered vars(t.head):
        if Flow proves pass(t, X)
           and not needed_by_shape_or_equality(t, X)
           and not needed_by_functional_dependency(t, X):
              keep.remove(X)

    return keep
```

This makes dropping opt-in.  The default is to retain.

### Projection Soundness

```text
ProjectionSound(t, keep, Flow):
    dropped = vars(t.head) - keep

    for X in dropped:
        require Flow proves pass(t, X)
        require X is not needed by ordinary constraints of t
        require quotienting by X preserves the concretization of t

    return true
```

The last requirement is intentionally semantic.  It is the place where we need a
real theorem.  For simple flat terms, it may be straightforward.  For
generalized structured terms, it may require an explicit concretization
relation from type analysis.

### Rule Projection

```text
ProjectRule(inst, Proj):
    # inst contains:
    #   head type t0 for source head x
    #   body types t1...tk for source body y1...yk
    #   propagated constraints C

    lhs = abbrev(t0, inst.head, Proj[t0])
    rhs = []

    for each body atom yi with type ti:
        rhs.append(abbrev(ti, yi, Proj[ti]))

    rhs.extend(head_constraints_not_implied_by_body(inst))
    return lhs += product(rhs)
```

The phrase `head_constraints_not_implied_by_body` must be defined using ordinary
constraint implication.  It should not rely on `$free`-specific intersection.

### Multiplicity Correction

```text
MultiplicityCorrection(inst, projected_rule, Proj, Flow):
    lost = local_source_variables(inst) - vars(projected_rule)

    for X in lost:
        require X is pass-through in inst
        require X is semantically irrelevant except for witness count

    if lost is empty:
        return 1
    if every X in lost has finite known cardinality:
        return product(cardinality(X | retained vars))
    return infinity
```

The finite-cardinality case may be useful later, but the current implementation
only has the infinite correction.  The correction is applied after projection
soundness is proved; it is not part of the projection proof.

## Worked Examples

**Diagonal path**

```dyna
path(I,I).
path(I,K) += path(I,J) * edge(J,K).
```

If usefulness constrains `path(I,K)` by `start(I), n(K)`, then the diagonal rule
must retain and enforce the equality `I = K` rather than treating either
variable as pass-through.

Suppose usefulness analysis gives the branch:

```text
path(I,J) :- start(I), n(I), n(J)
edge(J,K) :- n(J), n(K)
```

For the diagonal source rule:

```dyna
path(I,I).
```

the typed head must satisfy:

```text
path(I,I) :- start(I), n(I)
```

The equality is not optional.  If the abbreviation for the useful `path` branch
is `path_1(I,J)`, the generated rule is:

```dyna
path_1(I,I) += start(I) * n(I).
```

The projection decision is:

```text
vars(path(I,J)) = {I, J}
ordinary constraints mention I and J
head equality can identify I and J in one rule instance
drop set = {}
```

So neither `I` nor `J` is pass-through.  The rule is sound because every
grounding of the source diagonal maps to exactly one grounding of
`path_1(I,I)`, and there is no quotienting over either variable.

For the recursive source rule:

```dyna
path(I,K) += path(I,J) * edge(J,K).
```

the typed body implies `start(I), n(I), n(J), n(K)`.  The generated rule is:

```dyna
path_1(I,K) += path_1(I,J) * edge_0(J,K).
```

Again, no path argument is dropped.  The useful specialization constrains the
branch, but it does not create a free variable.

**Infinite multiplicity**

```dyna
goal += f(X).
f(X) += 3.
```

If `X` is dropped from the abbreviation for `f(X)`, then `goal += f(X)` sums
over infinitely many `X`.  The target needs multiplicity correction.

Assume type analysis has a branch:

```text
f(X) :- pass(X)
```

where `pass(X)` is analysis evidence, not a rewrite constraint.  The projection
for this branch may choose:

```text
A_f()
```

because `X` is pass-through and there are no ordinary constraints or shape
requirements that mention it.

For the source rule:

```dyna
f(X) += 3.
```

the projected rule is:

```dyna
f_1 += 3.
```

No multiplicity correction is needed in that rule because `X` appears in the
source head; the rule defines one value schema for `f`.

For the source rule:

```dyna
goal += f(X).
```

the projected body is:

```dyna
goal_0 += f_1.
```

But `X` was local to the original rule and has disappeared.  The rule used to
sum over all possible witnesses for `X`; the projected rule has only one body
instance.  Therefore:

```text
lost locals = {X}
pass-through(X) = true
ordinary constraints on X = none
cardinality(X) = infinity
```

The corrected target rule is:

```dyna
goal_0 += infinity * f_1.
```

This is sound only because `X` was already proved pass-through.  If `X` were
mentioned by a constraint such as `n(X)` or `X is Y+1`, multiplicity correction
alone would not justify dropping it.

**List beta**

```dyna
beta([X,Y|Xs]) += edge(X,Y) * beta([Y|Xs]).
beta([X]) += stop(X).
goal += start(X) * beta([X|Xs]).
```

The recursive tail structure is semantically important.  Any projection that
disconnects the recursive definitions is unsound.

Type analysis may infer finite-depth branches like:

```text
beta([X])          :- stop-like branch constraints
beta([X,Y])        :- edge-like branch constraints
beta([X,Y,Z])      :- edge-like branch constraints
beta([X,Y,Z,T|Ts]) :- generalized tail branch constraints
```

The dangerous projection is to abbreviate the generalized branch as if `T` and
`Ts` are irrelevant:

```text
beta_3(X,Y,Z)
```

That projection identifies many concrete lists:

```text
[X,Y,Z,a]
[X,Y,Z,b,c]
[X,Y,Z,T|Ts]
```

These lists are not automatically indistinguishable.  The recursive rule
peels one list cell:

```dyna
beta([X,Y|Xs]) += edge(X,Y) * beta([Y|Xs]).
```

So the tail determines which branch the recursive call enters.  Dropping tail
structure can disconnect rules such as:

```dyna
beta_3(...) += edge_0(...) * beta_2(...)
beta_3(...) += edge_0(...) * beta_3(...)
```

from the goal calls that need them, or merge cases with different recursive
behavior.

A sound projection must prove:

```text
for all concrete tails xs1, xs2:
    pi([X,Y,Z|xs1]) = pi([X,Y,Z|xs2])
    implies beta([X,Y,Z|xs1]) and beta([X,Y,Z|xs2])
    have indistinguishable behavior under every generated rule,
    up to explicit multiplicity.
```

The current design does not have that proof.  Therefore the conservative
decision is:

```text
retain tail variables needed to preserve recursive shape
```

or, if the type representation cannot express the needed concretization
relation, do not drop those variables.  This is not a special case for lists or
truncation markers; it follows from the missing projection proof.

**Functional dependency case**

Consider:

```dyna
use_city(Person) += lives_in(Person, City) * city_score(City).
```

If the input type includes a functional dependency:

```text
lives_in(Person, City) has City functionally determined by Person
```

then dropping `City` from an intermediate item may be sound in some contexts,
but not because `City` is pass-through.  It is sound because retained variables
determine it.

The projection proof is:

```text
same Person -> at most one City
```

so quotienting by `City` does not merge multiple distinct witnesses for the
same retained key.  This is a different proof case from pass-through, and the
analysis should keep it separate.

## Initial Example Audit

This section applies the audit template to the three priority examples.  The
point is to test the proposed mode vocabulary before implementing it.

### Audit 1: Diagonal Path

Source program:

```dyna
path(I,I).
path(I,K) += path(I,J) * edge(J,K).
```

Useful type context:

```text
edge(J,K)  :- n(J), n(K)
path(I,J)  :- start(I), n(I), n(J)
```

Mode facts:

```text
mode[path/useful]:
    shape      = path(I,J)
    key        = {I,J}
    inst(I)    = bound by start(I), n(I)
    inst(J)    = bound by n(J)
    witnesses  = {}

mode[edge/input]:
    shape      = edge(J,K)
    key        = {J,K}
    inst(J,K) = bound by n(J), n(K)
    witnesses = {}
```

Projection:

```text
path(I,J) -> path_1(I,J)
edge(J,K) -> edge_0(J,K)
```

Dropped variables:

```text
none
```

Proof case:

No variable is dropped.  The diagonal rule uses equality in the head:

```dyna
path(I,I).
```

The equality must be preserved in the projected head:

```dyna
path_1(I,I) += start(I) * n(I).
```

Expected transformed rules:

```dyna
edge_0(J,K) += edge(J,K) * n(J) * n(K).
path(I,J) += path_1(I,J).
path_1(I,I) += start(I) * n(I).
path_1(I,K) += path_1(I,J) * edge_0(J,K).
```

Failure mode if projection is too aggressive:

Dropping either `I` or `J` from `path_1` would merge diagonal and non-diagonal
items.  That loses the equality test and can introduce or remove derivations.

Conclusion:

This example should be accepted by a mode/projection system with no dropped
path arguments.  It is a specialization case, not a pass-through case.

### Audit 2: Infinite Multiplicity

Source program:

```dyna
goal += f(X).
f(1) += 2.
f(X) += 3.
g(X) += 4 * f(X).
```

Relevant type branches:

```text
f(1)
f(X) :- pass(X)
goal
g(1)
g(X) :- pass(X)
```

Mode facts:

```text
mode[f/free]:
    shape      = f(X)
    key        = {}
    inst(X)    = free/pass-through
    witnesses  = {X when f(X) is used in a local context}

mode[g/free]:
    shape      = g(X)
    key        = {}
    inst(X)    = free/pass-through
    witnesses  = {}
```

Projection:

```text
f(1) -> f_0
f(X) -> f_1
g(1) -> g_2
g(X) -> g_3
goal -> goal_4
```

Dropped variables:

```text
X from f(X)
X from g(X)
```

Proof case for dropped variables:

`X` is pass-through in the `f(X)` and `g(X)` branches because it is not
inspected by any ordinary constraint and does not affect branch selection after
the constant branch `f(1)` has been split out.

Multiplicity correction:

For:

```dyna
goal += f(X).
```

`X` is local to the source rule and disappears from the projected rule.  The
source sums over infinitely many witnesses, so the projected rule requires:

```dyna
goal_4 += infinity * f_1.
```

For:

```dyna
g(X) += 4 * f(X).
```

`X` appears in both source head and body and is dropped consistently from both
abbreviated items.  There is no local witness lost in that rule:

```dyna
g_3 += 4 * f_1.
```

Expected transformed rules:

```dyna
f(1) += f_0.
f(X) += f_1.
g(1) += g_2.
g(X) += g_3.
goal += goal_4.

goal_4 += f_0.
goal_4 += infinity * f_1.

f_0 += 2.
f_1 += 3.
g_2 += 4 * f_0.
g_3 += 4 * f_1.
```

Failure mode if projection is too aggressive:

If `X` is dropped from `f(X)` without multiplicity correction in `goal += f(X)`,
the transformed program undercounts `goal`.  If `X` is considered pass-through
before splitting out `f(1)`, then constant and nonconstant cases may be merged
incorrectly.

Conclusion:

This example should be accepted.  It is the canonical pass-through plus
multiplicity-correction case.

### Audit 3: List Beta

Source program:

```dyna
beta([X,Y|Xs]) += edge(X,Y) * beta([Y|Xs]).
beta([X]) += stop(X).
goal += start(X) * beta([X|Xs]).
```

Representative type branches:

```text
beta([X])
beta([X,Y])
beta([X,Y,Z])
beta([X,Y,Z,T|Ts])   # generalized tail branch
edge(X,Y)
start(X)
stop(X)
goal
```

Mode facts:

```text
mode[beta/one]:
    shape      = beta([X])
    key        = {X}
    inst(X)    = bound by stop/start/edge context
    witnesses  = {}

mode[beta/two]:
    shape      = beta([X,Y])
    key        = {X,Y}
    inst(X,Y) = bound by edge/recursive context
    witnesses = {}

mode[beta/generalized]:
    shape      = beta([X,Y,Z,T|Ts])
    key        = {X,Y,Z,T,Ts} unless proven otherwise
    inst(tail) = any or structural-unknown
    witnesses  = not established
```

Projection:

```text
beta([X])              -> beta_0(X)
beta([X,Y])            -> beta_1(X,Y)
beta([X,Y,Z])          -> beta_2(X,Y,Z)
beta([X,Y,Z,T|Ts])     -> beta_3(X,Y,Z,T,Ts)    # retain tail
```

Dropped variables:

```text
none from generalized tail branch
```

Proof case:

No proof currently justifies dropping `T` or `Ts`.  They are not merely local
witnesses; they determine which recursive branch `beta([Y|Xs])` enters after
one list cell is peeled.

Multiplicity correction:

None justified for generalized tail variables.  Multiplicity correction cannot
repair a projection that changes recursive branch behavior.

Expected transformed shape:

The exact generated rules may vary with the type chart, but the key requirement
is:

```text
recursive beta calls must preserve enough tail structure
to connect beta_3 goal calls with beta_3/beta_2 definitions.
```

Failure mode if projection is too aggressive:

Dropping generalized tail variables can produce goal calls such as:

```dyna
goal_5 += start_6(X) * beta_3(X, X1, X2)
```

while the recursive definitions require distinctions that were erased.  The
result can prune valid recursive definitions or merge cases with different
successor branches, causing undercounting.

Conclusion:

This example should reject tail dropping under the current evidence.  A future
structural mode/concretization proof might allow a smaller key, but the current
pass-through story is insufficient.

### Audit 4: Functional Dependency / Drop By Determination

Source program:

```dyna
goal(Person) += use_city(Person, City).
use_city(Person, City) += lives_in(Person, City) * city_score(City).

inputs: lives_in(Person, City); city_score(City).
outputs: goal(Person).
```

Assumed input invariant:

```text
lives_in(Person, City) has City functionally determined by Person
```

This means:

```text
forall Person, City1, City2:
    lives_in(Person, City1) and lives_in(Person, City2)
    implies City1 = City2
```

Useful type context:

```text
lives_in(Person, City) :- person(Person), city(City)
city_score(City)       :- city(City)
goal(Person)           :- person(Person)
use_city(Person, City) :- person(Person), city(City)
```

Mode facts:

```text
mode[use_city/fd]:
    shape       = use_city(Person, City)
    key         = {Person}
    inst(Person)= bound by goal/output context
    inst(City)  = determined by Person through lives_in
    witnesses   = {}
    fd          = Person -> City
```

Projection:

```text
use_city(Person, City) -> use_city_0(Person)
goal(Person)           -> goal_1(Person)
```

Dropped variables:

```text
City from use_city(Person, City)
```

Proof case for dropped variables:

`City` is not pass-through.  It is inspected by `city_score(City)`, and changing
`City` can change the contribution.  Dropping it is sound only under the
functional-dependency proof that the retained key `Person` determines `City` in
the relevant typed instance.

The proof obligation is:

```text
same retained key Person
    -> at most one compatible City in lives_in(Person, City)
    -> quotienting by City does not merge multiple different city_score values
```

Multiplicity correction:

None.  Functional dependency is an at-most-one proof, not a witness-counting
proof.  If the dependency is absent, a correction factor is not enough because
the omitted `City` may carry different `city_score` values.

Expected transformed shape:

```dyna
goal(Person) += goal_1(Person).

goal_1(Person) += use_city_0(Person).
use_city_0(Person) += lives_in(Person, City) * city_score(City).
```

If `use_city(Person, City)` must be recoverable as an output, the recovery rule
needs a support guard that does not duplicate the weighted contribution of
`lives_in`.  Without such a guard, abbreviation should retain `City` or decline
to abbreviate the output item.  If recovery is not needed because `use_city` is
internal and never queried, the abbreviated computation may still use
`use_city_0(Person)` as the table key.

Failure mode if projection is too aggressive:

If the input contains:

```text
lives_in(alice, paris)
lives_in(alice, rome)
city_score(paris) = 2
city_score(rome)  = 5
```

then `use_city_0(alice)` would merge contributions that are not equivalent.
The transformed program would either sum both cities, choose neither city
explicitly, or recover both original items from one abbreviated value.  None of
those behaviors is justified by pass-through reasoning.

Conclusion:

This example should be accepted only when the functional dependency is an
explicit input/type invariant available to abbreviation.  It is not a `$free`
case, and it should not use the pass-through judgment.

### Audit 5: Slashed CKY After Hoisting

Representative source program:

```dyna
p(X, I, K) += rewrite(X, Y, Z) * p(Y, I, J) * p(Z, J, K).
p(X, I, K) += rewrite(X, Y) * p(Y, I, K).
p(X, I, K) += rewrite(X, Y) * word(Y, I, K).
goal += length(N) * p("ROOT", 0, N).

inputs: rewrite(X,Y,Z); rewrite(X,Y); word(W,I,K); length(N).
outputs: goal.
```

The current tests slash either the unary recursive body item or the left child
of the binary rule:

```python
q = p.slash("p(X',I',K')", {1: 1}).prune()
q = p.slash("p(X',I',K')", {0: 1}).prune()
```

The slash transformation creates items shaped like:

```text
p(X,I,K) / p(X0,I0,K0)
$other(p(X,I,K))
```

The type-analysis tests for slashed CKY show branches such as:

```text
(p(X, I, K) / p(X, I, K))      :- $free(X) * $free(I) * $free(K)
(p(X, I, K) / p(X', I, K))     :- k(X) * k(X') * $free(I) * $free(K)
other(p(X, I, K))              :- k(X), n(I), n(K)
p(X0, I0, K0)                  :- k(X0), n(I0), n(K0)
```

and, for binary CKY:

```text
(c(B', I', J') / c(B', I', J'))        += $free(J') * $free(I') * $free(B')
(c(A, I', K) / c(B', I', J'))          += k(B') * n(J') * $free(I') * k(A) * n(K)
$other(c(A, I, K))                     += n(K) * k(A) * n(I)
c($X0, I', $X2)                        += n($X2) * n(I') * k($X0)
```

Mode facts:

```text
mode[slash/base]:
    shape      = p(X,I,K) / p(X,I,K)
    key        = {X,I,K} unless equality-preserving projection says otherwise
    inst       = equality between numerator and denominator positions
    witnesses  = {}

mode[slash/unary-chain]:
    shape      = p(X,I,K) / p(X0,I,K)
    key        = {X,X0,I,K}
    inst       = X and X0 are grammar categories; I,K are span endpoints
    witnesses  = {}

mode[other/phrase]:
    shape      = other(p(X,I,K))
    key        = {X,I,K}
    inst       = ordinary phrase chart item
    witnesses  = {}
```

Projection:

The conservative projection keeps slash numerator and denominator structure
unless a proof shows that some positions are determined by retained positions:

```text
p(X,I,K) / p(X,I,K)      -> slash_base(X,I,K)
p(X,I,K) / p(X0,I,K)     -> slash_unary(X,X0,I,K)
other(p(X,I,K))          -> other_phrase(X,I,K)
```

For the binary slashed shape:

```text
c(A,I,K) / c(B,I,J)      -> slash_binary(A,B,I,J,K)
```

Dropped variables:

```text
none by default
```

Proof case:

The tempting abbreviation is to treat positions marked by `$free` as droppable.
That is not sound by itself.  In these slashed programs, a variable can look
free in a local branch because the slash item carries an equality, a shared
span endpoint, or a numerator/denominator relationship that only becomes
meaningful when composed with `$other`.

The required proof is structural:

```text
pi(p_num / p_den) must preserve:
    numerator phrase identity needed by recombination,
    denominator phrase identity needed by $other,
    equalities between shared span endpoints,
    grammar-category positions used by rewrite/tag rules,
    recursive chain behavior of slash rules.
```

Multiplicity correction:

None is justified merely by slashing.  Span endpoints and grammar categories
are finite in typical CKY inputs, but finite domain size is not the same as a
pass-through witness count.  A correction factor would be justified only if the
omitted variable is proven to be irrelevant to every recombination and rule
selection step.

Expected transformed shape:

The exact generated item names may differ, but the shape should preserve the
slash relation:

```dyna
slash_base(X,I,K) += ...
slash_unary(X,X0,I,K) += rewrite(X,Y) * slash_unary(Y,X0,I,K).
other_phrase(X,I,K) += rewrite(X,Y,Z) * p(Y,I,J) * p(Z,J,K).
p(X,I,K) += slash_unary(X,X0,I,K) * other_phrase(X0,I,K).
```

For the binary left-child slash, the split point is semantically important:

```dyna
slash_binary(A,B,I,J,K) += ...
p(A,I,K) += slash_binary(A,B,I,J,K) * other_phrase(B,I,J).
```

Failure mode if projection is too aggressive:

Dropping `I`, `J`, or `K` can merge different spans.  Dropping `X`, `A`, or `B`
can merge different grammar categories.  Dropping the denominator phrase
identity can make the recombination rule attach the wrong `$other` item.  Any
of these changes can preserve a small test accidentally while changing the
chart recurrence.

Conclusion:

Slashed CKY should be treated as a structural-projection test, not as a
`$free`-dropping test.  The first sound implementation target should retain
all slash-structure positions.  Later compaction can be added only when the
projection proof can show that a denominator or endpoint is determined by the
retained slash key.

## Projection Proof Contract

Abbreviation should consume a small proof object for every omitted position.
The proof object is the boundary between analysis and code generation.

```text
DropProof =
    PassThroughWitness(position, witness_domain)
  | DeterminedBy(retained_positions, dependency)
  | StructuralQuotient(projection, concretization_relation)
```

Every dropped variable or term position must have exactly one primary proof.
The cases have different meanings and must not be collapsed:

```text
PassThroughWitness:
    The position is not inspected, not used for shape/equality, and not routed
    to a non-pass-through position.  If it is local to a projected rule, the
    rule needs an explicit multiplicity correction.

DeterminedBy:
    The retained key determines the omitted position.  No multiplicity
    correction is introduced, because the proof is at-most-one.

StructuralQuotient:
    The projection is a homomorphism from concrete typed items to abbreviated
    items, and every generated rule respects that homomorphism.
```

The default rule is:

```text
no proof -> retain the position
```

The implementation-facing checks should be:

```text
CheckProjection(type_branch t, projection pi):
    for each omitted position o:
        proof = proof_for(t, o)
        require proof exists

        if proof is PassThroughWitness:
            require o is absent from ordinary constraints
            require o is absent from equality/shape obligations
            require all flow successors of o are also pass-through

        if proof is DeterminedBy:
            require dependency is available as an input/type invariant
            require dependency covers the typed instance being projected

        if proof is StructuralQuotient:
            require concretization relation for t
            require every projected rule preserves pi

    return ok
```

The rule-projection check should then be:

```text
CheckProjectedRule(source_instance r, projected_rule r'):
    require each source body/head item maps through its branch projection
    require ordinary constraints in r are either retained or discharged
    require equality and structural constraints are preserved
    require local omitted variables have exactly the correction required by
            their DropProof
```

This contract gives the five audited examples clear outcomes:

```text
diagonal path:
    no dropped path arguments; equality preserved

infinite multiplicity:
    X is PassThroughWitness; local use in goal gets infinity correction

list beta:
    generalized tail has no proof; retain tail or reject projection

functional dependency:
    City is DeterminedBy(Person -> City); no witness correction

slashed CKY:
    slash structure has no droppable proof initially; retain numerator,
    denominator, category, and span positions
```

## Minimum Viable Sound Implementation

The first implementation milestone should be deliberately conservative.  Its
purpose is to make abbreviation proof-driven, not maximally compact.

Scope:

```text
Support initially:
    PassThroughWitness

Defer initially:
    DeterminedBy
    StructuralQuotient
```

This means the first pass may still generate larger abbreviated items than the
current implementation.  That is acceptable.  The invariant is:

```text
abbreviate less when proof is missing
```

not:

```text
recover today's shortest item names and arities
```

Concrete behavior:

1. Treat `$free` as analysis evidence only.  It must not change rewrite
   intersection semantics for abbreviation.
2. Default every type branch projection to all term positions needed to
   reconstruct the typed head.
3. Drop a position only when `PassThroughWitness` proves:
   - the position is marked pass-through by type/mode evidence;
   - the position is absent from ordinary non-`$free` constraints;
   - the position is not required by head equality or structural shape;
   - all flow successors are also pass-through;
   - any local witness multiplicity is explicitly accounted for.
4. When a projected rule would need `DeterminedBy` or `StructuralQuotient`,
   retain the position instead of approximating the proof.
5. If retaining positions still does not make the typed rule instance sound,
   reject that abbreviation branch rather than patching generated rules.

The first pass should not try to solve finite-domain counting, functional
dependencies, or structural quotienting.  Those are separate proof cases.  In
particular, slashed CKY should initially keep the slash numerator, denominator,
category, and span positions unless a later proof pass justifies compaction.

### Current Code Map

The current abbreviation implementation is small, which is useful.  The risky
semantic decisions are concentrated in a few places.

`dyna/analyze/abbreviate.py`:

```text
freebies(r)
    Extracts variables from $free constraints.
    Today this is both analysis evidence and projection evidence.

Abbreviate.__init__
    Builds recovery rules for each disjoint simple type.
    Joins body type branches with self.types.chart.lookup.
    Computes body_closure with ALLOW_FREE_MERGE=True.
    Intersects with head type using ALLOW_FREE_MERGE=False.
    Projects all typed items through __abbrev.

Abbreviate.__abbrev
    Chooses abbreviation arguments as:
        term_vars(t_type) - freebies(t_type)
    This is the central projection decision that must become proof-driven.

Abbreviate.__dropped_var_correction
    Adds infinity when the set of free local variables changes.
    Today this is tied to $free syntax rather than a DropProof.
```

`dyna/analyze/rewrites.py`:

```text
Rewrites.__call__(..., ALLOW_FREE_MERGE=True)
    Drops $free(X) when X is bound or appears in non-$free constraints.

Rewrites.__call__(..., ALLOW_FREE_MERGE=False)
    Treats $free(X) as incompatible with bound/equality-constrained uses.

Rewrites.intersect
    Defaults to ALLOW_FREE_MERGE=False.
```

For abbreviation, the design target is:

```text
rewrite/intersection:
    computes ordinary type closure and consistency

mode/projection pass:
    interprets $free-like evidence and produces DropProofs
```

`dyna/analyze/types.py`:

```text
add_free_constraints
    Adds $free(X) for non-range-restricted variables in the type program.

TypeAnalyzer.inputs
    Registers $free(_) and $bound(_) as builtin type parameters.

truncate_term
    Replaces over-depth structure with a fresh variable.
    This is where structural quotienting can lose list-tail information.
```

`dyna/program.py`:

```text
Program.multiple
Program.__setitem__
    Existing runtime machinery detects dropped nonground variables and inserts
    infinite multiplicity.  Abbreviation should use the same semantic concept,
    but driven by projected rule variables and DropProofs rather than $free
    constraints alone.
```

### Experiment Log: Current Tree

These checks were run against the current worktree on 2026-06-02.  They are
evidence about the existing implementation, not proof that the existing design
is satisfactory.

Targeted regression checks:

```text
pytest -q \
  test/test_abbreviate.py::test_infinite_multiplicity \
  test/test_abbreviate.py::test_path_list \
  test/test_abbreviate.py::test_cky_unary_cycle_factoring \
  test/test_abbreviate.py::test_cky_left_child_slash

result: 4 passed
```

Focused slashed/type checks:

```text
pytest -q \
  test/test_type_analysis.py::test_slashed_unary_cky \
  test/test_type_analysis.py::test_slash_binary_cky \
  test/test_type_analysis.py::test_word_list

result: 3 passed
```

Full abbreviation file:

```text
pytest -q test/test_abbreviate.py

result: 14 passed
```

Observations from local probes:

```text
infinite multiplicity:
    f(1) -> f_0/0
    f(X) -> f_1/0
    g(1) -> g_2/0
    g(X) -> g_3/0
    goal -> goal_4/0
    generated goal rule includes inf * f_1
```

This supports the claim that the existing implementation handles the simple
pass-through witness case, but it does so through `$free` syntax rather than an
explicit `PassThroughWitness` proof object.

```text
list beta:
    beta_0 arity 1
    beta_1 arity 2
    beta_2 arity 3
    beta_3 arity 5

    representative beta_3 heads:
        beta_3(X,Y,$X1,$Trunc,[])
        beta_3(X,Y,$X1,$Trunc,[$$Trunc1])
        beta_3(X,Y,$X1,$Trunc,[$$Trunc1,$X4])
        beta_3(X,Y,$X1,$Trunc,[$$Trunc1,$X4,$X5])
        beta_3(X,Y,$X1,$Trunc,[$$Trunc1,$X4,$X5,$X6|$X7])
```

This is better than the feared `beta_3(X,Y,Z)` projection.  The current tree
retains substantial tail structure in this example.  The remaining design
concern is not that the current test fails; it is that the current projection
rule has no explicit structural proof explaining why this retention happens or
when it would be required.

```text
slashed unary CKY:
    other phrase item keeps arity 3
    p chart item keeps arity 3
    slash chain item compacts to '/_1'(X, X')
    slash base item compacts to '/_2'

slashed left-child CKY:
    other phrase item keeps arity 3
    p chart item keeps arity 3
    slash chain item compacts to '/_1'(X, K, X', K')
    slash base item compacts to '/_2'
```

These tests still compute the expected `goal` value.  However, the projection
is more compact than the conservative design target for slashed CKY.  The doc's
implementation plan should therefore treat these as regression examples that
need a projection audit, not as proof that the current `$free` behavior is
generally sound.

### Prototype Experiment: Retain-By-Default Audit

I added a lightweight runnable prototype:

```text
python docs/abbreviation_projection_audit.py
```

The prototype inspects the current type chart.  It does not change the
implementation.  It computes:

```text
current_retained = term_vars(type_branch) - freebies(type_branch)
current_dropped  = freebies(type_branch)
```

and then applies one conservative audit rule:

```text
if a dropped variable appears in an ordinary non-$free/$bound constraint:
    retain it
else:
    mark it as a PassThroughWitness candidate that still needs a flow check
```

This is intentionally weaker than the final analysis.  Its purpose is to show
where the current projection policy is making semantic decisions.

Prototype verification:

```text
python -m py_compile docs/abbreviation_projection_audit.py
result: passed

python docs/abbreviation_projection_audit.py
result: passed
```

Results:

```text
infinite multiplicity:
    f(X) :- $free(X)
        current drops X
        audit: candidate PassThroughWitness; needs flow check

    g(X) :- $free(X)
        current drops X
        audit: candidate PassThroughWitness; needs flow check
```

This is the expected easy case.  The follow-up flow check must distinguish:

```text
goal += f(X)
    X is local after projection -> infinity correction

g(X) += 4 * f(X)
    X is dropped consistently from head and body -> no local correction
```

```text
list beta:
    beta([X])
    beta([X,Y])
    beta([X,Y,Z])
    beta([X,Y,Z,$Trunc|Rest])

    current drops no $free variables from beta branches
    generalized beta branch currently retains arity 5
```

This supports the structural-retention conclusion for the current test.  The
audit still needs a structural blocker so that future changes cannot silently
turn the generalized branch into a smaller projection without proving a
concretization relation.

The prototype also exposes a limitation: it audits variable sets, not term
positions.  In generalized list branches, several positions can collapse to the
same printed variable name or the same snapped variable.  The real audit must
be position-based:

```text
head position path -> retained/dropped/proof
```

not merely:

```text
variable -> retained/dropped/proof
```

```text
unary slashed CKY:
    p(X,I',K') / p(X',I',K')
        current keeps X, X'
        current drops I', K'
        audit: I', K' are candidates; need flow check

    p(X',I',K') / p(X',I',K')
        current drops X', I', K'
        audit: all are candidates; need flow check
```

```text
left-child slashed CKY:
    p(X,I',K) / p(X',I',K')
        current keeps X, K, X', K'
        current drops I'
        audit: I' is candidate; need flow check

    p(X',I',K') / p(X',I',K')
        current drops X', I', K'
        audit: all are candidates; need flow check
```

The slashed cases are the important finding.  A constraint-only audit cannot
reject the current drops, because the relevant obligation is not an ordinary
constraint.  It is a flow/structure obligation:

```text
Does the omitted span/category position remain irrelevant after recombination
with $other and recursive slash rules?
```

Therefore, the first real prototype must include rule-instance flow.  A pure
branch-local check is insufficient.

### Prototype: Projection Audit Surface

Before rewriting abbreviation, build a non-codegen audit surface that can be
called from tests.  This prototype can exist inside `dyna/analyze/abbreviate.py`
or a neighboring module, but it should not change generated programs at first.

Target interface:

```text
audit = abbreviation_projection_audit(program, types)

audit.branches:
    branch_id
    original_head
    retained_positions
    dropped_positions
    proofs
    blocked_candidates

audit.instances:
    source_rule_id
    head_branch_id
    body_branch_ids
    projected_head
    projected_body
    local_witnesses
    multiplicity_correction
    obligations
```

Example assertion style:

```text
free_f_branch = audit.find_branch(head_functor = "f", branch_shape = "free")
assert free_f_branch.drops(
    position = 0,
    proof = PassThroughWitness,
)

general_beta_branch = audit.find_branch(
    head_functor = "beta",
    structural_case = "generalized-list-tail",
)
assert general_beta_branch.retains_position("tail_head")
assert general_beta_branch.retains_position("tail_rest")

slash_branch = audit.find_branch(head_functor = "/")
assert slash_branch.has_no_unproved_drops()
```

The important design property is that the audit can fail before code
generation.  A generated program should be the result of a successful
projection proof, not the mechanism by which we discover whether the projection
was valid.

Prototype implementation sketch:

```text
class DropProof:
    kind
    position
    reason
    witness_domain

class Projection:
    branch_id
    retained_positions
    dropped: position -> DropProof
    blocked: position -> reason

def build_projection_audit(program, types):
    flow = build_rule_instance_flow(program, types)
    projections = []

    for branch in types.chart:
        projection = Projection.retain_all(branch)

        for position in head_positions(branch.head):
            proof = prove_pass_through(branch, position, flow)
            if proof is None:
                projection.blocked[position] = explain_blocker(...)
            else:
                projection.drop(position, proof)

        projections.append(projection)

    instances = [
        audit_projected_instance(rule, typed_body, typed_head, projections)
        for rule in program
        for typed_body in lookup_body_types(rule)
        for typed_head in lookup_head_types(rule, typed_body)
    ]

    return ProjectionAudit(projections, instances)
```

The first useful prototype does not need to make every proof precise.  It can
start by producing conservative blockers:

```text
ordinary constraint mentions position
shape/equality requires position
position flows to retained position
generalized structure lacks concretization proof
functional dependency proof not implemented
```

That is already enough to test the main design rule:

```text
no proof -> retain
```

### Option Matrix

The current evidence points to several possible implementation strategies.

```text
Option A: Keep current $free rewrite behavior
    Pros:
        smallest change
        current tests pass
    Cons:
        no explicit projection proof
        slashed CKY compaction depends on rewrite artifacts
        hard to explain soundness for generalized structure
    Decision:
        reject as final design

Option B: Remove all dropping; abbreviation only renames type branches
    Pros:
        sound with respect to projection
        simple implementation
    Cons:
        loses the main benefit for non-range-restricted and slashed programs
        fails the dissertation's intended use of abbreviation
    Decision:
        useful fallback, not sufficient

Option C: Separate projection audit with only PassThroughWitness initially
    Pros:
        isolates $free from rewrites
        preserves infinite-multiplicity use case
        gives tests a stable proof surface
        leaves room for later FD and structural proofs
    Cons:
        may initially retain more slash structure than today
        requires new flow analysis over typed rule instances
    Decision:
        recommended first implementation

Option D: Range-restriction normalization before abbreviation
    Pros:
        aligns with McAllester-style ground/open-atom boundary
        could reduce the need for free-variable reasoning
    Cons:
        needs a separate semiring-preservation proof
        may be a larger transformation than abbreviation itself
        does not directly explain slash-item compaction
    Decision:
        research track, not first implementation

Option E: Full Dyna mode system
    Pros:
        principled treatment of free/bound/any and delayed constraints
        likely useful beyond abbreviation
    Cons:
        broad language-design project
        too large as a prerequisite for fixing abbreviation
    Decision:
        long-term direction

Option F: Add DeterminedBy and StructuralQuotient proof cases now
    Pros:
        captures functional dependencies and list/slash compaction directly
    Cons:
        risks reintroducing heuristic patches if rushed
        requires new user/type invariants and concretization relations
    Decision:
        defer until PassThroughWitness audit is working
```

Recommended path:

```text
Option C first.
Use Option B as the fallback behavior whenever Option C cannot prove a drop.
Keep Options D, E, and F as explicit future research tracks.
```

### Current Conclusions

Conclusions supported by the dissertation check, literature check, tests, and
prototype:

1. `$free` should not be a rewrite-engine feature for abbreviation.
   It should be input evidence to a projection/mode analysis.
2. The current implementation passes the available tests, but the tests do not
   prove the projection policy.  They mostly prove selected end-to-end values.
3. The simple infinite-multiplicity example is a genuine pass-through witness
   case and should remain the first positive target.
4. List beta currently retains generalized tail structure.  The design still
   needs a structural blocker so this remains guaranteed rather than accidental.
5. Slashed CKY is the main stress test.  Current compaction may be valid, but
   it needs a rule-instance flow proof; branch-local `$free` evidence is too
   weak.
6. Functional dependency dropping is a separate proof case and should not be
   folded into pass-through.
7. The first implementation should be conservative: prove `PassThroughWitness`
   drops, otherwise retain.

### Deferred Research Tracks

These tracks are either required by the first coding milestone or explicitly
deferred.  They are recorded here so the next implementation pass does not
silently expand the scope.

```text
Pass-through flow rules:
    Required for first implementation.  The proof contract is specified here;
    executable inference rules belong in the projection audit.

Projection audit prototype:
    Research prototype exists at docs/abbreviation_projection_audit.py.
    It is intentionally variable-set based; implementation should be
    term-position based.

Slashed CKY proof:
    Deferred proof.  First implementation may retain more slash structure than
    today unless rule-instance flow proves the current compaction.

Structural generalized terms:
    Deferred proof.  First implementation should retain generalized positions
    unless StructuralQuotient supplies concretization.

Range-restriction normalization:
    Future track, not a prerequisite.

Functional dependencies:
    Future track.  Requires user/type FD invariants before supporting
    DeterminedBy.
```

### Document Definition Of Done

This research/planning document can be considered finished when it contains:

```text
1. A problem statement and soundness invariant.
2. Local dissertation evidence and external literature evidence.
3. A worked audit of the five priority examples.
4. Test/experiment evidence from the current implementation.
5. A prototype audit result that exercises at least:
       infinite multiplicity,
       list beta,
       unary slashed CKY,
       left-child slashed CKY.
6. A chosen first implementation strategy.
7. Explicitly deferred strategies with reasons.
8. A concrete first coding milestone and test plan.
```

Status against that checklist:

```text
1. done
2. done for a first planning document: dissertation, Eisner-Blatz,
   McAllester, Magic Templates, and Mercury/Overton have evidence passes
3. done
4. done for current targeted tests
5. done for a research prototype; runnable API exists, but it is variable-set
   based and intentionally weaker than the future implementation audit
6. done: Option C, separate projection audit with PassThroughWitness first
7. done for FD, structural quotient, range-restriction, and full mode system
8. done at planning level
```

### Implementation Shape

A clean refactor boundary would introduce two small internal concepts before
changing the generated rules:

```text
Projection:
    branch_id
    head_shape
    retained_positions
    dropped_positions -> DropProof

ProjectedInstance:
    source_rule_id
    typed_head_branch
    typed_body_branches
    projection_used_by_each_item
    local_witnesses
```

Then `__abbrev` should become a pure lookup:

```text
abbrev(type_instance, projection):
    instantiate projection.retained_positions against type_instance.head
    return fresh_abbrev_name(projection.branch_id)(retained_args...)
```

and the projection choice should move out of `__abbrev`:

```text
BuildProjections(types, flow):
    for each branch t:
        retained = all_head_positions(t)
        dropped = {}

        for each candidate position p:
            proof = prove_pass_through(t, p, flow)
            if proof exists:
                retained.remove(p)
                dropped[p] = proof

        return Projection(t.i, retained, dropped)
```

The projected-rule check should happen before constructing the final `Rule`:

```text
ProjectRule(instance, projections):
    projected = apply projections to head and body items
    require ordinary constraints are preserved or discharged
    witnesses = local source variables absent from projected rule

    for each witness:
        require witness has PassThroughWitness proof
        add required multiplicity correction

    return projected
```

This also gives a natural debug mode:

```text
for each omitted position:
    print branch, position, proof kind, and reason
for each retained candidate:
    print branch, position, blocking obligation
```

That debug output is the right replacement for trying to infer intent from
`$free` constraints in rewritten rules.

### Test Plan Before Code

The tests should lock down the conservative behavior before any implementation
change.

Keep existing positive tests:

```text
test_infinite_multiplicity
    Still expects a dropped pass-through variable in f(X) plus infinity in goal.

test_input_dispatch_keeps_user_type_constraints_not_free_bound_markers
    Input dispatch continues to preserve ordinary user constraints and strip
    only mode markers from generated input wrappers.

test_startpath3 or its enabled equivalent
    Useful path branch preserves path(I,J), including the diagonal equality.
```

Add or strengthen structural negative tests:

```text
test_path_list_does_not_drop_generalized_tail_without_projection_proof
    Construct the beta/list example with enough type depth to produce a
    generalized tail branch.
    Assert the abbreviated branch retains tail structure or the transformation
    declines that projection.
    Do not merely compare one tiny dataset.

test_slash_cky_retains_structural_key_without_projection_proof
    Run the unary and left-child slash examples through type analysis and
    abbreviation.
    Assert slash items retain numerator/denominator category and span
    positions unless a DropProof is present.
    Continue checking the goal value as a secondary test.
```

Add functional-dependency guard tests:

```text
test_fd_like_city_is_not_dropped_without_fd_proof
    Program:
        goal(Person) += use_city(Person, City).
        use_city(Person, City) += lives_in(Person, City) * city_score(City).
    Without an explicit FD proof, abbreviation must retain City.

test_fd_drop_is_deferred
    Mark the desired FD example as deferred until DeterminedBy exists.
    This documents that the design has a proof case but the first
    implementation does not.
```

Add a projection audit test helper if possible:

```text
assert_projection(program, types, expected):
    build projections without generating final rules
    compare branch_id -> retained_positions and dropped proof kinds
```

This helper would make the tests less brittle than asserting full generated
program text for every case.  Existing `assert_equal` tests can remain for
end-to-end regression, but projection tests should be the primary safety net
for the new proof-driven behavior.

### First Coding Milestone

The first coding milestone should be:

```text
1. Introduce Projection and DropProof data structures.
2. Preserve current output for the simple infinite-multiplicity case.
3. Replace __abbrev's projection formula with Projection.retained_positions.
4. Route multiplicity correction through PassThroughWitness proof objects.
5. Remove abbreviation's dependence on ALLOW_FREE_MERGE=True for deciding
   what can be dropped.
6. Add structural-retention tests for list beta and slashed CKY.
```

Non-milestone work:

```text
Do not implement DeterminedBy yet.
Do not implement StructuralQuotient yet.
Do not compact slashed CKY beyond retained structural keys yet.
Do not change general rewrite semantics as part of this milestone.
```

## Non-Goals

- Do not use variable names as semantic evidence.
- Do not special-case truncation markers.
- Do not rely on `$free` changing rewrite/intersection behavior.
- Do not add recovery rules that make a known counterexample pass without a
  proof of the projection.
- Do not treat multiplicity correction as a substitute for projection
  soundness.

## Research Backlog

This section preserves the longer research backlog.  The first implementation
does not require all tracks to be completed.  Their status is recorded so
future work can continue without reopening the core design decision.

### 1. Eisner & Blatz: Abbreviation, Modes, And Weighted Transformations

Status:

```text
first pass complete for planning purposes
```

Primary source:

- Eisner and Blatz, "Program Transformations for Optimization of Parsing
  Algorithms and Other Weighted Logic Programs", Formal Grammar 2007.

Questions to answer:

- Where do they use the term "abbreviation," if at all?
- Is abbreviation a formal transformation, an implementation convention, or an
  informal cleanup step after other transformations?
- Do their examples assume ground forward chaining, range restriction, or
  mixed-semiring machinery?
- Do they distinguish shape inference from mode/adornment inference?
- How do they avoid overcounting when transformations merge proof structure?

Concrete extraction:

```text
For each relevant transformed example:
    record original item schema
    record transformed item schema
    identify omitted variables
    identify why omitted variables are semantically irrelevant
    identify whether multiplicity or mixed-semiring machinery is involved
```

Expected output:

- A table of examples with columns:
  `example`, `omitted variable`, `reason sound`, `requires range restriction`,
  `requires mixed semiring`, `applicable to Dyna abbreviation`.

Success criterion:

- We can say which part of Eisner & Blatz is reusable for Dyna abbreviation and
  which part depends on assumptions we do not want in the rewrite engine.

### 2. Magic Templates: Adornment And Sideways Information Passing

Status:

```text
first pass complete for planning purposes
```

Primary source:

- Ramakrishnan, "Magic Templates: A Spellbinding Approach To Logic Programs",
  Journal of Logic Programming 1991.

Questions to answer:

- What exactly is an adornment in the magic-template setting?
- How are bound/free positions propagated through a rule body?
- Does the method support non-range-restricted rules directly, or does it first
  transform them into a range-restricted form?
- Is the adornment attached to predicates globally, to calls, or to rule
  instances?
- Can sideways information passing be reinterpreted for bottom-up tabling as a
  table-key analysis?

Concrete extraction:

```text
For each adorned predicate p^a:
    record what a classifies: arguments, variables, or term positions
    record how a changes across each body position
    record what happens to variables never made bound
```

Expected output:

- A candidate mapping from magic adornments to Dyna branch modes:

```text
magic bound position -> Dyna key/known position
magic free position  -> Dyna unknown/pass-through candidate
sideways binding     -> rule-instance flow edge
```

Success criterion:

- We can reuse the information-flow discipline without importing magic sets'
  mixed boolean/semiring transformation.

### 3. McAllester: Range Restriction And Prefix Firings

Status:

```text
first pass complete for planning purposes;
range-restriction normalization deferred
```

Primary source:

- McAllester, "On the Complexity Analysis of Static Analyses", JACM 2002.

Questions to answer:

- What exact range-restriction condition does the meta theorem require?
- Does McAllester give a constructive transformation for non-range-restricted
  rules, or only state that they can be avoided?
- Does the theorem allow structured terms directly, and what assumptions does
  it make about their generation?
- How does binarization/prefix memoization relate to Dyna table keys?
- Can the non-range-restricted case be normalized before abbreviation rather
  than represented by `$free`?

Concrete extraction:

```text
Find theorem/lemma statements mentioning:
    range restriction
    prefix firings
    binarization
    structured terms
    non-range-restricted transformations
For each statement:
    write the precondition in Dyna terms
    write whether semiring-weighted derivation sums preserve it
```

Expected output:

- A yes/no answer to:

```text
Can Dyna abbreviation be defined only after a sound range-restriction
normalization?
```

Success criterion:

- We know whether McAllester gives us a principled way to burn down `$free`, or
  whether `$free` remains necessary as a mode-analysis annotation.

### 4. Mercury And Overton: Instantiation Trees

Status:

```text
first pass complete for planning purposes;
full Dyna mode system deferred
```

Primary sources:

- Mercury language reference manual, especially modes and the `any`
  instantiatedness state.
- Overton, "Precise and Expressive Mode Systems for Typed Logic Programming
  Languages", PhD thesis, 2003.

Questions to answer:

- What is the formal lattice/order for `free`, `bound`, `ground`, partial
  instantiations, and `any`?
- Is `any` the union of `free` and `bound`, a solver-specific permission, or a
  separate approximation state?
- How do instantiation trees represent partially known structure?
- How are mode errors detected and reported?
- Is the analysis flow-sensitive, predicate-global, or call-pattern-specific?

Concrete extraction:

```text
For representative Mercury modes:
    in      = ?
    out     = ?
    free    = ?
    bound   = ?
    any     = ?
    partial list skeleton = ?
Translate each into a candidate Dyna table-entry interpretation.
```

Expected output:

- A proposed Dyna mode lattice for term positions, with joins/meets and a
  conservative interpretation of `any`.

Success criterion:

- We can state when a Dyna mode join should produce `any`, and we can state
  that `any` means "retain in the key" unless another proof applies.

### 5. Dyna Mode Judgment

Status:

```text
planning model selected;
full formalization deferred
```

Goal:

- Define a Dyna-specific judgment for bottom-up, memoized execution.

Candidate judgment:

```text
Modes |- p_t(term) : Mode

Mode = {
    shape: structural type branch,
    key: retained term positions,
    inst: term-position -> {free, bound, any},
    witnesses: variables omitted from key but counted by rules
}
```

Questions to answer:

- Should modes be attached to item symbols, simple type branches, or typed rule
  instances?
- Does `key` contain variables, term positions, or projections?
- How does a mode compose through a rule body under bottom-up evaluation?
- What does it mean for a body item to produce a binding in a bottom-up table?
- How do delayed builtins and input relations affect `inst`?

Expected output:

- A formal judgment with:
  - syntax,
  - concretization function,
  - ordering,
  - join operation,
  - transfer rule for one Dyna rule.

Success criterion:

- The judgment can express the diagonal path, infinite multiplicity, and list
  beta examples without referring to variable names or rewrite-engine `$free`
  behavior.

### 6. Pass-Through Judgment

Status:

```text
required for first implementation;
proof contract specified, executable rules still to be implemented
```

Goal:

- Refine "pass-through variable" into a judgment that abbreviation can consume.

Candidate judgment:

```text
Flow |- pass(inst, X)
```

Required meaning:

```text
For every concrete derivation represented by inst,
changing X while holding retained variables fixed
does not change:
    selected type branch,
    ordinary constraints,
    recursive rule behavior,
    output contribution,
except through explicitly accounted witness multiplicity.
```

Rules to formulate:

- Ordinary constraint rule: if a non-mode constraint mentions `X`, then not
  `pass(X)`.
- Equality/shape rule: if `X` is needed to preserve equality or term structure,
  then not `pass(X)`.
- Flow rule: if `X` flows into a non-pass-through position, then not `pass(X)`.
- Functional dependency rule: if `X` is determined by retained variables, then
  it may be dropped under the FD proof case, not under pass-through.
- Multiplicity rule: if local `X` is pass-through and omitted, compute witness
  correction.

Expected output:

- A set of inference rules and counterexamples for each rule.

Success criterion:

- The judgment is strong enough to reject the bad list-tail projection and
  precise enough to accept the infinite-multiplicity example.

### 7. Two-Pass Feasibility

Status:

```text
decision made for first implementation: run projection audit after type
analysis
```

Goal:

- Determine whether pass-through analysis can be implemented after type
  analysis, without changing rewrite semantics.

Experiment design, still on paper:

```text
Input:
    disjoint simple type chart
    typed rule instances generated by ordinary type lookup
    ordinary constraint propagation result without $free special cases

Pass 1:
    compute mode/instantiation facts for type branches

Pass 2:
    compute projection and multiplicity proof obligations
```

Questions to answer:

- What information is lost by type generalization before pass-through analysis?
- Does the analysis need concretization witnesses for generalized terms?
- Can `$free` annotations from current type analysis seed the pass-through pass
  while remaining outside rewrites?
- What does the analysis do when type branches overlap before disjointing?

Expected output:

- A decision:
  - "two-pass is sufficient,"
  - "type analysis must carry modes internally," or
  - "abbreviation requires a separate abstract domain."

Success criterion:

- We can explain where the list beta case lands and why.

### 8. Example Audit Before Code

Status:

```text
complete for the five priority examples in this document
```

Goal:

- Prevent another implementation pass before the theory explains the examples.

Required examples:

1. Diagonal path with usefulness constraints.
2. Infinite multiplicity from a dropped local pass-through variable.
3. List beta with generalized tails.
4. Functional dependency/drop-by-determination example.
5. Slashed CKY examples that currently rely on abbreviation after hoisting.

For each example, fill out:

```text
source program:
type branches:
mode facts:
projection:
dropped variables:
proof case for each dropped variable:
multiplicity correction:
expected transformed rules:
failure mode if projection is too aggressive:
```

Success criterion:

- No code changes until each example has a completed audit and every dropped
  variable is justified by exactly one proof case.
<!-- chat Tim Vieira 2026-06-03 09:02
McAllester claims that all non-range-restricted programs can be transformed into range-restricted programs (I am not sure that he provides the construction, however).  I would like to work out that construction precisely and completely.   I recognize that there might be a minor caveat to this: much like it is always possible to "eliminate nullary rules from a CFG" - what that actually means is that we can boil all of the nullary rules down into a single very superficial nullary rule at the top.  I believe that the McAllester result will have a small caveat like that one.  Please try to deliver a transformation that is as complete as this.
-->
<!-- chat claude 2026-06-03 09:05
Short version first: McAllester states range restriction as a *precondition* (the property that bottom-up firing never asserts an open atom), and — as your own reading notes already record at lines 388–392 and 2647–2651 — he asserts non-range-restricted rules "can be avoided" without developing the elimination. So we have to build it. And yes, it has exactly the ε-elimination shape you're guessing: you can push *all* non-range-restriction into a single superficial top layer, and the residue is irreducible for the same reason `S' → ε` is.

Here is the construction.

## 0. The exact CFG correspondence

The analogy is not loose — it's a term-by-term translation:

| ε-elimination (CFG) | range-restriction normalization (Dyna) |
|---|---|
| terminal alphabet | the universe / active domain of constants |
| nonterminal `A` | predicate-position `(p, i)` |
| `A` is **nullable** (`A ⇒* ε`) | `(p, i)` is **open** (p derivable with position `i` non-ground) |
| ε-production `A → ε` | non-range-restricted rule (free head variable) |
| inline nullable occurrences, expand over subsets | split each open occurrence into a *closed* and an *open* reading |
| `L(G') = L(G) \ {ε}` | `P'` range-restricted, agrees with `P` on every **ground** query |
| residual `S₀ → S \| ε`, `S₀→ε` the only ε-rule | a single **open output layer**; in weighted Dyna, the `∞·1̄` factor |

The load-bearing fact in both: nullability/openness is a **finite least fixpoint over a finite set of symbols** (nonterminals / predicate-positions), so the rewrite is a bounded, terminating, one-shot expansion — *not* unbounded unfolding. That's why recursion is not a problem.

## 1. Definition (so the target is unambiguous)

A rule `h += B` is **range-restricted** iff every variable in `h` occurs in a *range-generating* subgoal of `B` — a positive, groundable item position. Tests (`X<Y`, `X==Y` with both bound) and the unbound inputs of builtins (the `Y` in `X is Y+1`) are **not** generators. Operationally: from ground facts, a range-restricted program only ever asserts ground items.

## 2. Failure taxonomy

A head variable `X` is unbound in exactly three ways:

1. **Projection / pure free**: `X` in head, absent from body (`f(X) += 3`). This is the only *primitive* source.
2. **Test/builtin-only**: `X` appears only in tests or only as an unbound builtin input (`f(X) += g(Y) * (X>Y)`).
3. **Propagated**: `X` is "bound" only by consuming another item at a position that is itself open.

(2) reduces to (1)+(3): a test cannot generate, so `X` is effectively free; treat it like (1). So the whole problem is generated by projection rules and propagated through consumption — exactly as all CFG nullability is generated by `A→ε` and propagated through `A→αAβ`.

## 3. Openness fixpoint (the "nullable set")

Compute the least set `O` of predicate-positions:

```
groundable(p,i)  :=  some rule deriving p has position i ground in some firing
open(p,i)        :=  ¬ groundable(p,i)        # "only-open": every derivation leaves it free
```

A head variable `X` of rule `r` is **bindable** iff it occurs in a body subgoal at a *groundable* position (or as the output of a generator builtin). The base case `open(p,i)` comes from projection rules (X free in body); it propagates: if `p(…,X,…)` at head position `i` is filled only from open positions / tests, then `(p,i)` is open. Least fixpoint over the finite set of positions ⇒ terminates. This is structurally identical to the nullable-nonterminal fixpoint.

## 4. The rewrite (production expansion)

For each rule, take every body occurrence `q(…,V,…)` at an open position `(q,j)`. Like ε-elimination expanding over subsets of nullable occurrences, emit a copy of the rule for each choice of {closed, open} per such occurrence:

- **closed reading**: keep `q(…,V,…)`, require `V` ground here. If `(q,j)` is *only-open* (never groundable) this reading is dead — drop it (matches "a non-nullable occurrence can't go ε"). If you have an active domain (§6), the closed reading is `q(…,V,…) * adom(V)`.
- **open reading**: `q`'s value is independent of `V` at position `j` (that's what open *means* — the pass-through condition). Replace `q(…,V,…)` by the **projected lower-arity item** `q_open_j` and delete `V` from the body. If `V` was *summed* (local to the rule, now vanished), multiply by the witness count of `V`.

That projected item `q_open_j` is **literally the abbreviated item this whole document is about** — the open position dropped. So:

> **Range-restriction normalization and abbreviation are the same operation seen from two sides.** Abbreviating an open position = making its consumers range-restricted; the `∞·1̄` correction = the residue when the dropped position was summed over an infinite domain.

Worked, reproducing your canonical case:

```dyna
f(X) += 3.          % (f,1) only-open
goal += f(X).       % X local, occurs only at the open position of f
```
`f(X)` at `(f,1)` open; `X` bindable nowhere ⇒ closed reading dead, open reading only:
```dyna
f_open += 3.
goal   += inf * f_open.     % X was summed -> witness count = |universe| = inf
```
which is exactly your `goal_0 += inf * f_1`. The normalized program is range-restricted; the `inf` is the residue.

## 5. The residue — your caveat, precisely

After exhaustive rewriting, the *only* remaining non-range-restricted rules are open atoms whose free variable reaches an **output/goal** without ever being bound on any path. These cannot be inlined away — there is no consumer above them to absorb the variable. Confine them to one top layer:

```dyna
output(X) += f_open.        % the single residual open rule
```

This is the precise analog of `S₀ → S | ε` with `S₀→ε` the unique ε-rule: one superficial top-level rule carrying the irreducibility, the entire engine beneath it range-restricted. Its meaning is "the answer is the uniform value `f_open` for every `X`," i.e. a non-ground / quantified output object — which is genuinely what the original program meant, and genuinely not finitely groundable.

**Weighted form of the caveat.** If the output is a *sum* over the open variable rather than a uniform table (`goal` rather than `output(X)`), the residue collapses to a scalar: `∞ · 1̄` (or, in idempotent/max-plus semirings, just `1̄` — `∞` copies of the same value is one value). That semiring-dependence is the real subtlety the Boolean CFG picture hides.

## 6. The escape hatch (why the caveat's *size* is a choice)

If you accept an **active domain** predicate — `adom(c)` for every constant in the EDB/program, plus `adom(X) :- r(…,X,…)` per input position — then add `adom(V)` to every closed reading and the residue **vanishes**: the program becomes fully range-restricted with *zero* open rules, and `∞` is replaced by the finite `|adom|`. This is the database/Datalog answer and the standard "safe-ification."

So the honest statement of McAllester's claim is two-pronged:

- **With a materialized finite domain**: range restriction is *fully* achievable, no caveat (cost: you pay to enumerate `adom`, and you've committed to active-domain semantics).
- **Domain-independent / infinite universe**: the caveat is irreducible and equals the CFG ε-residue — one open top rule, or `∞·1̄` under summation. You cannot do better, for the same reason you cannot express `ε ∈ L` with zero ε-rules.

## 7. Termination & soundness notes

- **Termination**: the rewrite is one-shot over the finite fixpoint `O`; no recursive unfolding, so recursive open predicates (e.g. unary chains) are fine — they get a range-restricted closed version plus at most one open marker, never an infinite expansion.
- **Value-preservation**: each open reading is a fold/unfold step (sound in any semiring) *plus* a projection that is licensed only when the open position is truly value-independent — which is exactly your `PassThroughWitness` proof obligation. So the normalization is sound precisely when abbreviation's pass-through proof goes through; there is no separate proof debt.

---

This is, I think, "as complete as the CFG result": a finite fixpoint, a bounded expansion, a clean residue, and a stated escape hatch — with the bonus that it collapses into the abbreviation machinery you're already building rather than being a separate transformation (which retires Option D's "separate semiring-preservation proof" worry at lines 2241–2244).

Want me to write this up as a "Range-Restriction Normalization (constructive)" section in the doc, replacing the hand-wavy treatment at lines 336–351 and the §3 backlog entry?
-->
<!-- chat Tim Vieira 2026-06-03 09:47
Can you write this up as a standalone design doc.  Make sure the define this clearly so that I can pass this to an agent with a "/goal" directive to complete.
-->
<!-- chat claude 2026-06-03 09:50
Wrote `docs/range-restriction-normalization.md` — a standalone, goal-directed spec.

How it's structured for handoff to a `/goal` agent:

- **Goal callout** up top: one paragraph stating the deliverable, pointing at the acceptance criteria (§11) and ordered milestones (§10).
- **The math, made implementable**: the CFG↔Dyna correspondence table (§2), precise definitions of open/groundable/bindable (§3), the failure taxonomy (§4), and the five-step algorithm A–E (§5) — openness fixpoint, expansion, multiplicity, residue isolation, active-domain escape.
- **The theorem** (§6) restated as four properties the implementation must achieve, plus the irreducibility caveat (your ε analog).
- **Five worked examples E1–E5** (§7) written to double as the test fixtures — including the recursion case and the test-only-variable case.
- **Grounding in real code** (§8): `LinearRuleElimination` is the inliner, and its commented-out lines 64–94 are exactly Step C; reuse `linearize`, `is_range_restricted`, `Semiring.multiple`, `add_free_constraints`, `freebies`.
- **Five ordered, independently testable milestones** (§10), a checklist **Definition of Done** (§11), and **non-goals** (§12).

Two decisions baked in that you may want to confirm:
- I made it the **authority for the normalization transform** but explicitly subordinate to `abbreviation-design.md` on abbreviation proofs, and tied Step B's open reading to the `PassThroughWitness` obligation so there's no duplicate soundness proof (this retires your Option D worry, §9).
- I framed the `inf` factor as going through `Semiring.multiple` with an idempotent-semiring regression required (DoD #6), since `inf` copies collapse in Boolean/max-plus.

Nothing in `abbreviation-design.md` was changed. Want me to also drop a one-line pointer to this new doc from `abbreviation-design.md` §3 (lines 336–351), or leave them independent?
-->
<!-- chat Tim Vieira 2026-06-03 09:52
good idea
-->
<!-- chat claude 2026-06-03 09:52
Done. Added a pointer at the end of the "Relation To McAllester's Meta Theorem" section (after line 351) directing readers to `range-restriction-normalization.md`, noting it's the constructive form, the CFG-ε model, the abbreviation connection, and that it shares the `PassThroughWitness` proof (softening Option D). Left the rest of the section's framing intact.
-->
<!-- chat Tim Vieira 2026-06-03 09:53
add it to the exec summary too
-->
<!-- chat claude 2026-06-03 09:53
Added a pointer to the Executive Summary, right after the "Evidence so far" bullets — same framing as the McAllester-section note (constructive form, CFG-ε analogy, shared `PassThroughWitness` proof), kept short since it's the summary.
-->
