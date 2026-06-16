"""
Tests for the sound range-restriction normalization
(the normalization half of dyna/analyze/range_restriction.py).

Covers the three layers: the phantom analysis (sound + invariant), the phantom
projection, the value-split (constant-overlap), and the combined normalizer.
The load-bearing regression is `test_startpath3_sound`: abbreviate drops the
reflexive diagonal `path(I,I)` (all-zero paths); this refuses to project it.
"""

from dyna import Program, term_vars
from dyna.term import gen_functor
from dyna.analyze.range_restriction import (
    is_range_restricted, is_rule_range_restricted, bindable_vars,
    phantom_paths, PhantomProjection, ValueSplit, RangeRestrictionNormalizer,
    reachable_patterns, quotient_cancelling_paths, QuotientProjection,
)


# the unary-cycle CKY grammar (test_cky_unary_cycle_factoring); inputs are
# declared inline so the derivation seeds itself with no separate input type.
CKY = """
p(X, I, K) += rewrite(X, Y, Z) * p(Y, I, J) * p(Z, J, K).
p(X, I, K) += rewrite(X, Y) * p(Y, I, K).
p(X, I, K) += rewrite(X, Y) * word(Y, I, K).
goal += length(N) * p("ROOT", 0, N).
inputs: rewrite(X,Y,Z); rewrite(X,Y); word(W,I,K); length(N).
outputs: goal.
"""
CKY_DATA = """
word("papa",0,1)+=1. word("ate",1,2)+=1. word("the",2,3)+=1.
word("caviar",3,4)+=1. word("with",4,5)+=1. word("a",5,6)+=1. word("spoon",6,7)+=1.
rewrite("ROOT","S")+=1. rewrite("S","NP","VP")+=1. rewrite("VP","V","NP")+=1.
rewrite("VP","VP","PP")+=1. rewrite("NP","D","N")+=1. rewrite("NP","NP","PP")+=1.
rewrite("PP","P","NP")+=1. rewrite("NP","papa")+=1. rewrite("N","caviar")+=1.
rewrite("N","spoon")+=1. rewrite("V","ate")+=1. rewrite("P","with")+=1.
rewrite("D","the")+=1. rewrite("D","a")+=1. length(7)+=1.
rewrite("N","N1")+=.5. rewrite("N1","N2")+=.5. rewrite("N2","N3")+=.5.
rewrite("N3","N4")+=.5. rewrite("N4","N5")+=.5. rewrite("N5","N")+=.5.
"""


# --------------------------------------------- the refined range-restriction check

def test_refined_check_rejects_test_only_var():
    # the E5 trap: syntactic check passes (X in body), refined check rejects it
    p = Program('f(X) += g(Y) * (X > Y). goal += f(X). inputs: g(Y). outputs: goal.')
    assert p.is_range_restricted()          # syntactic: wrong
    assert not is_range_restricted(p)       # refined: right
    [rf, _] = p.rules
    assert not is_rule_range_restricted(p, rf)


def test_bindable_vars_binder_vs_test():
    # `is` binds the LHS when the RHS is bound; comparisons are tests that bind nothing
    p = Program('f(X) += g(Y) * (X is Y + 1). outputs: f(X).')
    [r] = p.rules
    assert term_vars(r.head) <= bindable_vars(p, r)
    q = Program('f(X) += g(Y) * (X > Y). outputs: f(X).')
    [r] = q.rules
    assert not (term_vars(r.head) <= bindable_vars(q, r))


def same(p, q, queries, D=''):
    "Assert programs `p` and `q` agree (by value) on each query under data `D`."
    ps, qs = (p + Program(D)).sol(), (q + Program(D)).sol()
    for qy in queries:
        qs.user_query(qy).assert_equal(ps.user_query(qy))


# ------------------------------------------------ analysis: sound + invariant

def test_phantom_paths_invariant_under_wrapping():
    assert phantom_paths(Program('f(X) += 3. goal += f(X). outputs: goal.')) == {('f', 1, (0,))}
    assert phantom_paths(Program('g(w(X)) += 3. goal += g(w(X)). outputs: goal.')) == {('g', 1, (0, 0))}
    assert phantom_paths(Program(
        'item(d,f(X)) += 3. goal += item(d,f(X)). outputs: goal.')) == {('item', 2, (1, 0))}


def test_self_recursive_phantom_lifts():
    # greatest-fixpoint: a self-recursive open position (the lifted geometric
    # series) is phantom — x(I)'s value is independent of I, so it lifts to a
    # scalar. A least fixpoint would miss this (the recursion is self-justifying).
    p = Program('x(I) += 1. x(I) += 0.5 * x(I). outputs: x(_).')
    assert phantom_paths(p) == {('x', 1, (0,))}
    q = p.normalize_range_restriction()
    same(p, q, ['x(j)', 'x(k)'])


def test_phantom_paths_excludes_diagonals():
    for src in ['temp(X0,X0) += 1. outputs: temp(A,B).',
                'path(I,I). path(I,K) += path(I,J)*edge(J,K). inputs: edge(I,J). outputs: path(I,K).',
                'f(X) += g(Y)*(X>Y). goal += f(X). inputs: g(Y). outputs: goal.']:
        assert phantom_paths(Program(src)) == set()


# --------------------------------------------------------- phantom projection

def test_baseline_and_wrapped_agree():
    for src in ['f(X)+=3. goal+=f(X). outputs: goal.',
                'g(w(X))+=3. goal+=g(w(X)). outputs: goal.',
                'item(d,f(X))+=3. goal+=item(d,f(X)). outputs: goal.']:
        p = Program(src)
        assert bool(phantom_paths(p))
        same(p, PhantomProjection(p), ['goal'])


def test_startpath3_sound():
    src = 'path(I,I). path(I,K) += path(I,J)*edge(J,K). inputs: edge(I,J). outputs: path(I,K).'
    D = 'edge(a,b)+=1. edge(b,c)+=1.'
    p = Program(src)
    assert phantom_paths(p) == set()
    same(p, PhantomProjection(p), ['path(a,a)', 'path(a,c)', 'path(c,c)', 'path(c,a)'], D=D)
    (PhantomProjection(p) + Program(D)).sol().assert_equal_query('path(a,a)', 1.0)


def test_diagonal_values_preserved():
    same(Program('q(X,X)+=2. q(X,Y)+=e(X,Y). out(A,B)+=q(A,B). inputs: e(X,Y). outputs: out(A,B).'),
                   PhantomProjection(Program('q(X,X)+=2. q(X,Y)+=e(X,Y). out(A,B)+=q(A,B). inputs: e(X,Y). outputs: out(A,B).')),
                   ['out(a,a)', 'out(c,c)', 'out(a,b)'], D='e(a,b)+=1.')


def test_constant_arg_consumed_generally_is_sound():
    p = Program('b(X,a) += 4. out(X,Y) += b(X,Y). outputs: out(X,Y).')
    same(p, PhantomProjection(p), ['out(a,a)', 'out(b,a)', 'out(a,b)'])


# --------------------------------------------------------------- value-split

def test_infinite_multiplicity_value_split():
    p = Program('f(1) += 2. f(X) += 3. goal += f(X). g(X) += 4*f(X). outputs: goal; g(X).')
    q = ValueSplit(p)
    same(p, q, ['goal', 'g(1)', 'g(7)', 'f(1)', 'f(2)'])
    q.sol().assert_equal_query('f(1)', 5.0)
    q.sol().assert_equal_query('f(2)', 3.0)
    assert is_range_restricted(q.engine_layer)


def test_multiple_specific_constants():
    p = Program('f(1) += 2. f(2) += 5. f(X) += 3. h(X) += f(X). outputs: h(X).')
    q = ValueSplit(p)
    same(p, q, ['h(1)', 'h(2)', 'h(7)'])
    q.sol().assert_equal_query('h(1)', 5.0)
    q.sol().assert_equal_query('h(2)', 8.0)
    q.sol().assert_equal_query('h(7)', 3.0)


def test_no_split_is_value_preserving():
    p = Program('f(X) += 3. out(X) += f(X). outputs: out(X).')
    same(p, ValueSplit(p), ['out(z)', 'out(a)'])


def test_value_split_is_path_based_nested_constant():
    # the constant/variable overlap can sit at any depth: f(g(1)) vs f(g(X))
    # splits just like f(1)/f(X) (the variable subterm is dropped, the g(_)
    # skeleton kept).  f(g(1)) = 2 + 3 = 5, f(g(7)) = 3.
    p = Program('f(g(1)) += 2. f(g(X)) += 3. o1 += f(g(1)). o7 += f(g(7)). outputs: o1; o7.')
    q = ValueSplit(p)
    assert q._splits                                # it actually split (not refused)
    same(p, q, ['o1', 'o7'])
    # deeper still: a list cons cell
    pl = Program('f([a|Xs]) += w(Xs). f([Y|Xs]) += 1. o += f([a|nil]). ob += f([b|nil]).'
                 ' inputs: w(Xs). outputs: o; ob.')
    same(pl, ValueSplit(pl), ['o', 'ob'], D='w(nil) += 5.')


# --------------------------------------------------------------- end-to-end

def test_normalizer_value_split_then_project():
    p = Program('f(1) += 2. f(X) += 3. goal += f(X). g(X) += 4*f(X). outputs: goal; g(X).')
    q = RangeRestrictionNormalizer(p)
    same(p, q, ['goal', 'g(1)', 'g(7)', 'f(1)', 'f(2)'])


def test_normalizer_sound_on_startpath3():
    src = 'path(I,I). path(I,K) += path(I,J)*edge(J,K). inputs: edge(I,J). outputs: path(I,K).'
    D = 'edge(a,b)+=1. edge(b,c)+=1.'
    p = Program(src)
    same(p, RangeRestrictionNormalizer(p), ['path(a,a)', 'path(a,c)', 'path(c,c)'], D=D)


# ----------------------------------------- quotient cancellation (slash/LCT)
# The sound replacement for what abbreviate's `$free` did on slash items: drop a
# position only where it is shared between the numerator and denominator of a `/`
# quotient (it cancels under the division), never on a plain diagonal.

def test_reachable_patterns_derive_slash_sharing():
    # the derivation re-derives the shared span that is NOT syntactic in the
    # slashed rules (`p(X,I,K)/p(X0,I0,K0)` -> `p(X,I',K')/p(X',I',K')`).
    sl = Program(CKY).slash("p(X',I',K')", {1: 1}).prune()
    slashes = [h for h in reachable_patterns(sl) if getattr(h, 'fn', None) == '/']
    assert slashes, 'expected a derived `/` pattern'
    # numerator and denominator share their span variables in every derived pattern
    for h in slashes:
        num, den = h.args
        assert num.args[1:] == den.args[1:]      # spans shared; only the label differs


def test_quotient_cancelling_paths_slash_vs_diagonal():
    sl = Program(CKY).slash("p(X',I',K')", {1: 1}).prune()
    cancel = set().union(*quotient_cancelling_paths(sl).values())
    assert cancel == {(0, 1), (0, 2), (1, 1), (1, 2)}    # the shared span, num & den
    # a plain diagonal is not a quotient: nothing cancels (the startpath3 trap)
    sp = Program('path(I,I). path(I,K) += path(I,J)*edge(J,K). inputs: edge(I,J). outputs: path(I,K).')
    assert quotient_cancelling_paths(sp) == {}


def test_quotient_projection_reduces_and_preserves_value():
    sl = Program(CKY).slash("p(X',I',K')", {1: 1}).prune()
    # exact reduced shape: the 6-place `p/p` item collapses to the 2-place
    # `slash1(label, label)` -- the spans cancelled under the division.  The open
    # `slash1(X,X)` identity base is the (sound) residue.
    gen_functor.reset()
    QuotientProjection(sl).assert_equal("""
    slash1(X,X).
    slash1(X,X') += rewrite(X,Y) * slash1(Y,X').
    $other(p(X,I,K)) += rewrite(X,Y,Z) * p(Y,I,J) * p(Z,J,K).
    $other(p(X,I,K)) += rewrite(X,Y) * word(Y,I,K).
    goal += length(N) * p("ROOT",0,N).
    p(A,I,K) += $other(p(B,I,K)) * slash1(A,B).
    """)
    qp = QuotientProjection(sl)
    assert is_range_restricted(qp.engine_layer)
    (qp + Program(CKY_DATA)).sol().assert_equal_query('goal', 2.064)
    same(sl, qp, ['goal'], D=CKY_DATA)


def test_quotient_projection_noop_without_quotient():
    # no `/` items -> QuotientProjection is the identity (the diagonal is left alone)
    sp = Program('path(I,I). path(I,K) += path(I,J)*edge(J,K). inputs: edge(I,J). outputs: path(I,K).')
    qp = QuotientProjection(sp)
    qp.assert_equal(sp)
    same(sp, qp, ['path(a,a)', 'path(a,c)', 'path(c,c)'], D='edge(a,b)+=1. edge(b,c)+=1.')


def test_normalizer_subsumes_slash_optimization():
    # end-to-end through the entry point: the slash degree optimization is
    # recovered soundly by `normalize_range_restriction` (no `$free`).
    sl = Program(CKY).slash("p(X',I',K')", {1: 1}).prune()
    q = sl.normalize_range_restriction()
    (q.prune() + Program(CKY_DATA)).sol().assert_equal_query('goal', 2.064)


def test_quotient_binary_slash_derived_sharing():
    # binary slash: the cancelling position is the span-*start*, which is NOT
    # shared in the raw rules (`c(A,I,K)/c(B',I',J')`) -- the derivation recovers
    # the sharing.  `goal/c`, `rewrite/c` are different shapes and not reduced.
    cky = Program("""
    goal += c(s,0,N) * len(N).
    c(A,I,K) += rewrite(A,B) * word(B,I,K).
    c(A,I,K) += rewrite(A, B, C) * c(B,I,J) * c(C,J,K).
    """, 'rewrite(_,_,_). word(_,_,_). len(_).', 'goal.')
    itype = Program("""
    word(X,I,K) :- w(X), n(I), n(K).
    rewrite(X,Y,Z) :- k(X), k(Y), k(Z).
    rewrite(X,Y) :- k(X), k(Y).
    len(I) :- n(I).
    """, 'k(_). n(_). w(_).', '')
    sl = cky.slash("c(B',I',J')", positions={2: 1})
    cancel = quotient_cancelling_paths(sl, itype)
    assert len(cancel) == 1                              # only the `c/c` shape reduces
    assert set().union(*cancel.values()) == {(0, 1), (1, 1)}   # the shared span-start


# ------------------------------------------ soundness regressions (Codex review)

def test_value_split_keeps_body_variable_connected():
    # the gen-rule default must share variables between head and body (one fresh
    # copy, not two): f_dft(Y) must read g(Y), not g(<other>).
    p = Program('f(1,Y) += 5. f(X,Y) += 3 * g(Y). out(A,B) += f(A,B). inputs: g(Y). outputs: out(A,B).')
    same(p, ValueSplit(p), ['out(a,a)', 'out(a,c)', 'out(c,a)'], D='g(a) += 1. g(c) += 1.')


def test_quotient_refuses_when_value_depends_on_cancelled_var():
    # (p(X)/p(X)) += g(X): X is shared num/den but also drives g, so the quotient
    # value depends on X -- cancelling it is unsound and must be refused.
    p = Program('(p(X)/p(X)) += g(X). out(X) += (p(X)/p(X)). inputs: g(X). outputs: out(X).')
    assert quotient_cancelling_paths(p) == {}
    same(p, QuotientProjection(p), ['out(a)', 'out(b)'], D='g(a) += 2. g(b) += 3.')


def test_quotient_distinct_skeletons_get_distinct_names():
    # two independent span-sharing closures (a/a and b/b) must not collapse into
    # one `slash` relation.
    p = Program("""
    (a(X,I,K)/a(X0,I,K)) += ra(X,Y) * a(Y,I,K)/a(X0,I,K).
    (a(X0,I,K)/a(X0,I,K)).
    a(X,I,K) += othera(X,I,K) * a(X,I,K)/a(X0,I,K).
    othera(X,I,K) += worda(X,I,K).
    (b(X,I,K)/b(X0,I,K)) += rb(X,Y) * b(Y,I,K)/b(X0,I,K).
    (b(X0,I,K)/b(X0,I,K)).
    b(X,I,K) += otherb(X,I,K) * b(X,I,K)/b(X0,I,K).
    otherb(X,I,K) += wordb(X,I,K).
    goal += a("s",0,N) * b("s",0,N) * length(N).
    inputs: ra(X,Y); rb(X,Y); worda(X,I,K); wordb(X,I,K); length(N).
    outputs: goal.
    """)
    assert len(quotient_cancelling_paths(p)) == 2
    # a/a -> slash1, b/b -> slash2: distinct functors, the closures never merge
    gen_functor.reset()
    QuotientProjection(p).assert_equal("""
    slash1(X,X0) += ra(X,Y) * slash1(Y,X0).
    slash1(X0,X0).
    slash2(X,X0) += rb(X,Y) * slash2(Y,X0).
    slash2(X0,X0).
    a(X,I,K) += othera(X,I,K) * slash1(X,X0).
    b(X,I,K) += otherb(X,I,K) * slash2(X,X0).
    othera(X,I,K) += worda(X,I,K).
    otherb(X,I,K) += wordb(X,I,K).
    goal += a("s",0,N) * b("s",0,N) * length(N).
    """)


def test_projection_names_disambiguate_by_arity():
    # f/1 and f/2 are different predicates: PhantomProjection must not merge them
    # into one `f_p` (the fresh name includes the arity).
    p = Program('f(X) += 2. f(X,Y) += 3. out1 += f("a"). out2 += f("b","c"). outputs: out1; out2.')
    same(p, PhantomProjection(p), ['out1', 'out2'])
    # likewise for the value-split's f_dft / f_spc
    q = Program('f(1) += 2. f(X) += 9. f(1,Z) += 3. f(X,Z) += 9.'
                ' o1 += f(1). o2 += f(1,5). outputs: o1; o2.')
    same(q, ValueSplit(q), ['o1', 'o2'])


def test_quotient_projection_compensates_summed_multiplicity():
    # `goal += (p(X)/p(X))` sums X over an open quotient -> goal = inf; the
    # projection must keep that multiplicity (the `inf` factor), not collapse to 1.
    p = Program("(p(X)/p(X)). goal += (p(X)/p(X)). outputs: goal.")
    qp = QuotientProjection(p)
    qp.sol().assert_equal_query('goal', float('inf'))
    same(p, qp, ['goal'])


def test_normalizer_is_strictly_semantics_preserving():
    # The normalizer never restricts witnesses to an active domain (that would
    # change answers under Dyna's open universe).  A summed-away open variable
    # keeps its `inf` witness count.
    p = Program("(p(X)/p(X)). goal += (p(X)/p(X)). outputs: goal.")
    q = p.normalize_range_restriction()
    q.sol().assert_equal_query('goal', float('inf'))    # inf preserved, not |adom|
    same(p, q, ['goal'])                                # open-domain answers unchanged

    # an irreducibly open rule (the phantom recovery `x(I) += x_p`) stays residual
    g = Program('x(I) += 1. x(I) += 0.5 * x(I). outputs: x(_).')
    gn = g.normalize_range_restriction()
    same(g, gn, ['x(j)', 'x(k)'])
    assert len(gn.residual_layer.rules) > 0
    assert not is_range_restricted(gn.residual_layer)

    # `normalize_range_restriction` advertises no `adom` (or any) argument
    import inspect
    assert list(inspect.signature(Program.normalize_range_restriction).parameters) == ['self']


def test_quotient_output_is_not_projected():
    # a quotient that is itself a declared output has no recovery, so it must be
    # left intact (queryable), not projected away.
    p = Program("""
    (p(X,I,K)/p(X0,I,K)) += r(X,Y) * p(Y,I,K)/p(X0,I,K).
    (p(X0,I,K)/p(X0,I,K)).
    inputs: r(X,Y).
    outputs: p(X,I,K)/p(X0,I,K).
    """)
    assert quotient_cancelling_paths(p) == {}            # output quotient -> skipped
    qp = QuotientProjection(p)
    same(p, qp, ['p(s,0,1)/p(s,0,1)'], D='r(s,t) += 1.')


def test_is_is_forward_only_not_bidirectional():
    # `X is Y*Z` binds X from Y,Z (forward) but cannot invert to bind Y,Z; a head
    # var reachable only by inverting `is` is NOT range-restricted.
    p = Program('f(Y,Z) += g(X) * (X is Y * Z). inputs: g(X). outputs: f(Y,Z).')
    [r] = p.rules
    assert not is_rule_range_restricted(p, r)
    # forward still works: Y bound from g, X is Y+1 binds X
    q = Program('h(X) += g(Y) * (X is Y + 1). inputs: g(Y). outputs: h(X).')
    [r2] = q.rules
    assert is_rule_range_restricted(q, r2)


if __name__ == '__main__':
    from arsenal import testing_framework
    testing_framework(globals())
