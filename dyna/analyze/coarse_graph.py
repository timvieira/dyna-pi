from itertools import product, combinations

from dyna import Program, term, unifies
from dyna.term import DisjointEstimate
from dyna.util import Hypergraph, Graph


class CoarseGraph:

    def __init__(self, p):
        self.program = p
        assert p.inputs is not None and p.outputs is not None

        "run thru the program to establish a coarse-grained vocabulary of nodes"
        nodes = DisjointEstimate()
        for x in p.inputs.just_heads():
            nodes.add(x)
        for x, *ys in p:
            nodes.add(x)
            for y in ys:
                if not (p.is_const(y) or p.is_builtin(y)):
                    nodes.add(y)
        self.nodes = nodes

        # coarse-grained hypergraph
        h = Hypergraph()
        for x in p.inputs.just_heads():
            h.add_edge(nodes.root(x), None)
        for i, r in enumerate(p):
            (x, *ys) = r
            yys = [nodes.roots(y) for y in ys if not (p.is_const(y) or p.is_builtin(y))]
            for xx in nodes.roots(x):
                for yy in product(*yys):
                    h.add_edge(xx, i, *yy)

        # coarse-grained dependency graph
        g = Graph()
        for x in p.inputs.just_heads():
            g.nodes.add(nodes.root(x))
        for (x, *ys) in p:
            g.nodes.add(nodes.root(x))
            for y in ys:
                if not (p.is_const(y) or p.is_builtin(y)):
                    g.add_edge(nodes.root(x), nodes.root(y))

        self.g = g
        self.h = h

    def split_input_dependent(self):
        """
        Split the program into input-independent and input-dependent subprogram.
        """

        g = self.g
        T = g.transitive_closure(reflexive=True)

        inputs = set(p.inputs.just_heads() if p.inputs is not None else [])

        I = []; D = []
        for r in p:
            x = self.nodes.root(r.head)
            if T.outgoing[x] & inputs:
                D.append(r)
            else:
                I.append(r)

        return p.spawn(I), p.spawn(D)

    # TODO: when the SCC is data-independent, we can solve it right away (i.e., add
    # the /solution/ rather than the rule)
    def solve_input_independent(self):
        I, D = self.split_input_dependent()
        return I.sol() + D

    # TODO: in the case of a type-based analysis, there may be rules that
    # participate in multiple SCCs (they need to be /specialized/ to the current SCC
    # to avoid double counting).  See dissertation for how it is supposed to work.
    def scc_decomposition(self):
        """
        Split the program into a sequence of strongly connected subprograms.
        """
        g = self.g
        C = g.condensation(roots=[x for x in g.nodes if p.is_output(x)])
        for i, xs in enumerate(C.topo):
            q = p.spawn()
            q.set_input_types(Program([Rule(y) for ys in C.outgoing[xs] for y in ys]))
            q.set_output_types(Program([Rule(x) for x in xs]))
            for r in p:
                for x in xs:
                    for _ in unify(x, r.head):
                        q.append(r)
            yield (xs, q)

    def possibly_cyclic(self):
        """
        Using coarse-graind analysis, determine if this program is possibly cyclic.
        """
        # Note: we want the transitive---but not reflexive---closure of the coarse
        # dependency graph
        T = self.g.transitive_closure(reflexive=False)
        return any(i in T.outgoing[i] for i in T.nodes)

    def possibly_expansive(self):
        """
        Using coarse-graind analysis, determine if this program is expansive (i.e.,
        is there an item that can transitively expand into two copies of
        itself).  Non-expansive programs can be solved in finite time with
        Newton's method.
        """
        g = self.g
        T = g.transitive_closure(reflexive=True)
        for r in p:
            x = self.nodes.root(r.head)
            count = 0
            for y in r.body:   # can we reach x in more than one way?
                if p.is_const(y): continue
                y = self.nodes.root(y)
                count += (x in T.outgoing[y])
                if count > 1: return True
        return False


def assert_disjoint(xs):
    for x,y in combinations(xs, 2):
        assert not unifies(x, y), [x,y]


def test_coarsen():
    p = Program("""
    f(3,Y).
    f(X,4).

    g(X).

    h(3).
    h(4).

    p(X1,"cat").
    p(X2,"dog").

    q([X1,"cat"|Xs]).
    q([X2,"dog"|Ys]).
    q([X|Xs]).

    outputs: X.
    """)

    nodes = p._coarse_graph().nodes
    print(nodes)

    # The nodes must be disjoint!
    assert_disjoint(nodes)

    nodes.to_program().assert_equal("""
    f(X,Y).
    g(X).
    h(3).
    h(4).
    p(X1,"cat").
    p(X2,"dog").
    q([X|Xs]).
    """)


def test_coarse_hypergraph():
    from dyna import canonicalize
    from dyna.util import Hypergraph

    p = Program("""
    goal += h(I,I).
    h(I,K) += f(I,J) * g(J,K).

    inputs: f(_,_); g(_,_).
    """)

    g = p.coarse_hypergraph()
    print(g)

    n = lambda x: canonicalize(term(x))

    gg = Hypergraph()
    gg.add_edge(n('f(_,_)'), None)
    gg.add_edge(n('g(_,_)'), None)
    gg.add_edge(n('goal'), 0, n('h(_,_)'))
    gg.add_edge(n('h(_,_)'), 1, n('f(_,_)'), n('g(_,_)'))

    assert gg.nodes == g.nodes
    print(gg)
    assert g == gg


if __name__ == '__main__':
    from arsenal import testing_framework
    testing_framework(globals())
