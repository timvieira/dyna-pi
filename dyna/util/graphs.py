import re
import numpy as np
import pylab as pl

from arsenal import colors, Integerizer
from collections import defaultdict, deque, namedtuple
from io import StringIO
from functools import cached_property

from dyna.util import escape_str, graphviz, remove_ansi


#class LabeledGraph:
#
#    def __init__(self):
#        self.edges = defaultdict(lambda:defaultdict(dict))
#        self.nodes = Integerizer()
#
#    def unlabeled_arcs(self, i):
#        for _, j in self.edges[self.nodes(i)].items():
#            yield self.nodes[j]
#
#    def edge(self, i, a, j):
#        self.edges[self.nodes(i)][a] = self.nodes(j)
#
#    # TODO: stick with add_edge
#    add_edge = edge
#
##    def nx(self):
##        g = nx.DiGraph()
##        for i in self.edges:
##            for a in self.edges[i]:
##                j = self.edges[i][a]
##                g.add_node(i)
##                g.add_node(j)
##                g.add_edge(i, j, label=a)
##        return g
#
#    def _repr_svg_(self):
##        return self.graphviz()._repr_svg_()
#        return self.graphviz()._repr_image_svg_xml()
#
#    def graphviz(self, graph_attrs=None):
#        from graphviz import Digraph
#        if graph_attrs is None: graph_attrs = {}
#
#        g = Digraph(
#            node_attr=dict(
#                shape='record',
#                fontname='Monospace', fontsize='10',
#                height='0', width='0',
#                margin="0.055,0.042",
#            ),
#            edge_attr=dict(
#                arrowhead='vee', arrowsize='0.5', fontname='Monospace', fontsize='9'
#            ),
#        )
#        g.graph_attr.update(**graph_attrs)
#
#        for i in self.edges:
#            for a in self.edges[i]:
#                j = self.edges[i][a]
#                g.edge(str(i), str(j), label=str(a) if a is not None else None)
#
#        def escape(x):
#            if isinstance(x, frozenset): x = set(x) or {}
#            x = str(x)
#            x = remove_ansi(x, r'`\1`')
#            return x
#
#        for x, i in self.nodes.items():
#            g.node(str(i), label=escape(x))
#
#        return g


# TODO: should probably rename to LabeledHyperedge
Edge = namedtuple('Edge', 'weight, head, body')


class Hypergraph:

    def __init__(self):
        self.incoming = defaultdict(list)
        self.nodes = set()

    def __eq__(self, other):
        return self.nodes == other.nodes and self.incoming == other.incoming

    def __repr__(self):
        return f'{self.__class__.__name__}(nodes={len(self.nodes)})'

    def __str__(self):
        lines = ['{']
        for x in sorted(self.nodes):
            lines.append(f'  {x}:')
            for e in self.incoming[x]:
                lines.append(f'    {e.weight}: {e.body}')
        lines.append('}')
        return '\n'.join(lines)

    def edges(self):
        for h in self.incoming:
            yield from self.incoming[h]

#    def __iter__(self):
#        return iter(self.nodes)

#    def __getitem__(self, x):
#        return self.incoming[x]

    def add_edge(self, head, weight, *body):
        e = Edge(weight, head, body)
        self.incoming[head].append(e)
        self.nodes.add(head)
        for y in body: self.nodes.add(y)
        return e

#    def terminals(self):
#        terminals = set()
#        for e in self.edges():
#            for b in e.body:
#                if not self.incoming[b]:
#                    terminals.add(b)
#        return terminals

#    def toposort(self):
#        visited = set()
#
#        def t(v):
#            if v not in visited:
#                visited.add(v)
#                if self.incoming[v]:
#                    for e in self.incoming[v]:
#                        for u in e.body:
#                            yield from t(u)
#                    yield v
#
#        assert self.root is not None
#        return t(self.root)

    def reachability(self, inputs, outputs):
        C = set(inputs)
        C.update(e.head for e in self.edges() if not e.body)

        outgoing = defaultdict(list)
        for e in self.edges():
            for b in e.body:
                outgoing[b].append(e)

        agenda = set(C)
        while agenda:
            x = agenda.pop()
            for e in outgoing[x]:
                if all((b in C) for b in e.body):
                    if e.head not in C:
                        C.add(e.head)
                        agenda.add(e.head)

        T = set(outputs)
        agenda.update(T)
        while agenda:
            x = agenda.pop()
            for e in self.incoming[x]:
                if e.head in T:
                    for b in e.body:
                        if b not in T and b in C:
                            T.add(b)
                            agenda.add(b)

        return T

    def graphviz(self, **kwargs):

        def escape(x):
            if isinstance(x, frozenset): x = set(x) or {}
            return escape_str(str(x)).replace('$', r'\$')  # notebook seem to not like $ - probably mathjax

        f = StringIO()
        print('digraph {', file=f)
        f.write('  node [fontname=Monospace,fontsize=10,shape=none,height=0,width=0,margin="0.055,0.042"];\n')  # shape=box,style=rounded
        f.write('  edge [arrowhead=vee,arrowsize=0.5,fontname=Monospace,fontsize=9];\n')

        ix = Integerizer()
        for x in list(self.incoming):
            for e in self.incoming[x]:
                print(f'  "{ix(e)}" -> "{ix(e.head)}";', file=f)
                for b in e.body:
                    print(f'  "{ix(b)}" -> "{ix(e)}" [arrowhead=none];', file=f)

        for x, i in ix.items():
            if isinstance(x, Edge):
                print(f'  "{i}" [shape=circle,label="",height=.05,width=.05,margin="0.0,0.0"];', file=f)
            else:
                print(f'  "{i}" [label="{escape(x)}"];', file=f)
        print('}', file=f)

        return graphviz(f.getvalue(), **kwargs)

    def _repr_html_(self):
        "Visualize graphviz rendering in a Jupyter notebook."
        svg = self.graphviz().to_svg()
        # wrap the svg in a <pre> block to suppress MathJax.  The choice to
        # suppress MathJax comes having $ in output that mysteriously disappears
        return svg.replace('<svg ', '<pre style="margin:0; padding:0"><svg ') + '</pre>'


class Graph:
    "Very simple graph data structure."
    def __init__(self, edges=()):
        self.nodes = set()
        self.outgoing = defaultdict(set)
        for (u,v) in edges:
            self.add_edge(u,v)

    def __repr__(self):
        return f'<Graph nodes={len(self.nodes)} edges={len(list(self.edges))}>'

    def __iter__(self):
        return iter(self.nodes)

    def __getitem__(self, u):
        return self.outgoing[u]

    def __len__(self):
        return len(self.nodes)

    def add(self, u):
        self.nodes.add(u)

    def add_edge(self, u, v):
        self.nodes.add(u)
        self.nodes.add(v)
        self.outgoing[u].add(v)

    @property
    def edges(self):
        for x in self:
            for y in self[x]:
                yield (x,y)

    def condensation(self, roots=None):
        "Return the directed acyclic graph of strongly connected components."
        sccs = list(tarjan(self.__getitem__, roots if roots else self.nodes))
        s = {x: i for i, xs in enumerate(sccs) for x in xs}

        c = Graph()
        for x in self.nodes:
            if x not in s: continue
            X = sccs[s[x]]
            c.nodes.add(X)
            for y in self[x]:
                if y in X: continue     # drop self loops; x and y are in the same SCC
                if y not in s: continue
                Y = sccs[s[y]]
                c.add_edge(X, Y)

        c.s = s
        c.topo = sccs

        return c

    def _repr_svg_(self):
        return self.graphviz()._repr_image_svg_xml()

    def graphviz(self):
        from graphviz import Digraph

        name = Integerizer()

        g = Digraph(
            node_attr=dict(
                fontname='Monospace',
                fontsize='9',
                height='0', width='0',
                margin="0.055,0.042",
                penwidth='0.15',
                shape='box',
                style='rounded',
            ),
            edge_attr=dict(
                penwidth='0.5',
                arrowhead='vee',
                arrowsize='0.5',
                fontname='Monospace',
                fontsize='8'
            ),
        )

        for i in self:
            for j in self[i]:
                g.edge(str(name(i)), str(name(j)))

        def escape(x):
            if isinstance(x, frozenset): x = set(x) or {}
            if isinstance(x, float): x = f'{x:.2g}'
            x = str(x)
            x = remove_ansi(x)
            return x

        for x in self:
            g.node(str(name(x)), label=escape(x))

        return g

    def transitive_closure(self, reflexive=False):
        from dyna.execute.linear import kleene
        from semirings import Boolean

        ix = Integerizer()

        # transitive closure of SCC dependency graph gives ordering relation.
        K = len(self)
        E = np.zeros((K,K), dtype=object)
        for x in self: ix.add(x)
        for i in range(K):
            for j in range(K):
                E[i,j] = Boolean.zero

        for x in self:
            for y in self[x]:
                E[ix(x),ix(y)] = Boolean.one

        T = kleene(E, Boolean, reflexive=reflexive)

        g = Graph()
        for x in self: g.add(x)
        for i in range(K):
            for j in range(K):
                if T[i,j].score:
                    g.add_edge(ix[i], ix[j])

        return g

#    def reverse(self):
#        R = Graph()
#        for i,j in self.edges:
#            R.add_edge(j,i)
#        return R


# For an iterative version see:
# https://slashvar.github.io/2019/04/05/tail-recursive-functions.html
def tarjan(successors, roots):
    """
    Tarjan's linear-time algorithm O(E + V) for finding the maximal
    strongly connected components.
    """

    # 'Low Link Value' of a node is the smallest id reachable by DFS, including itself.
    # low link values are initialized to each node's id.
    lowest = {}      # node -> position of the root of the SCC

    stack = []      # stack
    trail = set()   # set of nodes on the stack
    t = 0

    def dfs(v):
        # DFS pushes nodes onto the stack
        nonlocal t
        t += 1
        num = t
        lowest[v] = t
        trail.add(v)
        stack.append(v)

        for w in successors(v):
            if lowest.get(w) is None:
                # As usual, only recurse when we haven't already visited this node
                yield from dfs(w)
                # The recursive call will find a cycle if there is one.
                # `lowest` is used to propagate the position of the earliest
                # node on the cycle in the DFS.
                lowest[v] = min(lowest[v], lowest[w])
            elif w in trail:
                # Collapsing cycles.  If `w` comes before `v` in dfs and `w` is
                # on the stack, then we've detected a cycle and we can start
                # collapsing values in the SCC.  It might not be the maximal
                # SCC. The min and stack will take care of that.
                lowest[v] = min(lowest[v], lowest[w])

        if lowest[v] == num:
            # `v` is the root of an SCC; We're totally done with that subgraph.
            # nodes above `v` on the stack are an SCC.
            C = []
            while True:   # pop until we reach v
                w = stack.pop()
                trail.remove(w)
                C.append(w)
                if w == v: break
            yield frozenset(C)

    for v in roots:
        if lowest.get(v) is None:
            yield from dfs(v)
