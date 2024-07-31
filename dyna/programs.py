"""
Program collections
"""

from arsenal import groupby2, iterview, colors, timelimit, Integerizer
from time import time
from itertools import product
from collections import defaultdict
from io import StringIO

from dyna import Hypergraph
from dyna.util import escape_str, graphviz, Edge, Hypergraph
from dyna.program import Program, TransformedProgram, Define, inf

import pandas


class ProgramCollection(list):

    @property
    def graph(self):
        return ProgramGraph(self)

    def _repr_html_(self):
        #other_columns = {
        #    'bigo': [p.prune().type_analysis().runtime().x._repr_latex_() for p in self]
        #}
        df = pandas.DataFrame({
            'program': self,
            'degree': [p.degree for p in self],
            #**other_columns,
        })
        return df.style.format({'program': Program._repr_html_})._repr_html_()

    def add(self, x):
        self.append(x)
        return x

    def eurekas(self):
        "Extend collection with every variable-elimination eureka definition"
        new = list(self)
        for p in self:
            for i, r in enumerate(p):
                a = r.analyzer
                Fs = {tuple(sorted(a.v2f[v])) for v in a.can_elim}
                for fs in Fs:
                    new.append(p.hook(i, fs))
        return ProgramCollection(new)

    def partial_megafolds(self, defs, **kwargs):
        return self + ProgramCollection([
            y for x in self
            for y in x.partial_megafolds(defs, **kwargs)
        ])

    def reversible_megafolds(self, *args, **kwargs):
        return self + ProgramCollection([
            y for x in self
            for y in x.reversible_megafolds(*args, **kwargs)
        ])

    def megafolds(self, defs):
        return self + ProgramCollection([
            y for x in self
            for y in x.megafolds(defs)
        ])

    def folds_seq(self, **kwargs):
        new = list(self)
        for p in self:
            new.extend(self._folds_seq(p, **kwargs))
        return ProgramCollection(new)

    @staticmethod
    def _folds_seq(p, **kwargs):
        # This version of the fold actions constrains the megafolds that we are
        # considering to just those that include some new definition and
        # constraint the fold to that definition (allow the initial program too,
        # of course)
        for defs in p.lineage():
            if isinstance(defs, Define):
                def_ix = list(defs._new_ix)
            elif not isinstance(defs, TransformedProgram):   # original program
                def_ix = list(range(len(defs)))
            else:
                def_ix = []
                continue
            if defs is p: defs = defs.fresh()
            for r in p.fold_proposals(defs = Program([defs.rules[i] for i in def_ix]), **kwargs):
                for q in p.folds_by(r=r, js=r.j, defs=defs):
                    yield q

    def unfolds_first(self, **kwargs):
        return self.unfolds_seq(first_only=True, **kwargs)

    def unfolds_seq(self, **kwargs):
        new = list(self)
        for p in self:
            new.extend(self._unfolds_seq(p, **kwargs))
        return ProgramCollection(new)

    @staticmethod
    def _unfolds_seq(p, first_only=False):
        for i, r in enumerate(p):
            for j, x in enumerate(r.body):
                if p.safe_inline(x):
                    for defs in reversed(list(p.lineage())):
                        if defs.is_item(x):
                            yield p.unfold(i, j, defs=defs)
                            if first_only: break

    def unfolds(self, *args, **kwargs):
        return self + ProgramCollection([
            y for x in self
            for y in x.unfolds(*args, **kwargs)
        ])

#    def folds_pairwise(self):
#        "Warning: safety not checked"
#        pairs = [(x,y) for x in self for y in self]
#        new = list(self)
#        for x, y in iterview(pairs, transient=True):
#            for z in x.partial_megafolds(y):
#                new.append(z)
#        return ProgramCollection(new)

#    def unfolds_pairwise(self):
#        "Warning: safety not checked"
#        pairs = [(x,y) for x in self for y in self]
#        new = list(self)
#        for x, y in iterview(pairs, transient=True):
#            for z in x.unfolds(y):
#                new.append(z)
#        return ProgramCollection(new)

    def __add__(self, other):
        return ProgramCollection(list.__add__(self, other))

    def __getitem__(self, key):
        if isinstance(key, list):
            # Return the subcollection at the specified indices
            return ProgramCollection([self[k] for k in key])
        elif isinstance(key, slice):
            # Return the subcollection at the specified indices
            return ProgramCollection(list(self).__getitem__(key))
        else:
            # return a program, not a singleton collection
            assert isinstance(key, int)
            return list.__getitem__(self, key)

    def groupby(self, key=lambda x: x):
        g = groupby2(self, key=key)
        return {k: ProgramCollection(ps) for k, ps in g.items()}

    def sort(self, key=None):
        return ProgramCollection(sorted(self, key=key))

    def max(self, key=None):
        return max(self, key=key)

    def min(self, key=None):
        return min(self, key=key)

    def filter(self, predicate):
        return ProgramCollection(filter(predicate, self))

    def dedup(self):
        return ProgramCollection(set(self))

    def min_degree(self):
        return self.min(Program.degrees)

    def sort_degree(self):
        return self.sort(Program.degrees)

    def prune(self, **kwargs):
        return self.map(Program.prune, **kwargs)

    def prune_fast(self, **kwargs):
        return self.map(Program.prune_fast, **kwargs)

    def map(self, f, progress=False, **kwargs):
        if progress: self = iterview(self, transient=True)
        return ProgramCollection([f(x, **kwargs) for x in self])

    def lct(self, **kwargs):
        return self._slashes(speculation=False)

    def slashes(self, **kwargs):
        return self._slashes(speculation=True)

    def _slashes(self, **kwargs):
        return ProgramCollection([q for p in self for q in self.__slashes(p, **kwargs)])

    def __slashes(self, p, speculation):
        # TODO: A proposal for proposing speculation actions: pick a *pair* of
        # "subtask", i.e., two sets of items a numerator and a denominator, then
        # consider all subsets/positions that connect the numerator set to the
        # denominator set.
        assert isinstance(p, Program)
        positions = []
        for r in p:
            positions.append([None] + list(range(len(r.body))))
        for pos in product(*positions):
            if speculation:
                yield p.slash('X', dict(enumerate(pos)))
            else:
                yield p.lct(dict(enumerate(pos)))

    def race(self, run, tmin, growth_factor=2):
        budget = tmin
        best_t = inf
        best_x = None
        best_y = None
        while best_t == inf:
            for x in iterview(self, transient=True, msg=colors.cyan % f'race({budget:g})'):
                try:
                    b4 = time()
                    with timelimit(budget):
                        y = run(x)
                    t = time() - b4
                except timelimit.Timeout:
                    pass
                else:
                    if t < best_t:
                        best_t = t
                        best_x = x
                        best_y = y
            budget *= growth_factor
        return (best_t, best_x, best_y)


class ProgramGraph:

    def __init__(self, nodes=()):
        self.graph = defaultdict(set)
        for x in nodes: self.add_parents(x)

    def tidy(self, correct_nodes):

        G = self.__class__()
        while True:
            changed = False
            for x in correct_nodes:
                for e in self.graph[x]:
                    [_, t, deps] = e
                    if all((y in G.graph) for y in deps):
                        if e not in G.graph[x]:
                            changed = True
                            G.add(t)
            if not changed: break

        return G

    def hg(self):
        h = Hypergraph()
        for x in self:
            for (label, _, body) in self.graph[x]:
                h.add_edge(x, label, *body)
        return h

    def __repr__(self):
        return f'<{self.__class__.__name__} {len(self.graph)} nodes, {sum(len(xs) for xs in self.graph.values())} hyperedges>'

    def __iter__(self):
        return iter(list(self.graph))

    def __getitem__(self, x):
        return self.graph[x]

    def add(self, x):
        from dyna import Fold, Unfold, TransformedProgram
        if isinstance(x, Fold):
            self.graph[x].add(('fold', x, (x.parent, x.defs)))
        elif isinstance(x, Unfold):
            self.graph[x].add(('unfold', x, (x.parent, x.defs)))
        elif isinstance(x, TransformedProgram) and x.name == 'fresh':
            return self.add(x.parent)
        elif isinstance(x, TransformedProgram):
#            self.graph[x].add((x.__class__.__name__, x, (x.parent,)))
            self.graph[x].add((x.name, x, (x.parent,)))
        else:
            self.graph[x].add(('ref', x, ()))
        return x

    def add_parents(self, x, stack=None):
        from dyna import Fold, Unfold
        if stack is None: stack = set()
        if id(x) in stack: return
        stack.add(id(x))
        if isinstance(x, (Unfold, Fold)):
            self.add(x)
            self.add_parents(x.parent, stack=stack)
            self.add_parents(x.defs, stack=stack)
        elif isinstance(x, TransformedProgram) and x.name == 'fresh':
            return self.add(x.parent)
        elif isinstance(x, TransformedProgram):
            self.add(x)
            self.add_parents(x.parent, stack=stack)
        else:
            self.add(x)

    def _repr_html_(self):
        svg = self.render(set(), set())._repr_html_()
        # wrap the svg in a <pre> block to suppress MathJax.  The choice to
        # suppress MathJax comes having $ in output that mysteriously disappears
        return svg.replace('<svg ', '<pre style="margin:0; padding:0;"><svg ') + '</pre>'

    def render(self, have_safe=None, want_safe=None, hypergraph=False):

        if have_safe is None: have_safe = set()
        if want_safe is None: want_safe = set()

        g = self.hg()

        def escape(x):
            x = x.sort().__repr__(color=False, numbered=False, sep='\n', indent='', open_brace=None, close_brace='')
            return escape_str(x)

        f = StringIO()
        print('digraph {', file=f)
        f.write('  node [fontname=Monospace,fontsize=10,textalign=left,shape=box,style=rounded,height=0,width=0,margin="0.055,0.042"];\n')
        f.write('  edge [arrowhead=vee,arrowsize=0.5,fontname=Monospace,fontsize=9];\n')

        ix = Integerizer()
        for x in list(g.incoming):
            for e in g.incoming[x]:
                if hypergraph:
                    print(f'  "{ix(e)}" -> "{ix(e.head)}";', file=f)
                    for b in set(e.body):   # dedups when defs = parent
                        print(f'  "{ix(b)}" -> "{ix(e)}" [arrowhead=none];', file=f)
                else:
                    if len(e.body) == 0:
                        # just take the first node on the edge; label the edge with transform name
                        print(f'  "{ix(e.head)}-ref" -> "{ix(e.head)}" [label="{e.weight}"];', file=f)
                        print(f'  "{ix(e.head)}-ref" [shape=box, label="init"];', file=f)
                    else:
                        # just take the first node on the edge; label the edge with transform name
                        print(f'  "{ix(e.body[0])}" -> "{ix(e.head)}" [label="{e.weight}"];', file=f)

        for x, i in ix.items():
            if isinstance(x, Edge):
                if hypergraph:
                    print(f'  "{i}" [shape=box, label="{x.weight}"];', file=f)
            else:
                if x in have_safe:
                    sty = ', fillcolor=green, style=filled'
                elif x in want_safe:
                    sty = ', fillcolor=yellow, style=filled'
                else:
                    sty = ''
                print(f'  "{i}" [label="{escape(x)}" {sty}];', file=f)
        print('}', file=f)

        return graphviz(f.getvalue())
