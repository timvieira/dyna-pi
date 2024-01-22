"""
Derivations
"""

import re
from arsenal import colors, iterview
from collections import defaultdict
from IPython.display import HTML
from io import StringIO

from dyna.term import covers, fresh, Product, unify
from dyna.util import escape_str, escape_html, dot2svg, tikz, latex
from dyna.rule import Rule, is_const
from dyna import PrettyPrinter


class Derivation(Rule):
    "Our representation of a derivation extends Rule; it adds some bookkeeping information"

    def __init__(self, D, p, I):

        self.p = p
        self.i = I
        self.R = p.rules[I] if I is not None else None
        # instantiation of the top rule of this derivation
        self.r = Rule(D.head, *[y.head if isinstance(y, Derivation) else y for y in D.body])

        #assert (not isinstance(D.head, (Rule, Derivation))
        #        and all(isinstance(y, Derivation) or is_const(y) for y in D.body)), D
        #assert I is None or p[I].same(R), D.head

        if I is None or covers(self.R, self.r):         # I is None happens with builtins
            super().__init__(D.head, *D.body)
        else:
            super().__init__(D.head, *reorder_subgoals(D, self.r, self.R))

    def __add__(self, other):
        return Derivations([self]) + other

    def base(d):
        "Is this derivation a base case?"
        assert not isinstance(d, (Product, list, tuple))
        return not isinstance(d, Rule) or Program.is_builtin(d.head)

    def value(d):
        """
        Compute the value of a derivation. The value of a proof is the product of its
        leaves, which are all semiring values.
        """
        # A proof is either
        #    a constant (leaf).
        # or a `Rule` consistiting of derivations in its body.
        # Thus, a proof is a tree with constants at its leaves.
        if isinstance(d, (tuple, Product)):
            if len(d) == 0:
                return Product()
            else:
                return Derivation.value(d[0]) * Derivation.value(d[1:])
        elif is_const(d):
            return d
        else:
            return Derivation.value(d.body)

    def size(d):
        if isinstance(d, tuple): return sum(Derivation.size(y) for y in d)
        if Derivation.base(d): return 0
        return 1 + Derivation.size(d.body)

    def height(d):
        if isinstance(d, tuple): return max(Derivation.height(y) for y in d) if d else 0
        if Derivation.base(d): return 0
        return 1 + Derivation.height(d.body)

    def is_subtree(d, x):
        if d == x: return True
        if Derivation.base(d): return False
        return any(Derivation.is_subtree(y, x) for y in d.body)

#    def n_labels(d):
#        return len(set(Derivation.labels(d)))

#    def labels(d):
#        if isinstance(d, Product):
#            for y in d:
#                yield from Derivation.labels(y)
#        elif isinstance(d, Derivation):
#            yield d.head
#            yield from Derivation.labels(d.body)
#        else:
#            assert is_const(d)
#            yield d

    def dimension(d):
        # XXX: warning the dimension of a product/tuple is not associative!
        if isinstance(d, tuple):
            ds = list(reversed(sorted([Derivation.dimension(y) for y in d])))
            if len(ds) == 0:     return 0
            elif len(ds) == 1:   return ds[0]
            elif ds[0] == ds[1]: return 1 + ds[0]   # tie
            else:                return ds[0]       # no tie
        return 0 if Derivation.base(d) else Derivation.dimension(d.body)

    def fresh(self, m):
        return Derivation(m(Rule(self.head, *self.body)), self.p, self.i)

    def sub(self, subst):
        raise NotImplementedError()

    def _repr_html_(self):
        #return self.render_tikz()
        return self.to_forest()._repr_svg_()
        #return self.draw_svgling()._repr_svg_()

    def render_tikz(self):
        return self.to_tikz().to_svg()

    def pp_proof(self, show_values=False):
        "Pretty printing for this derivation."

        def f(d):
            if is_const(d): return [f'{d}']
            assert isinstance(d, Rule), d
            fs = [f(g) for g in d.body]
            return [f'{d.head}'] + colors.branch([x for x in fs if x])

        return '\n'.join(f(self))

    def to_tikz(self):

        def f(d):
            if Derivation.base(d): return r'{\color{magenta}%s}' % tikz.escape(d)
            body = " ".join(f(b) for b in d.body)
            return f'[.{{{tikz.escape(d.head)}}} {body} ]'

        return tikz(rf'\Tree {f(self)};')

    def to_forest(self, *args, **kwargs):
        return Derivations([self]).to_forest(*args, **kwargs)

    def to_dot(self):

        def node(x):
            node.id += 1
            # draw item the first time we see it
            b = str(x if Derivation.base(x) else x.head)
            s = re.sub(r'\033\[.*?m(.*?)\033\[0m', lambda m: '%s' % m.group(1), b)
            s = escape_str(escape_html(s))
            f.write(f'"{node.id}" [label="{s}"];\n')
            return node.id

        def edge():
            # draw the hyper edge
            edge.id += 1
            c = f'e{edge.id}'
            #f.write(f'"{c}" [label="", shape=point, fillcolor=black, style=filled];\n')
            f.write(f'"{c}" [shape=circle,label="",height=.05,width=.05,margin="0.0,0.0"];')
            return c

        node.id = 0
        edge.id = 0

        def traverse(d):
            h = node(d)
            if Derivation.base(d): return h
            c = edge()
            if 0:  # root at the top
                # connect the crux of the hyperedge to the head
                f.write(f'"{h}" -> "{c}" [dir=none];\n')
                # connect each node in the body to the crux of the hyperedge
                for y in d.body:
                    f.write(f'"{c}" -> "{traverse(y)}";\n')
            else:  # root at the bottom
                # connect the crux of the hyperedge to the head
                f.write(f'"{c}" -> "{h}";\n')
                # connect each node in the body to the crux of the hyperedge
                for y in d.body:
                    f.write(f'"{traverse(y)}" -> "{c}" [dir=none];\n')
            return h

        f = StringIO()
        f.write('digraph tmp {')
        #f.write('  node [fontname=Monospace,fontsize=10,shape=box,style=rounded,height=0,width=0,margin="0.055,0.042"];')
        f.write('  node [fontname=Monospace,fontsize=10,shape=none,height=0,width=0,margin="0.055,0.042"];\n')  # shape=box,style=rounded
        f.write('  edge [arrowhead=vee,arrowsize=0.5,fontname=Monospace,fontsize=9];')
        traverse(self)
        f.write('}')
        return f.getvalue()

    def draw_svgling(self):
        from svgling import draw_tree
        pp = PrettyPrinter()
        def f(d):
            if not isinstance(d, Derivation): return pp(d)
            return [pp(d.head), *map(f, d.body)]
        return draw_tree(f(self))


#_______________________________________________________________________________
# Rendering Derivation(s)

class Derivations(list):

    def __add__(self, other):
        if not isinstance(other, (list, Derivations)): other = [other]
        return Derivations(list(self) + list(other))

    def __getitem__(self, x):
        if isinstance(x, list):
            return Derivations([list.__getitem__(self, y) for y in x])
        else:
            return list.__getitem__(self, x)

#    def packed_forest(self):
#        "Inspect subderivation topology; graph is never cyclic because nodes are uniquified"
#        from arsenal import Integerizer
#        from dyna.util import Hypergraph
#        g = Hypergraph()
#        ix = Integerizer()
#        for d in self:
#            g.add_edge((d.head, ix(d)),
#                       d.r,
#                       *[(x.head if isinstance(x, Derivation) else x,
#                          ix(x))
#                         for x in d.body])
#        return g

#    def grouped_by_value(self):
#        g = defaultdict(Derivations)
#        for d in self:
#            g[d.value()].append(d)
#        return g

    def sort(self, key=Derivation.height):
        return Derivations(sorted(self, key=key))

#    def Transform(self, source, target):
#        return Derivations([source.Transform(d, target) for d in self])

    def _repr_html_(self):
#        return self.render_tikz().data
        return '\n'.join(
            d.to_forest().to_svg()
            for d in iterview(self, transient=True)
        )

    def render_tikz(self):
        out = ''
        for d in iterview(self, transient=True):
            out += d.to_tikz().to_svg()
        return HTML(out)

    def render_terminal(self):
        for d in self:
            print(d.pp_proof())

    def render_graphviz(self, **kwargs):
        return HTML('\n'.join(
            dot2svg(d.to_dot(), **kwargs)
            for d in iterview(self, transient=True)
        ))

    def to_forest(self, label_fn=lambda x: latex.escape(str(x)), preamble=''):
        "render `Derivation`s with LaTeX's `forest` package."

        def f(d):
            if Derivation.base(d): return r'[{\color{magenta}%s}]' % (label_fn(d),)
            body = " ".join(f(b) for b in d.body)
            return f'[{{{label_fn(d.head)}}} {body}]'

        fs = '\n'.join(f(d) for d in self)

        return latex(r"""
\documentclass[tikz]{standalone}
\usepackage{forest}
%s
\begin{document}
\begin{forest}{for tree={font=\tt, l=0cm, l sep-=.25em}}
[,phantom
%s
]
\end{forest}
\end{document}
""" % (preamble, fs))


#_______________________________________________________________________________
# Derivation enumeration


def naive(p, T=None):
    "Naive bottom-up enumeration of derivations."
    x = Program(semiring=p.semiring)
    t = 0
    while True:
        t += 1
        if T is not None and t > T: break
        x1 = step_derivations(p, x)
        if len(x1) == len(x): break   # no new derivations found
        x = x1
    return x


def step_derivations(p, chart):
    "Extend derivations in `chart` by rules in this program."

    rs = []
    def add(x, *ys): rs.append(fresh(Rule(x, *ys)))

    for i, _r in enumerate(p):
        r = fresh(_r)
        for ds in chart.join(*r.body):

            # TODO: include builtins in the other derivation enumeration
            # methods!  I think the nicest way to do it would be to unify the
            # chart representations.  The reason it doens't happen automatically
            # is because we didn't apply the "peel" trick to builtins; we only
            # did it for ordinary program items.
            ds = list(ds)
            for j,b in enumerate(ds):
                if p.is_builtin(r.body[j]):
                    ds[j] = Derivation(Rule(r.body[j], b), p=None, I=None)

            add(r.head, Derivation(Rule(r.head, *ds), p=p, I=i))

    return Program(rs, inputs=chart.inputs, outputs=p.outputs, semiring=p.semiring)


def seminaive(p, T=None, verbose=False):
    "semi-naive bottom-up evaluation; equivalent to fc but <= work per iteration."
    t = 0
    m = Program(semiring=p.semiring)
    d = step_derivations(p, Program(semiring=p.semiring))   # initialize with height 1 derivations
    while True:
        t += 1
        if T is not None and t > T: break
        if verbose: print(colors.light.yellow % f'iter {t}:', f'change {d}')
        [m, d] = seminaive_update(p, m, d)
        if len(d) == 0: return m
    return m


def seminaive_update(p, old, d):
    "derive the valuation for derivations of the next height."

    rs = []
    def add(x, *ys): rs.append(fresh(Rule(x, *ys)))

    new = (old + d)

    d.has_builtins = False

    for i, _r in enumerate(p):
        r = fresh(_r)
        for k in range(len(r.body)):
            # better to have an outer loop over change to improve the number of "prefix firings"
            for vk in d[r.body[k]]:
                for left in new.join(*r.body[:k]):
                    for right in old.join(*r.body[k+1:]):
                        add(r.head, Derivation(Rule(r.head, *left, *vk, *right), p=p, I=i))

    return new, Program(rs, semiring=p.semiring, has_builtins=False)


def agenda(p):
    "Agenda-based bottom-up proof enumeration."

    old = Program(semiring=p.Semiring)
    change = list(step_derivations(p, old))

    new = Program(semiring=p.Semiring)

    while len(change) > 0:

        # pick an arbitrary rule from the change buffer
        # XXX: use a better default policy!
        #i = int(np.random.randint(len(change)))
        [driver, value] = change.pop(0)

        yield value

        new.update(driver, value)

        for i, r in enumerate(p):
            for k in range(len(r.body)):
                for _ in unify(driver, r.body[k]):

                    for left in new.join(*r.body[:k]):
                        for right in old.join(*r.body[k+1:]):
                            d = Derivation(Rule(r.head, *left, value, *right), p=p, I=i)
                            change.append(fresh(Rule(r.head, d)))

        old.update(driver, value)


def peel(ds):
    "Utility that removes the head of a list of derivation `ds`."
    dds = []
    for d in ds:
        [d] = d.body
        dds.append(d)
    return dds


def Naive(p, T, x):
    return Derivations(peel(naive(p, T=T).user_lookup(x)))


def Seminaive(p, T, x, verbose=False):
    return Derivations(peel(seminaive(p, T=T, verbose=verbose).user_lookup(x)))


def sld(p, x):
    """
    Top-down enumeration of derivations of the item `x` in program `p`.

    [Uses SLD resolution; beware of infinite left recursion.]  This function is
    essentially backward chaining no memoization.
    """
    if isinstance(x, (Product, tuple)):
        if len(x) == 0:
            yield Product()
        else:
            for d1 in sld(p, x[0]):
                for d2 in sld(p, x[1:]):
                    yield d1 * d2
        return
    if p.is_const(x):
        yield x
        return
    # TODO: check that lookup didn't just delay an immature builtin?  The
    # current behavior is to left recurse forever (the builtin rewrites as
    # itself and recurse on it; then, we repeat).
    for r in p.lookup(x):
        for ds in sld(p, r.body):
            yield Derivation(Rule(r.head, *ds), p=p, I=r.i)



def reorder_subgoals(D, r, R):
    """
    Reorder derivation `D`'s subgoals to match their original order in `R`; (`r` is
    `D`'s instantiated top rule)
    """

    possible = r.folds_by(R)
    if not possible:    # pragma: no cover
        msg = (f"""
        failed to re-order subgoal order:
        want: {R}
        have: {r}
        """)

        if Derivation.SAFE:
            raise AssertionError(msg)
        else:
            return D.body

    [t] = possible

    assert not t.remaining, [R, r, t]  # we shouldn't have any more fuzzy matches
    # permute subgoals to match the rule
    bs = [D.body[j] for i,j in sorted(t.align.items())]
    # check that the permutation did the trick
    if not covers(R, Rule(r.head, *[r.body[j] for i,j in sorted(t.align.items())])):  # pragma: no cover
        if Derivation.SAFE:
            raise AssertionError(f"""
            failed to re-order subgoals:
            want: {R}
            have: {r}
            ====> {Rule(r.head, *[r.body[j] for i,j in sorted(t.align.items())])}
            """)
    return bs


#from contextlib import contextmanager
#@contextmanager
#def unsafe_ctx():
#    was = Derivation.SAFE
#    Derivation.SAFE = False
#    yield
#    Derivation.SAFE = was


#Derivation.SAFE = False
Derivation.SAFE = True
#Derivation.unsafe_ctx = unsafe_ctx
#Derivation.BUILTINS = False
Derivation.BUILTINS = True

from dyna.program import Program
