import re
from arsenal import assert_throws

from dyna import Program
from dyna.util import Graph, latex, run_cmd, render_groundings


def test_scc():

    G = Graph([
        ('a','b'),
        ('b','c'),
        ('c','a'),
        ('c','d'),
        ('d','d'),
        ('d','e'),
        ('e','f'),
    ])

    scc = G.condensation()
    assert scc.topo == [{'f'}, {'e'}, {'d'}, {'c','b','a'}]

    assert set(G.transitive_closure().edges) == {
        ('d', 'd'), ('d', 'e'), ('d', 'f'), ('b', 'd'), ('b', 'b'),
        ('b', 'f'), ('b', 'e'), ('b', 'a'), ('b', 'c'), ('e', 'f'),
        ('a', 'd'), ('a', 'b'), ('a', 'f'), ('a', 'e'), ('a', 'a'),
        ('a', 'c'), ('c', 'd'), ('c', 'b'), ('c', 'f'), ('c', 'e'),
        ('c', 'a'), ('c', 'c'),
    }

    G2 = Graph([(1,2), (3,1), (3,6), (6,7), (7,6), (2,3), (4,2),
                (4,3), (4,5), (5,6), (5,4), (8,5), (8,7), (8,6)])

    C2 = G2.condensation()
    assert C2.topo == [{6, 7}, {1, 2, 3}, {4, 5}, {8}]

    G3 = Graph([('A', 'B'), ('B', 'C'), ('C', 'A'), ('A', 'Other')])
    C2 = G3.condensation()
    assert C2.topo == [{'Other'}, {'A', 'B', 'C'}]


def test_latex():

    x = latex(r"""
    \documentclass{article}
    \begin{document}
    Hello, World.
    \end{document}
    """)
    x.to_svg()

    with assert_throws(Exception):
        run_cmd(['non-existent-executable', '--help'])


#def test_tikz():
#    tikz(r'\Tree [.a b c ]', force=1).to_svg()
#    tikz(r'\Tree [.a b c ]', force=1).to_png()


def test_tikz_derivations():

    p = Program("""

    a += b * c.

    b += 1.
    c += 1.

    """)

    ds = p.derivations(T=10, x='a')
    print(ds)

    assert ds.to_forest().code.strip() == r"""
\documentclass[tikz]{standalone}
\usepackage{forest}

\begin{document}
\begin{forest}{for tree={font=\tt, l=0cm, l sep-=.25em}}
[,phantom
[{a} [{b} [{\color{magenta}1}]] [{c} [{\color{magenta}1}]]]
]
\end{forest}
\end{document}
""".strip()

    ds.render_graphviz(force=True)
    ds.render_graphviz(force=False)
    ds.render_graphviz(force=False)   # call twice so that caching kicks in

    ds.render_graphviz()._repr_html_()


def test_program_graphs():

    p = Program("""

    a += b * c.

    b += 1.
    c += 1.

    outputs: X.

    """)

    h = p.coarse_hypergraph()
    assert len(list(h.edges())) == 3

    h.graphviz()._repr_html_()
    h.graphviz(force=True).to_png()
    h.graphviz(force=False).to_png()

    h._repr_html_()
    assert h.graphviz().code == """\
digraph {
  node [fontname=Monospace,fontsize=10,shape=none,height=0,width=0,margin="0.055,0.042"];
  edge [arrowhead=vee,arrowsize=0.5,fontname=Monospace,fontsize=9];
  "0" -> "1";
  "2" -> "0" [arrowhead=none];
  "3" -> "0" [arrowhead=none];
  "4" -> "2";
  "5" -> "3";
  "0" [shape=circle,label="",height=.05,width=.05,margin="0.0,0.0"];
  "1" [label="a"];
  "2" [label="b"];
  "3" [label="c"];
  "4" [shape=circle,label="",height=.05,width=.05,margin="0.0,0.0"];
  "5" [shape=circle,label="",height=.05,width=.05,margin="0.0,0.0"];
}
"""

    g = p.coarse_graph()
    print(g.graphviz())
    print(g._repr_svg_())


def test_render_groundings():
    p = Program("""

    a += b * c.

    b += 1.
    c += 1.

    """)

    have = str(render_groundings(p))
    want = """
<table style="font-family: Courier New,monospace;">
        <tr style="border: thin solid black;"><th></th>
        <th style="text-align: left; vertical-align: top;">a += b * c
        </th></tr>
                <tr><td>1.0</td><td style="text-align: left; vertical-align: top;">
                a += b * c
                </td></tr>
        <tr style="border: thin solid black;"><th></th>
        <th style="text-align: left; vertical-align: top;">b += 1
        </th></tr>
                <tr><td>1</td><td style="text-align: left; vertical-align: top;">
                b += 1
                </td></tr>
        <tr style="border: thin solid black;"><th></th>
        <th style="text-align: left; vertical-align: top;">c += 1
        </th></tr>
                <tr><td>1</td><td style="text-align: left; vertical-align: top;">
                c += 1
                </td></tr>
</table>
"""

    assert re.sub('\s+', ' ', have.strip()) \
        == re.sub('\s+', ' ', want.strip())


if __name__ == '__main__':
    from arsenal import testing_framework
    testing_framework(globals())
