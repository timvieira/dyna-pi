import re
from arsenal import assert_throws

from dyna import Program
from dyna.util import Graph, GroundingsPrinter, latex, run_cmd, render_groundings, tikz


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


def todo_latex():

    x = latex(r"""
    \documentclass{article}
    \begin{document}
    Hello, World.
    \end{document}
    """)
    x.to_svg()

    with assert_throws(Exception):
        run_cmd(['non-existent-executable', '--help'])


def todo_tikz():
    tikz(r'\Tree [.a b c ]', force=1).to_svg()
    tikz(r'\Tree [.a b c ]', force=1).to_png()


def todo_tikz_derivations():

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
<style>.grnd{interpolate-size:allow-keywords}.grnd::details-content{block-size:0;overflow:clip;transition:block-size .2s ease,content-visibility .2s;transition-behavior:allow-discrete}.grnd[open]::details-content{block-size:auto}</style>
<details open class="grnd" style="font-family: Courier New,monospace; margin: 1px 0;">
<summary style="cursor: pointer;"># 0: a <span style="color: blue;">+=</span> b * c</summary>
<div style="margin-left: 0.55em; padding-left: 1em; border-left: 1px solid #ccc;"><table><tr><td style="vertical-align: top; padding-right: 1em; color: #888;">1.0</td><td style="text-align: left; vertical-align: top;">a <span style="color: blue;">+=</span> b * c</td></tr></table></div>
</details>
<details open class="grnd" style="font-family: Courier New,monospace; margin: 1px 0;">
<summary style="cursor: pointer;"># 1: b <span style="color: blue;">+=</span> <span style="color: #aa6699;">1</span></summary>
<div style="margin-left: 0.55em; padding-left: 1em; border-left: 1px solid #ccc;"><table><tr><td style="vertical-align: top; padding-right: 1em; color: #888;">1</td><td style="text-align: left; vertical-align: top;">b <span style="color: blue;">+=</span> <span style="color: #aa6699;">1</span></td></tr></table></div>
</details>
<details open class="grnd" style="font-family: Courier New,monospace; margin: 1px 0;">
<summary style="cursor: pointer;"># 2: c <span style="color: blue;">+=</span> <span style="color: #aa6699;">1</span></summary>
<div style="margin-left: 0.55em; padding-left: 1em; border-left: 1px solid #ccc;"><table><tr><td style="vertical-align: top; padding-right: 1em; color: #888;">1</td><td style="text-align: left; vertical-align: top;">c <span style="color: blue;">+=</span> <span style="color: #aa6699;">1</span></td></tr></table></div>
</details>
"""

    assert re.sub('\s+', ' ', have.strip()) \
        == re.sub('\s+', ' ', want.strip())


def test_show_groundings():
    p = Program("""

    a += b * c.

    b += 1.
    c += 1.

    """)

    d = p.agenda()
    g = p.show_groundings(d)

    # `show_groundings` returns a surface-aware pretty-printer, not None.
    assert isinstance(g, GroundingsPrinter)

    # Notebook surface: HTML matches the standalone `render_groundings`.
    assert g._repr_html_() == render_groundings(p, d)

    # Terminal surface: ANSI-stripped text shows each rule and its value.
    text = re.sub(r'\x1b\[[0-9;]*m', '', repr(g))
    assert '# 0: a += b * c' in text
    assert '1.0: a += b * c' in text

    # The grounding *data* lives on `Program`; metadata is out of band in the
    # records, not patched onto the ground rules.
    records = list(p.groundings(d))
    assert [rec.i for rec in records] == [0, 1, 2]
    assert all(not hasattr(rec.rule, '_contrib_value') for rec in records)
    assert [str(r) for r in p.instantiate(d).rules] == [str(rec.rule) for rec in records]

    # Filtering returns a new printer; the original is unchanged (immutable).
    assert g.hide(1, 2).hidden == {1, 2}
    assert g.only(0).hidden == {1, 2}
    assert g.hidden == frozenset()
    assert '1.0:' not in re.sub(r'\x1b\[[0-9;]*m', '', repr(g.hide(0)))   # rule 0 dropped from console
    # HTML: every source rule is a collapsible <details>, expanded by default;
    # a hidden rule starts collapsed.
    assert g._repr_html_().count('<details open') == 3
    assert g.hide(0)._repr_html_().count('<details open') == 2


def test_show_groundings_colors():
    p = Program("""
    goal += a(I) * x(I).
    a(I) += y(I).
    inputs: x(_).
    outputs: goal.
    """)
    html = p.show_groundings()._repr_html_()
    # rules are syntax-colored, and declared input/output items carry their role
    # colors -- the same `color='html'`/`roles` convention as `Program`'s HTML.
    assert 'color: blue;">+=</span>' in html       # aggregator
    assert 'color: green;">I</span>' in html        # variable
    assert 'color: #d4a017;">goal</span>' in html   # output (gold)
    assert 'color: #7b2fbe;">x</span>' in html      # input (violet)


if __name__ == '__main__':
    from arsenal import testing_framework
    testing_framework(globals())
