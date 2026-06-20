r"""
EXPERIMENTAL PROBE -- eureka "tie-the-knot" classifier.

Standalone; NOT wired into the search (`dyna.search.__init__` does not import
this).  Importable as `dyna.search.knot_probe` and runnable directly:

    python -m dyna.search.knot_probe

Given a program, it enumerates the loop-absorption (eureka) proposals that
`AgendaBasedSearch._drive_eureka` would generate, and classifies each one:

    contract        Case A -- fold the new definition straight into its
                    consumer rule; no recursion is needed.

    linear-knot     Case B -- the absorbed sub-loop closes exactly one cycle
                    back through the rule head; tie the knot (linear recursion).

    branching-knot  Case B -- two or more absorbed subgoals reach the head;
                    tying the knot yields a branching/expansive recursion
                    (harder well-foundedness measure).

The verdict is purely topological.  A proposed eureka `$gen += absorbed` is fed
only by the rule head and feeds nothing else, so `$gen` can be recursive iff
some absorbed subgoal transitively depends on the rule head.  We read that
straight off the coarse dependency graph (`CoarseGraph`): it is exactly
`possibly_expansive` restricted to the absorbed subgoal set.

Framing: Pettorossi & Proietti definition-introduction + unfold/fold strategies
(loop absorption / tupling).
"""

from collections import namedtuple

from dyna import Program, Rule, term_vars


CONTRACT       = 'contract'
LINEAR_KNOT    = 'linear-knot'
BRANCHING_KNOT = 'branching-knot'


# `before`/`eureka_deg`/`residual_deg` are *rule-local* degrees: the degree of
# the rule being transformed, and of the two rules ($gen + residual) that
# replace it.  Whole-program degree is a separate (search-level) concern.
Verdict = namedtuple(
    'Verdict',
    'i, js, kind, eureka, absorbed, reaching, elim_vars, before, eureka_deg, residual_deg',
)


def _roots(nodes, x):
    "Coarse-graph classes that term `x` falls into ([] if none/ambiguous)."
    try:
        return nodes.roots(x)
    except KeyError:
        return []


def _reaching(program, cg, T, i, js):
    "Indices of absorbed subgoals that transitively reach the rule head."
    r = program.rules[i]
    head_roots = _roots(cg.nodes, r.head)
    out = []
    for j in js:
        b = r.body[j]
        if program.is_const(b) or program.is_builtin(b):
            continue
        broots = _roots(cg.nodes, b)
        if any(h in T.outgoing[rb] for rb in broots for h in head_roots):
            out.append(j)
    return out


def classify(program, i, js, cg=None, T=None):
    """Classify one eureka proposal: rule index `i`, absorbed factor indices `js`
    (the loop_absorption recipe used by `_drive_eureka`)."""
    if cg is None: cg = program._coarse_graph()
    if T  is None: T  = cg.g.transitive_closure(reflexive=True)

    r        = program.rules[i]
    eureka   = program.loop_absorption(i, js)
    absorbed = [r.body[j] for j in js]
    rev_fs   = [f for j, f in enumerate(r.body) if j not in js]
    residual = Rule(r.head, eureka.head, *rev_fs)   # consumer rule after the fold

    reaching = _reaching(program, cg, T, i, js)
    n = len(reaching)
    kind = CONTRACT if n == 0 else LINEAR_KNOT if n == 1 else BRANCHING_KNOT

    return Verdict(
        i=i, js=tuple(js), kind=kind, eureka=eureka, absorbed=absorbed,
        reaching=reaching,
        elim_vars=term_vars(absorbed) - term_vars(eureka.head),
        before=r.analyzer.degree,
        eureka_deg=eureka.analyzer.degree,
        residual_deg=residual.analyzer.degree,
    )


def proposals(program):
    "Enumerate + classify every eureka proposal, faithfully to `_drive_eureka`."
    if isinstance(program, str): program = Program(program)
    cg = program._coarse_graph()
    T  = cg.g.transitive_closure(reflexive=True)
    out = []
    for i, r in enumerate(program):
        a  = r.analyzer
        # Warning: proposal assumes commutative products (same as _drive_eureka).
        Fs = {tuple(sorted(a.v2f[v])) for v in a.can_elim}
        for js in sorted(Fs):
            out.append(classify(program, i, js, cg, T))
    return out


#_______________________________________________________________________________
# Reporting

def _fmt(x):
    try:    return x.__repr__(color=False)
    except TypeError: return repr(x)

_MARK = {
    CONTRACT:       'A  contract  (fold straight in)',
    LINEAR_KNOT:    'B  linear-knot  (tie the knot, then fold in)',
    BRANCHING_KNOT: 'B  branching-knot  (expansive recursion)',
}


def probe(program, show=True):
    "Run the classifier over `program`; optionally print a report.  Returns the verdicts."
    if isinstance(program, str): program = Program(program)
    vs = proposals(program)
    if not show: return vs

    print('=' * 78)
    for r in program:
        print('  ' + _fmt(r))
    print('-' * 78)
    if not vs:
        print('  (no eureka proposals)')
    for v in vs:
        r        = program.rules[v.i]
        after    = max(v.eureka_deg, v.residual_deg)
        win      = '  win' if after < v.before else ''
        elim     = ', '.join(sorted(map(str, v.elim_vars))) or '-'
        absorbed = ' * '.join(_fmt(b) for b in v.absorbed)
        reaching = ', '.join(_fmt(r.body[j]) for j in v.reaching) or '(none)'
        print()
        print(f'  rule[{v.i}]  eliminate {{{elim}}}    rule-degree {v.before} -> {after}{win}')
        print(f'      absorb        {absorbed}')
        print(f'      eureka        {_fmt(v.eureka)}')
        print(f'      reaches head  {reaching}')
        print(f'      => {_MARK[v.kind]}')
    print('=' * 78)
    return vs


#_______________________________________________________________________________
# Demo / self-check

EXAMPLES = {
    'linear (path builder)': """
        f(I,L) += g(I,J) * f(J,K) * h(K,L).
        inputs: g(_,_); h(_,_).
        outputs: f(_,_).
    """,
    'contract (start-path)': """
        path(I,I).
        path(I,K) += path(I,J) * edge(J,K).
        goal += start(I) * path(I,K) * stop(K).
        inputs: start(_); edge(_,_); stop(_).
        outputs: goal.
    """,
    'branching (CYK-like)': """
        t(I,L) += t(I,K) * t(K,L) * mid(I,L).
        inputs: mid(_,_).
        outputs: t(_,_).
    """,
}


def main():
    results = {}
    for name, src in EXAMPLES.items():
        print()
        print('#', name)
        results[name] = probe(src)

    kinds = lambda name: sorted({v.kind for v in results[name]})
    assert kinds('linear (path builder)')  == [LINEAR_KNOT],    kinds('linear (path builder)')
    assert kinds('contract (start-path)')  == [CONTRACT],       kinds('contract (start-path)')
    assert kinds('branching (CYK-like)')   == [BRANCHING_KNOT], kinds('branching (CYK-like)')
    print('\nself-check OK')


if __name__ == '__main__':
    main()
