"""
Constraint propagation
"""
from arsenal import colors
from dyna.pretty import PrettyPrinter
from dyna.term import Term, fresh, Var, replace_in_expr, Subst, FAIL
from dyna.program import Program
from dyna.builtin import Builtins


FAIL = Term('$fail')


def scons(subst):
    return tuple(Term('=', X,Y) for X,Y in subst.items())


class Chart:

    def __init__(self, chart=None):
        self.chart = set() if chart is None else set(chart)

    def __iter__(self): return iter(self.chart)

#    def __le__(self, other):
#        return set(self) <= set(other)

#    def __eq__(self, other):
#        return self.chart == other.chart

    def lookup(self, q, subst):
        #if is_const(q):
        #    yield subst
        #    return
        for x in list(self.chart):          # Use indexing
            subst1 = subst.copy().cover(q, x)
            #assert subst1 is None or subst1(x) == x
            if subst1 is Subst.FAIL: continue
            yield subst1

    def join(self, xs, subst):
        "Expand a conjunctive query against the chart."
#        if not isinstance(subst, Subst): subst = Subst(subst)
        if len(xs) == 0:
            yield subst
        else:
            for subst1 in self.lookup(xs[0], subst.copy()):
                if subst1 is Ellipsis: subst1 = subst
                yield from self.join(xs[1:], subst1)

    def update(self, x):
        self.chart.add(x)

    def __repr__(self):
        pp = PrettyPrinter()
        return '{\n%s\n}' % '\n'.join(
            f'  {pp(r)}' for r in sorted(self.chart)
        )


class ConstraintPropagation:

    DEBUG = 0

    def __init__(self, rules='', debug=0, propagation_hooks=()):
        if isinstance(rules, str): rules = Program(rules)
        self.rules = rules
        self.chart = None
        self.agenda = None
        self.bindings = None
        self.checked = None
        self.propagation_hooks = list(propagation_hooks)

        # TODO: builtins should fall out of program
        self.builtins = Builtins(None)
        self._pp = PrettyPrinter()
        self.pp = self._pp.print
        self.debug = max(debug, self.DEBUG)

    def __repr__(self):
        return f'{self.__class__.__name__} {Program(self.rules)}'

    # the broarder picture of whats going on in this method is that we have some
    # constraints that are "checkable".  Checkable constraints must be
    # semi-deterministic (i.e., they are queries that have <= 1 answer and a
    # semizero/semione value).  These are common for builtins, but we can braden
    # that to semi-det user-constaints.
    def check(self, q):

        if not isinstance(q, Term):
            yield Ellipsis

        # TODO: need a smarter way to specify which user constraints are checkable
        elif q.fn == 'ks' or q.fn == 'ws':
            # Below, we try querying the main program (if one is provided).  In
            # the event that <= 1 results are found, we can use them during
            # propagation---just like built-ins constraints!

            program = Program("""
            ks([]).
            ks([K|Ks]) :- k(K), ks(Ks).

            ws([]).
            ws([K|Ks]) :- w(K), ws(Ks).

            """)

            def query(q, subst):
                if subst is None: return
                if isinstance(q, (tuple, list)):
                    if len(q) == 0:
                        yield subst.copy()
                    else:
                        for subst1 in query(q[0], subst.copy()):
                            yield from query(q[1:], subst1)
                    return
                if q in self.chart:
                    yield subst
                    return
                for r in program:
                    r = fresh(r)
                    s = subst.copy().mgu(r.head, q)
                    if s is Subst.FAIL: continue
                    if s(r.head) == q:
                        yield from query(s(r.body), s)

            results = list(query(q, {}))
            if len(results) == 0:
                yield None
            elif len(results) == 1:
                yield results[0]
            else:
                # too many results: must skip; semi-det only
                yield Ellipsis

        elif q.fn in {'<','>','<=','>='}:    # XXX: fix this hardcoding
            yield from self.check(Term('is', True, q))

        elif q.fn == 'is':
            # indirect to avoid in-place variable - we use subst in this module.
            q0 = fresh(q)
            b = self.builtins
            if b.is_ready(q0):    # evaluate subgoal if it's ready
                count = 0
                for _ in b(q0):
                    assert count == 0, 'only semidet constraints should run'
                    count += 1
                    subst1 = Subst().mgu(fresh(q0), q)
                    yield subst1
                if count == 0:
                    yield None
            else:
                yield Ellipsis

        else:
            yield Ellipsis

    def update(self, x):
        if x not in self.chart:
            self.agenda.add(x)
            self.chart.update(x)   # push-time updates
            if self.debug >= 2:
                self.pp(colors.magenta % '    push:', x)
        else:
            if self.debug >= 2:
                self.pp(colors.magenta % '    push-dup:', x)

    def __call__(self, D):
        assert isinstance(D, (list, tuple, set, Chart)), D
        # reset chart and agenda
        self.chart = chart = Chart()
        self.agenda = agenda = set()
        self.bindings = []
        self.checked = set()

        update = self.update

        if self.debug >= 1: print(colors.magenta % 'inputs')
        for x in D: update(x)

        if self.debug >= 1: print(colors.magenta % 'init')

        for r in self.rules:
            for subst in chart.join(r.body, Subst()):
                r1 = subst(r)
                if r1.head == FAIL: return
                if self.debug >= 2: self.pp(colors.magenta % '  pop', r1)
                update(r1.head)

        iteration = 0
        while True:
            iteration += 1

            if not agenda:
                return chart
            driver = agenda.pop()

            if self.debug >= 1:
                self.pp(colors.magenta % 'pop', driver)

            # try to evaluate the builtin constraint
            for subst in self.check(driver):
                if subst is Ellipsis: continue   # constraint is not ready
                self.checked.add(driver)
                if subst is None: return         # constraint failed
                for k,v in subst.items():
                    update(Term('=',k,v))

            if isinstance(driver, Term) and driver.fn == '=':
                X,Y = driver.args

                # check for a contradiction
                if not isinstance(X, Var) and not isinstance(Y, Var) and X != Y: return

                # Release the equality constraint now that it has be
                # successfully applied.
                self.checked.add(driver)

                # eagerly replace all the instances of the variable with its
                # value (in both the chart and agenda)
                if X != Y:
                    for x in list(self.chart):
                        if isinstance(x, Term) and x.fn != '=':
                            self.update(replace_in_expr(x, X, Y))
                            self.update(replace_in_expr(x, Y, X))

                self.bindings.append(driver)  # keep a record of the substitution

                # If there was a change (i.e., a variable is more instantiated),
                # we might want to try re-evaluating pending constraint that
                # depend on them as these constraints may be ready now.
                #
                # TODO: use indexing to speed up finding constraints that depend
                # on the variables that were affected
                for x in chart:
                    if isinstance(x, Term) and x.fn == 'is' and self.builtins.is_ready(x):
                        self.agenda.add(x)

            for r in self.rules:
                for k in range(len(r.body)):
                    subst0 = Subst().cover(r.body[k], driver)
                    if subst0 is not None:
                        for subst1 in chart.join([*r.body[:k], *r.body[k+1:]], subst0):
                            r1 = subst1(r)
                            if r1.head == FAIL: return
                            if self.debug >= 2: self.pp(colors.magenta % '  rule:', r1)
                            update(r1.head)

            for hook in self.propagation_hooks:
                hook(self, driver)
