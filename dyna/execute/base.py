from dyna import Program, Rule, term, Float, fresh, Product
from dyna.builtin import Builtins
from arsenal.robust import timelimit, Timeout


tupleone = Product()


class BaseSolver:

    def __init__(self, program, tol=1e-8):
        #assert isinstance(program, Program), program

        self.builtins = Builtins(None)

        self.program = program
        self.Weight = self.program.Semiring
        self.zero = self.program.Semiring.zero
        self.one = self.program.Semiring.one
        self.prefix_firings = 0

        self.interrupted = False
        self.initialized = set()
        self.tol = tol

    def user_query(self, q, **kwargs):
        """
        Answer user query `q`, returns a (mostly consolidated)
        program with += aggregators.
        """
        if isinstance(q, str): q = term(q)
        #if self.program.outputs is not None:
        #    assert self.program.is_output(q), f'{q} is not a declared output'

        # If we interrupted execution, don't start it up again.
        if not self.interrupted: self(**kwargs)
        result = Program([fresh(Rule(q, v)) for v in self.lookup_vals(q)],
                         semiring=self.Weight)
        result = result.constant_folding().sort()
        return result

    def lookup_vals(self, q):
        raise NotImplementedError()

    def sol(self):
        "Return solution as `Program`."
        return Program([Rule(k, v) for k, v in self.chart.items()], semiring=self.Weight, inputs='')

    def assert_equal(self, want, **kwargs):
        return self.sol().assert_equal(want, **kwargs)

    def assert_equal_query(self, q, want, **kwargs):
        return self.sol().assert_equal_query(q, want, **kwargs)

    # XXX: Defer to a semiring-specific defn that lives in the semiring class?
    def approx_equal(self, x, y):
        if self.Weight != Float and self.Weight is not None:
            return x == y
        else:
            # direct equality is useful for comparing values like infinity
            return x == y or abs(x - y) <= self.tol

    #___________________________________________________________________________
    # Inference methods

    def __call__(self, data='', budget=None, kill=False, throw=True, **kwargs):
        "shortcut to load `data` and run forward chaining."
        try:
            with timelimit(budget):
                self.load_data(data)
                self._forward_chaining(*kwargs)
        except KeyboardInterrupt as e:  # pragma: no cover
            self.interrupted = True
            if kill: raise e
            print('^C')
        except Timeout as e:
            self.interrupted = True
            #print('timed out')
            if throw: raise e   # pragma: no cover
        return self

    forward_chaining = __call__

    def _forward_chaining(self):
        raise NotImplementedError()

    # XXX: Can we directly call `chart.join` and `chart.lookup` instead of these methods
    def join(self, xs, value):
        """
        Answer conjunctive query `xs` using the current chart,
        returns an iterator which binds variables in `xs` and emits values.
        """
        self.prefix_firings += 1
        if len(xs) == 0:
            yield value
        else:
            for v in self.lookup_vals(xs[0]):
                yield from self.join(xs[1:], value * v)

    def ground_out_rule(self, r):
        "Ground out the rule `r` against the current chart."
        assert isinstance(r, Rule), r
        for value in self.join(r.body, self.one):
            yield value * self.program.multiple(r)

    def init_rule(self, r):
        "Ground out the rule `r` against the current memo table."
        assert isinstance(r, Rule), r
        # use id(r) to avoid possibility that two rule test equal, e.g., if we
        # have two `x += 1` rules.
        if id(r) in self.initialized: return
        self.initialized.add(id(r))
        # Notes: If a rule is late to the game, then the chart may be populated.
        # Thus, the rule r may have contribution even if it's RHS is not a
        # constant.  This is different from the fresh slate situation.  Thus,
        # the code below supports both the constant and non-constant RHS cases.
        r = fresh(r)
        if self.debug: print('init rule\n  rule:', r)
        for c in self.ground_out_rule(r):
            self.update(r.head, c)

    # TODO: this method is used in the benchmarks to allows the solvers to have
    # time to do data-independent setup.
    def load_data(self, data):
        """
        Load data specified as Dyna code.
        Warning: these rules will not be saved!
        """
        # TODO: Add checks that the data match the input anntations; similarly,
        # add checks that the user queries match the output annotations.
        if not isinstance(data, Program): data = Program(data)   # parse here, lift below.
        if data.semiring is None and self.program.semiring is not None:
            data = data.lift_semiring(self.program.semiring)
        assert self.program.Semiring == data.Semiring, [self.program.Semiring, data.Semiring]
        d = self.__class__(data)._forward_chaining()
        for k,v in d.chart.items():
            # XXX: might be fine to allow items that are irrelevant to the
            # Program, which are not declared input.  We may also want to
            # downgrade the assertion to a warning.
            #assert self.program.is_input(k), f'`{k}` not a declared input'
            self.update(k, v)
        return d.sol()
