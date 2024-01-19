"""
Implementation of type-based abbreviation transformation.
"""

from arsenal import colors
import warnings

from dyna.analyze import add_free_constraints
from dyna import (
    Program, Rule, PrettyPrinter, TransformedProgram, join_f, Term, vars, fresh,
    is_var, Subst, snap, unify, covers, unifies, deref
)


def body(x): return x.body if isinstance(x, Rule) else [x]


def snap_vars(x):
    return {snap(v) for v in vars(x)}


def freebies(r):
    "Returns the set of $free-typed variables in `r`."
    return {
        snap(x.args[0])
        for x in r.body
        if isinstance(x, Term) and x.fn == '$free'
    }


class Abbreviate(TransformedProgram):

    def __init__(self, program, types, debug=False):

        self.parent = program
        self.types = types

        self.types.chart = self.types.chart.sort()   # for stability in test cases
        del types

        assert self.types.is_disjoint()
        assert self.types._input_type.inputs is not None

        if debug: print(colors.render(colors.light.magenta % self.types))

        def add_rule(r_id, r):
            r = fresh(r)
            r._orig_rule_index = r_id
            new_rules.append(r)

        # recovery rules (can easily be pruned away)
        self._new_names = {}
        new_rules = []
        for i, t in enumerate(self.types.chart):
            t.i = i   # assign type ids

            # Give the abbrevation a familiar name based on the original function symbol
            self._new_names[i] = self.parent._gen_functor(t.head.fn + f'_{i}')

            if self.parent.is_input(t.head):
                # special handling for free and bound
                add_rule(None, Rule(self.__abbrev(t), t.head, *[c for c in t.body if c.fn not in {'$free', '$bound'}]))
            else:
                # abbreviation is disallowed for input items
                add_rule(None, Rule(t.head, self.__abbrev(t)))

        for r_id, r in enumerate(program):
            r = fresh(r)
            if debug:
                pp = PrettyPrinter()
                print(colors.render(f'\n{colors.render(colors.magenta % pp(r, color=False))}'))

            for t_body in join_f(self.types.chart.lookup, *r.body):

                # constraint closure for the body's type
                frees = [Term('$free', v) for v in vars(r.head) - vars(r.body)]
                # body constraints before closure
                body_constraints = [b for t_b in t_body for b in body(t_b)]
                # body constraints after closure
                body_closure = self.types.rewrites(Rule(r.head, *body_constraints, *frees), ALLOW_FREE_MERGE=True)

                if body_closure is None: continue

                for tt in self.types.chart.lookup(r.head):

                    t_head = self.types.rewrites(Rule(r.head, *tt.body, *body_closure.body), ALLOW_FREE_MERGE=False)
                    #t_head = self.types.rewrites(Rule(r.head, *tt.body, *body_closure.body), ALLOW_FREE_MERGE=True)

                    if t_head is None: continue
                    t_head.i = tt.i

                    # we are required to check the head constraints that aren't guaranteed by the body's type.
                    head_constraints = set(t_head.body) - set(body_closure.body)

                    new_rule = Rule(
                        self.__abbrev(t_head),
                        *[self.__abbrev(t_y) for t_y in t_body],
                        *head_constraints,
                    )

                    new_rule = self.__dropped_var_correction(body_closure, new_rule, debug)

                    add_rule(r_id, new_rule)

        super().__init__('specialize', program, new_rules)
        # the user's type parameter are now required as input
        self.set_input_types(self.inputs + self.types._input_type.inputs)

    def __dropped_var_correction(self, body_closure, new_rule, debug):
        # apply the multiplicity correction if a free local variable is lost
        if freebies(body_closure) - snap_vars(body_closure.head) != freebies(new_rule) - snap_vars(new_rule.head):
            if debug: print(colors.light.red % 'VARS CHANGED!')
            new_rule = Rule(new_rule.head, *new_rule.body, self.parent.Semiring.multiple(float('inf')))
        return new_rule

    def __abbrev(self, t):
        if self.is_const(t): return t
        assert isinstance(t, Rule), t
        if self.parent.is_builtin(t.head): return t.head
        assert hasattr(t, 'i')
        t_type = self.types.chart.rules[t.i]
        #print(
        #    #colors.orange % 'inst name:',
        #    #colors.orange % 'vars:', vars(t),
        #    #colors.orange % 'free:', freebies(t),
        #    colors.orange % 't:', t, '\n',
        #    colors.orange % 't_type:', t_type,
        #)
        return Subst().mgu(t_type.head, t.head)(
            Term(self._new_names[t.i], *(vars(t_type) - freebies(t_type)))
        )
