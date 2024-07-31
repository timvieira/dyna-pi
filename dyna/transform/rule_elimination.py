from arsenal import colors

from dyna import fresh, unify, TransformedProgram, Constant, I

#______________________________________________________________________________
# Support the elimination of non-range-restricted rules
#
# goal += f(X).
# f(X) += 1.
#
# ==>
#
# goal += 1.
#
# which is incorrect because it ignores the infinite multiplicity of X.
# Currently, we spot these tricky cases and throw an exception.
# There is a general fix that involves aggregation with multiplicity -
# we encountered in in the non-ground forward chaining solver.

inf = float('inf')

class LinearRuleElimination(TransformedProgram):
    """
    Eliminate a given rule (specified by index) from a give program.
    This version of the transform assumes that the rest of the program
    depends on this rule "linearly" -- meaning that the eliminated rules
    head does not appear more than once in any other rules body.  We can
    force the program to satisfy this property by calling "linearize" on it.
    """

    def __init__(self,
                 program,
                 i: 'Index of rule to eliminate',
                 debug: 'enable debugging' = False,
    ):

        self.i = i
        self.s = s = program.rules[i]

        # Below we check that we aren't eliminating rule that directly feeds into
        # an output node because the transform will alter its semantics.
        if program.outputs is not None:
            assert not program.is_output(s.head), \
                f'Unsafe to eliminate rules {s} because feed into outputs {program.outputs}.'

        if debug: print(colors.light.cyan % 'ELIM', s)

        new_program = program.spawn()
#        new_program = []
        for _r in program:
            r = fresh(_r) if _r is s else _r
            count = 0
            for j, b in enumerate(r.body):
                for _ in unify(s.head, b):
                    count += 1
                    new_program[r.head] = (
                        Constant(r.body[:j])
                        * I(s.head, b, program.Semiring.one)
                        * Constant(s.body)
                        * Constant(r.body[j+1:])
                    )

#                    t = Rule(r.head, *r.body[:j], *s.body, *r.body[j+1:])
#
#                    # Special handling for non-range-resitricted rule elimination
#                    #
#                    # f(X) += 1.          % <== elim
#                    # goal += f(X).
#                    # ==>
#                    # goal += 1.   % incorrect because 1 should have infinite multiplicity.
#                    #
#                    # On the other hand, this case is safe because the non-rr variables
#                    # aren't lost during elimination.
#                    #
#                    # temp(X0,X0) += 1.
#                    # temp(X,X0) += rewrite(X,Y) * temp(Y,X0).
#                    # ==>
#                    # temp(X,X0) += rewrite(X,Y) * 1.
#                    #
#                    if not (set(vars(s)) <= set(vars(t))):
#                        semiring = program.Semiring
#                        m = semiring.multiple(inf)
#                        t = Rule(r.head, *r.body[:j], *s.body, m, *r.body[j+1:])
#
#                    new_program.append(t)
##                    new_program.append(fresh(t))
#                    if debug:
#                        print(colors.light.magenta % '•', colors.render(colors.light.magenta % r))
#                        print(colors.light.magenta % '→', colors.render(colors.light.yellow % t))
#
#                    # TODO: we could do linearization here, which would generate
#                    # the extra rules on an "as needed" basis.  Basically, if a
#                    # count>1 generate swap in a tmp'd subgoal instead of
#                    # generating the `t` rule above.

            if count > 1:
                # [2021-09-06 Mon] I believe that our linearization step is
                # sufficient to avoid issues.
                assert False, f'call linearize before elim! {program}\n\n{program.linearize()}'
                pass

            if _r is s: continue
            new_program.append(r)

        super().__init__(f'LinearRuleElimination({self.i})', program, new_program)
