import numpy as np
from arsenal import Integerizer, colors
from dyna import TransformedProgram, Program, Rule, Term, vars, canonicalize


def kleene(A, semiring, reflexive=True):
    """
    Solve B = I + A B for B given a weighted binary relation A in semiring^{N
    \times N} where N is the relation's domain.

    Equivalent to reflexive+transitive closure of a weighted binary relation
    (i.e., matrix).  If `reflexive=False`, it will return the transitive
    closure.
    """
    # initialization
    [N,_] = A.shape; zero = semiring.zero; one = semiring.one
    new = A.copy(); old = A.copy()
    for j in range(N):
        new[:,:] = zero
        sjj = semiring.star(old[j,j])
        for i in range(N):
            for k in range(N):
                # i ➙ j ⇝ j ➙ k
                new[i,k] = old[i,k] + old[i,j] * sjj * old[j,k]
        old, new = new, old   # swap to repurpose space
    if reflexive:  # post processing fix-up: add the identity matrix
        for i in range(N): old[i,i] += one
    return old


class kleene_linsolve(TransformedProgram):

    def __init__(self, p):

        # First, we estimate the support of the program. Note that this is
        # faster than solving the program because it runs in the boolean
        # semiring where cycles do not slow us down.
        b = p.booleanize()
        bsol = b.agenda()

        # TODO: We need to be more careful about cases where the rule doesn't
        # come to ground.  I'm not entirely sure how to get a finite linear
        # system, but I think it should be possible.  In the worst case, we can
        # use inst-based specialization to eliminate the variables.  So what
        # ever that is doing is probably what we need to do.

        M = p.Semiring.chart()
        V = p.Semiring.chart()

        # The following two loops instantiate p's rules according to the
        # estimated support in `bsol`.
        for r in p:
            for _ in bsol[r.body]:

                # Below, we extract <= 1 variable and fold coefficients
                vs = []
                coeff = p.Semiring.one
                for b in r.body:          # XXX: assumes commutativity - better to check!
                    if p.is_const(b):
                        coeff *= b
                    else:
                        vs.append(b)
                assert len(vs) <= 1

                if len(vs) == 0:
                    V[canonicalize(r.head)] += coeff

                else:
                    [var] = vs

                    [h, v] = canonicalize(Term('tmp', r.head, var)).args

                    if len(vars(v) - vars(h)) > 0:
                        #print('warning dropped variable')
                        #print(h, '+=', v)
                        coeff = coeff * p.Semiring.multiple(float('inf'))

                    M[h, v] += coeff


        pack = pack_arrays(M, V, p.Semiring)
        self.arrays = pack

        #print(p)
        #print(pack)

        sol = kleene(pack.MM, p.Semiring) @ pack.VV

        Sol = [Rule(x, sol[i]) for i,x in enumerate(pack.ix)]

        super().__init__('linear-solve', p, Sol)


# TODO: Cut out the conversion to arrays, just work with charts
class pack_arrays:
    def __init__(self, M, V, Semiring):
        # pack everything into arrays

        # determine the alphabet
        ix = Integerizer()
        for i,j in M:
            ix(i), ix(j)
        for i in V:
            ix(i)

        MM = np.full((len(ix), len(ix)), Semiring.zero)
        for i,j in M:
            MM[ix(i), ix(j)] = M[i,j]

        VV = np.full(len(ix), Semiring.zero)
        for i in V:
            VV[ix(i)] = V[i]

        self.XX = np.array(list(ix))
        self.MM = MM
        self.VV = VV
        self.ix = ix

        self.Semiring = Semiring

    def __repr__(self):
        lines = ['Linear Equations {']
        for i,x in enumerate(self.ix):
            lin = ' + '.join(f'{colors.magenta % self.MM[i,j]}⋅{y}' for j,y in enumerate(self.ix) if self.MM[i,j] != self.Semiring.zero)
            if lin:
                lines.append(f'  {x} == {colors.magenta % self.VV[i]} + {lin}')
            else:
                lines.append(f'  {x} == {colors.magenta % self.VV[i]}')
        lines.append('}')
        return '\n'.join(lines)
