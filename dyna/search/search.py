import numpy as np
from arsenal import colors, take, Integerizer, timelimit
from arsenal.datastructures.pdict import pdict
from collections import Counter
from functools import lru_cache
from time import time
from itertools import product

from dyna import (
    Program, TransformedProgram, Rule, Define, Fold, Unfold,
    make_smt_measure, unifies, covers, fresh, ProgramCollection, MostGeneralSet
)
from dyna.transform.fold import prune_r_S
from dyna.util import OrderedSet


class Agenda:
    def __init__(self, priority_fn):
        self.priority_fn = priority_fn
        self.p = pdict()

    def pop(self):
        return self.p.pop()

    def add(self, x):
        self.p[x] = self.priority_fn(x)

    def __len__(self):
        return len(self.p)


class State:
    def __init__(self, program, eureka, unfold, lct):
        self.program = program
        self.eureka = eureka
        self.unfold = unfold
        self.lct = lct

    def __repr__(self):
        lines = ['{']

        if self.lct is not None:
            x,ref,pos = self.lct

            Pos = {ref.rules.index(rr): jj for rr,jj in pos.items()}

            lines.append(
                (colors.light.cyan % f' <<<< {self.lct[0], Pos } {ref.__repr__(color=False, indent="  >>> ")}')
            )

        for r in self.program:
            if self.lct is not None and r in self.lct[2]:
                lines.append('  ' + colors.cyan % r.__repr__(color=False) + (colors.light.cyan % f' <<<< {self.lct[2][r]}'))
            elif r in self.unfold:
                lines.append('  ' + colors.dark.white % r.__repr__(color=False))
            elif r in self.eureka:
                lines.append('  ' + colors.dark.yellow % r.__repr__(color=False))
            else:
                lines.append('  ' + r.__repr__(color=False))
        lines.append('}')
        return '\n'.join(lines)



class AgendaBasedSearch:

    def __init__(
            self, program,
            p_greedy=0.75,
            ALLOW_REVERSIBLE=False,
            ALLOW_LCT=False,
            ALLOW_SLASH=False,
            seed=0,
    ):
        if isinstance(program, str): program = Program(program)
        if seed is not None: np.random.seed(seed)
        self.program = program
        self.semiring = program.semiring
        assert program.inputs is not None and program.outputs is not None

        self.p_greedy = p_greedy

        self.ALLOW_LCT = ALLOW_LCT
        self.ALLOW_SLASH = ALLOW_SLASH
        self.ALLOW_REVERSIBLE = ALLOW_REVERSIBLE

        self.pops = 0
        self.pushes = 0
        self.pop_stats = Counter()
        self.agenda_stats = Counter()
        self.agenda = Agenda(lambda i: self.P[i].program.prune_very_fast().degrees())
        self._fifo = OrderedSet()
        self.chart = OrderedSet()

#        self._dups = 0
        self._n_check_measure = 0
        self._n_check_measure_fails = 0

        self.measure = make_smt_measure(program)

        self.verbosity = 0
        self.verbosity_K = 1

        self._reserved_names = {x.fn for x in self.program.inputs.just_heads()}

        self._best = program
        self._best_cost = program.prune_fast().degrees()

        self._start_time = time()

        self.P = Integerizer()

        self._update(State(program, set(), set(), None))

    def to_collection(self, agenda=False):
        xs = self.agenda if agenda else self.chart
        return ProgramCollection({self.P[i].program for i in xs})

    def run(self, *args, **kwargs):
        for _ in self.run_agenda(*args, **kwargs): pass
        return self

    def run_agenda(self, steps, **kwargs):
        try:
            for x in take(steps, self._run_agenda(**kwargs)):
                yield x
        except KeyboardInterrupt:  # pragma: no cover
            print('^C')
            return

    def _run_agenda(self):

        while self.agenda:  # pragma: no branch
            self.pops += 1

            if np.random.uniform() <= self.p_greedy:
                i = self.agenda.pop()
                self._fifo.remove(i)

            else:
                i = self._fifo[0]
                self._fifo.remove(i)
                del self.agenda.p[i]

            x = self.P[i]
            self.pop_stats[type(x.program).__name__] += 1

            if not self.check_measure(x.program): continue
            self.chart.add(i)

            x_cost = x.program.prune_fast().degrees()
            if x_cost < self._best_cost:
                self._best = x.program
                self._best_cost = x_cost

            if 0:
                y = x
                try:
                    y = x.prune().abbreviate().prune_fast()
                except AssertionError as e:
                    print('specialization error:', colors.light.red % e)
                yield y.program
            else:
                yield x.program

#            print(colors.light.cyan % 'POP ::', x)

            self.drive(x)

    @lru_cache(None)
    def check_measure(self, p):
        assert isinstance(p, Program), type(p)   # avoid silly mistakes
        if not isinstance(p, (Fold, Unfold)): return True   # don't bother checking in these cases
        m = self.measure(p)
        self._n_check_measure += 1
        s = m.is_safe()   # we add the safety conditions of the current complete program
        if not s: self._n_check_measure_fails += 1
        return s

    def _update(self, _x):
        assert isinstance(_x, State)
#        print(colors.orange % ':: PUSH:', _x)
        i = self.P(_x)   # use integerizer
        self.pushes += 1
        _x.pushed = self.pushes
        self.agenda_stats[type(_x.program).__name__] += 1

        self.agenda.add(i)
        self._fifo.add(i)

    def optimize_plans(self):
        "warning: tasks is ignored"
        return self._best

    def drive(self, state):

        no_unfold = len(set(state.program) - state.unfold) == 0
        no_eureka = len(set(state.program) - state.eureka) == 0

        if state.lct is None:

            if no_unfold:
                self._drive_folds(state)

            if 1: #len(set(state.program) - state.unfold) == 0:
                self._drive_eureka(state)

            if no_eureka:
                self._drive_unfold(state)

        # EXPERIMENTAL
        if no_unfold and no_eureka:
            if self.ALLOW_SLASH:  self._drive_slash(state)
            if self.ALLOW_LCT:    self._drive_lct(state)

        if self.ALLOW_REVERSIBLE: self._drive_reversible_folds(state)


    _n_slash_proposals = 0
    _n_slash_rejected = 0

    def _drive_reversible_folds(self, state):
        # TODO: only consider the 'done' rules for folds???

        Rs = state.program.fold_proposals(
            defs = state.program,
            skip_trivial = True,
            skip_zero_width = True,
        )

        for r in Rs:
            # Search for the subsets S ⊆ parent that could be replaced by `r`.
            def f(S):
                new = Fold(parent=state.program, r=r, S=S, defs=state.program, j=0)   # XXX: not sure about j=None here.
                yield new
                for j in S: yield from f(S - {j})

            Qs = prune_r_S(state.program, r)
            for q in f(frozenset(Qs)):
                if q.safe_by_rev:
                    self._update(State(q, state.eureka, state.unfold, state.lct))
                    break

    def _drive_folds(self, state):
        skip_trivial = True
        skip_zero_width = True

        program = state.program
        # Drive folds
        for defs in program.lineage():

            # This version of the fold actions constrains the megafolds that
            # we are considering to just those that include some new
            # definition and constraint the fold to that definition (allow
            # the initial program too, of course)

            # TODO: eventually add speculation/lct because they are new
            # definitions that may be worth folding against
            if isinstance(defs, Define):
                def_ix = list(defs._new_ix)
            elif not isinstance(defs, TransformedProgram):   # original program
                def_ix = list(range(len(defs)))
            else:
                def_ix = []
                continue
            if defs is program: defs = defs.fresh()

            for r in state.program.fold_proposals(
                defs = Program([defs.rules[i] for i in def_ix]),
                skip_trivial = skip_trivial,
                skip_zero_width = skip_zero_width
            ):
                for q in program.folds_by(r=r, js=r.j, defs=defs):
                    self._update(State(q, state.eureka, state.unfold, state.lct))    # TODO: should this advance something???

    def _drive_unfold(self, state):

        program = state.program
        # Drive unfolds - we limit unfolds to just the 'original' definition
        for i, r in enumerate(program):
            if r in state.unfold: continue   # skip 'done' rules

            # create a version where we don't unfold the rule
            self._update(State(program, state.eureka, state.unfold | { r }, state.lct))

            for j, x in enumerate(r.body):

                if program.safe_inline(x):

                    first_appears = program
                    for s in reversed(list(program.lineage())):
                        if s.is_item(x):
                            first_appears = s
                            break

                    q = program.unfold(i, j, defs=first_appears)
                    self._update(State(q, state.eureka, state.unfold | { r }, state.lct))

            return

    def _drive_eureka(self, state):

        # [2023-03-24 Fri] try to cut back on crummy eurekas.  I think there are
        # some eurekas that provably can't help.  For example an eureka that has
        # space complexity that is larger than the best degree so far.
        #
        # this won't prevent the very strange phenomenon below:
        #
        #   edgeedge(J) += edge(start,$J1) * edge($J1,J).
        #   edgeedgeedge(J) += edgeedge($J1) * edge($J1,J).
        #   edgeedgeedgeedge(J) += edgeedgeedge($J1) * edge($J1,J).
        #   edgeedgeedgeedgeedge(J) += edgeedgeedgeedge($J1) * edge($J1,J).
        #   edgeedgeedgeedgeedgeedge(J) += edgeedgeedgeedgeedge($J1) * edge($J1,J).
        #     ⋮
        #
        # these edge⋯edge items are derived by variable-elimination eurekas
        # after unfolding.

        #
        # [2023-03-29 Wed] The code below immediate folds the new eureka into
        # the program rather than putting it on the agenda
        program = state.program
        for i, r in enumerate(program):
            if r in state.eureka: continue

            self._update(State(program, state.eureka | {r}, state.unfold, state.lct))   # skip this rule in eureka

            r = program.rules[i]

            a = r.analyzer

#            Fs = powerset(range(len(r.body)))
            Fs = {tuple(sorted(a.v2f[v])) for v in a.can_elim}   # Warning: proposal assume commutative products
            for js in Fs:
                tmp_rule = program.loop_absorption(i, js)
                rev_rule = Rule(r.head, tmp_rule.head, *[f for j,f in enumerate(r.body) if j not in js])
                new = program.define([tmp_rule]).basic_fold(rev_rule, j=0, S={i})
                self._update(State(new, state.eureka | {r}, state.unfold, state.lct))

            return

    def _drive_lct(self, state):

        # In order to control the branching factor in this transformation, we
        # will predict whether to slash each rule one at a time.
        p = state.program


        if state.lct is None:
            # pick a node?
            for x in p.coarse_nodes():
                if not p.is_item(x): continue
                #x = Var()
                self._update(State(p, state.eureka, state.unfold, (x, p, {})))
            return

        # for each rule, we can slash at most one of its subgoals
        x, ref, pos = state.lct

        found = False
        for r in ref:
            if r in pos: continue   # advance to the first rule not in the position vector
            found = True

            for j in [None] + [j for j, y in enumerate(r.body) if not ref.is_const(y) and not ref.is_builtin(y)]:

                pos1 = pos.copy()
                pos1[r] = j

                q = ref.lct(x, {ref.rules.index(r): j for r,j in pos1.items()})
                new = q.prune().abbreviate().prune().reset_transform_history()

                if 1:

                    print(colors.cyan % colors.line(80))
                    print(colors.cyan % 'params:', x, pos1)

                    print(colors.cyan % 'lct:', q.prune(specialize=0))
                    print(colors.cyan % 'specialized:', new)

                    print(colors.cyan % 'degrees:', new.degrees(), colors.mark(
                        new.degrees() < ref.degrees()
                    ))

                    if 0:
                        print(colors.cyan % 'correctness:', end=' ')
                        self.check(new, budget=5)

                    print(colors.cyan % colors.line(80))

                self._update(State(new, state.eureka, state.unfold, (x, ref, pos1)))


        if not found:

            # after the transformation is unleashed, we should clear the parameter

            self._update(State(state.program, state.eureka, state.unfold, None))

#            print("TRIGGERED!", q.prune(specialize=0))
#            print('--->', new)

    def _drive_slash(self, state):

        # In order to control the branching factor in this transformation, we
        # will predict whether to slash each rule one at a time.
        p = state.program


        # XXX: give speculation its own slot in the State
        if state.lct is None:
            # pick a node?
            for x in p.coarse_nodes():
                if not p.is_item(x): continue
                #x = Var()
                self._update(State(p, state.eureka, state.unfold, (x, p, {})))
            return

        # for each rule, we can slash at most one of its subgoals
        x, ref, pos = state.lct

        found = False
        for r in ref:
            if r in pos: continue   # advance to the first rule not in the position vector
            found = True

            for j in [None] + [jj for jj, y in enumerate(r.body) if not ref.is_const(y) and not ref.is_builtin(y)]:

                pos1 = pos.copy()
                pos1[r] = j

                Pos1 = {ref.rules.index(rr): jj for rr,jj in pos1.items()}

                q = ref.slash(x, Pos1)
                new = q.prune_fast().abbreviate().prune_fast().reset_transform_history()

                if 1:
#                if sum(1 for v in pos.values() if v is not None) > 1:

                    print(colors.cyan % colors.line(80))

                    print("SLASH SIZE:", sum(1 for v in pos.values() if v is not None))


                    print(colors.cyan % 'params:', x, Pos1)

                    print(colors.cyan % 'ref:', ref)

                    print(colors.cyan % 'slash:', q.prune(specialize=0))
                    print(colors.cyan % 'specialized:', new)

                    print(colors.cyan % 'degrees:', ref.abbreviate().prune().degrees(), colors.arrow.right, new.degrees(), colors.mark(
                        new.degrees() < ref.degrees()
                    ))

                    if 0:
                        print(colors.cyan % 'correctness:', end=' ')
                        self.check(new, budget=5)

                    print(colors.cyan % colors.line(80))


                new_state = State(new, state.eureka, state.unfold, (x, ref, pos1))
                self._update(new_state)

            return


        if not found:

            # after the transformation is unleashed, we should clear the parameter

            self._update(State(state.program, state.eureka, state.unfold, None))

#            print("TRIGGERED!", q.prune(specialize=0))
#            print('--->', new)


    def _drive_slash_XXX(self, state):

        # [2023-03-30 Thu] My proposal for proposing speculation actions: pick a
        # *pair* of "subtask", i.e., two sets of items a numerator and a
        # denominator, then consider all subsets/positions that connect the
        # numerator set to the denominator set.
        strategy = state.program
        for num in strategy.coarse_nodes():
            if strategy.is_item(num):

                positions = []
                for r in strategy:
                    positions.append([None] + [
                        j for j, b in enumerate(r.body)
                        if unifies(r.head, num)
                    ])

                for pos in product(*positions):

                    # pick on the the subgoals that is actually slashed here
                    dens = MostGeneralSet([r.body[j] for r,j in zip(strategy, pos) if j is not None], covers)

                    for den in dens:
                        print('!', end='')

                        q = strategy.slash(fresh(den), dict(enumerate(pos))) #prune(specialize=0)

                        # TODO: this is a crude way to check for a "useless speculation" (i.e., one that doesn't create any slashed items other than the base case)

                        #qq = q.tidy().sort()
                        qq = q.elim(0).prune_fast().sort()

                        if not any((r.head.fn == q.slash_fn) for r in qq):

                            print('x', end='')

                            continue

                        else:
                            #print('slash:', num, den)
                            #print('raw:', q.sort())
                            #print('tidied:', qq)

                            try:
                                with timelimit(1):
                                    qqq = qq.abbreviate().prune_fast()
                            except timelimit.Timeout:
                                print(colors.timeout)
                                continue

                            #print(strategy.degrees(), colors.rightarrow, qq.degrees())

                            if qqq.degrees() <= strategy.degrees():

                                print(strategy.degrees(), colors.rightarrow, qqq.degrees())

                                #print(colors.orange % colors.line(100))
                                #print(colors.orange % 'slash:', num, den)
                                #print(colors.orange % 'raw:', q.sort().prune())
                                #print(colors.orange % 'tidied:', qqq)

                                self._update(State(q, state.eureka, state.unfold, state.lct))

#    def _drive_slash(self, state):
#        # [2023-03-30 Thu] My proposol for proposing speculation actions: pick a
#        # *pair* of "subtask", i.e., two sets of items a numerator and a
#        # denominator, then consider all subsets/positions that connect the
#        # numerator set to the denominator set.
#
#        # TODO: avoid rewrite/phrase but allow rewrite/rewrite
#        p = state.program
#        nnn = p.coarse_nodes()
#        for num in nnn:
#            if p.is_item(num):
#
#                # XXX: we have to put the subsets of previous rules into the state
#
#                positions = []
#                for r in p:
#                    positions.append([None] + [
#                        j for j, b in enumerate(r.body)
#                        if unifies(r.head, num)
#                    ])
#
#                for pos in product(*positions):
#
#
#                    # pick on the the subgoals that is actually slashed here
#                    dens = MostGeneralSet([r.body[j] for r,j in zip(p, pos) if j is not None], covers)
#
#                    dens = [dd for d in dens for dd in nnn.roots(d)]
#
#                    for den in dens:
#
#                        print('!', end='')
#
#                        q = p.slash(den, dict(enumerate(pos))) #prune(specialize=0)
#
#                        #qq = q.tidy().sort()
#                        qq = q.elim(0).prune_fast().sort()
#
#                        self._n_slash_proposals += 1
#
#                        if not any(r.head.fn == q.slash_fn
#                                   for r in qq):
#
#                            print('x', end='')
#
#                            self._n_slash_rejected += 1
#
#                            print(colors.yellow % 'slash rejection rate:', colors.percent(self._n_slash_rejected, self._n_slash_proposals))
#
#                            continue
#
#                        else:
#
#                            qqq = qq.abbreviate().prune()
#
#                            print(p.degrees(), colors.rightarrow, qq.degrees())
#
#                            if qq.degrees() <= p.degrees() :
#
#                                print(colors.orange % colors.line(100))
#                                print(colors.orange % 'slash:', num, den)
#                                print(colors.orange % 'raw:', q.sort().prune())
#                                print(colors.orange % 'tidied:', qqq)
#
#                                self._update(State(q, state.eureka, state.unfold, state.lct))


    def show_search_stats(self):
        print(colors.magenta % self.search_stats())
        #print(end="\r")
        print()

    def search_stats(self):
        return (f'nodes/sec {len(self.chart)/(time() - self._start_time):.1f} '
                f'pops={self.pops} {dict(self.pop_stats)} '
                f'agenda={len(self.agenda)} {dict(self.agenda_stats)} '
                f'measure fails: {colors.percentage(self._n_check_measure_fails, self._n_check_measure)}')
