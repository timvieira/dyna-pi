"""
These are old search methods for the more limited search space used in the

"Searching for More Efficient Dynamic Programs"
Tim Vieira, Ryan Cotterell, Jason Eisner
Findings of the Association for Computational Linguistics: EMNLP 2021
https://aclanthology.org/2021.findings-emnlp.322/

"""
import numpy as np
from time import time

from arsenal import colors
from arsenal.maths import argmin_random_tie
from arsenal.maths.combinatorics import powerset

from frozendict import frozendict
from orderedset import OrderedSet

from itertools import product

from dyna import Program, TransformedProgram, Rule, is_const, fresh, Define, ProgramCollection


class NoMoreEvals(Exception): pass
class OracleStop(Exception): pass


class Search:

    def __init__(self, name, G, program, reps, ORACLE_STOP, checkpoint,
                 benchmark = None, verbosity = 1, kill = False, run = True):
        self.i = 0
        self.name = name
        self.last_update = 0
        self.last_checkpoint = 0
        self.start_time = time()
        self.best = None
        self.best_cost = None
        self.verbosity = verbosity
        self.kill = kill

        self.G = G
        self.benchmark = benchmark
        self.program = program
        self.reps = reps        # XXX: consider other "budget" schemes, e.g.,
                                # total accumulated cost/time.

        self.log = []
        self.programs = {}

        if benchmark is None: ORACLE_STOP = False
        self.ORACLE_STOP = ORACLE_STOP
        self.checkpoint = checkpoint

        if run: self.go()

    def go(self):
        try:
            self.objective(self.program)   # must call in try to catch oracle stop
            self.run()

        except OracleStop:
            if self.verbosity > 0: print(colors.light.green % f'[{self.name}] oracle stop.')

        except NoMoreEvals:
            if self.verbosity > 0: print(colors.yellow % f'[{self.name}] no more evals')

        except KeyboardInterrupt as e:   # pragma: no cover
            if self.kill: raise e
            print('^C')
            print(f'[{self.name}] stopped early')

            if 0:
                import sys, traceback
                etype, evalue, tb = sys.exc_info()
                tb = '\n'.join(traceback.format_exception(etype, evalue, tb))
                print(colors.dark.white % '*'*80)
                print(colors.dark.white % tb)
                print(colors.dark.white % '*'*80)

    def run(self):
        raise NotImplementedError()

    def status(self):
        return ''

    def log_entry(self, p):
        return {}

    def objective(self, p):
        self.i += 1

        self.programs[self.i] = p

        cost = self.G.cost(p)
        now = time()
        x = dict(
            i = self.i,
            elapsed = now-self.start_time,
            cost = cost,
            degree = p.degree,         # XXX: (optional) move to log entry method
            degrees = p.degrees(),
            p_length = len(p.rules),
        )
        x.update(self.log_entry(p))
        self.log.append(x)
        if self.checkpoint is not None and (now - self.last_checkpoint) > 60:   # check point every couple minutes
            self.checkpoint(self)
            self.last_checkpoint = now

        # track best solution
        if self.best_cost is None or cost < self.best_cost:
            self.best = p
            self.best_cost = cost
            if self.verbosity > 0: print(f'[{colors.green % self.name}] i={self.i:,}{self.status()} improvement obj={cost}')
        else:
            if (now - self.last_update) > 1:
                self.last_update = now
                if self.verbosity > 0: print(f'[{colors.yellow % self.name}] i={self.i:,}{self.status()}')

        if self.ORACLE_STOP and self.benchmark.is_optimal(p, cost):
            raise OracleStop()

        if self.i >= self.reps:
            raise NoMoreEvals()

        return cost

    def __repr__(self):
        return f'{self.__class__.__name__} (cost={self.best_cost}) {self.best}'

    @property
    def collection(self):
        return ProgramCollection(self.programs.values())

    def top(self, K=None):
        for x in sorted(self.log, key=lambda x: x['cost'])[:K]:
            yield (x, self.programs[x['i']])

    def show_top(self, K=None):
        for rank, (log, p) in enumerate(self.top(K), start=1):
            print()
            print(colors.cyan % ('#' + '_'*80))
            print(colors.cyan % f'# {rank}')
            print(log)
            p.show_transforms()
            print(p)


class BeamSearch(Search):
    def __init__(
        self,
        G,
        program,
        reps,
        beam_size,
        benchmark = None,
        ORACLE_STOP = True,
        checkpoint = None,
        verbosity = 1,
        kill = False,
    ):
        self.depth = 0
        assert beam_size is not None
        self.beam_size = beam_size

        super().__init__(
            name = 'beam',
            G = G,
            program = program,
            benchmark = benchmark,
            reps = reps,
            ORACLE_STOP = ORACLE_STOP,
            checkpoint = checkpoint,
            verbosity = verbosity,
            kill = kill,
        )

    def status(self):
        return f' depth={self.depth}'

    def log_entry(self, p):
        return dict(depth=self.depth)

    def run(self):
        G = self.G
        x = G.initial_state
        beam = [(self.objective(x.program),x)]
        self.depth = 0
        while beam:
            self.depth += 1
            b = []
            for _,x in beam:
                for a in G.actions(x):
                    y = G.transition(x, a)
                    c = self.objective(y.program)
                    b.append((c, y))
            beam = sorted(b, key = lambda cy: cy[0])[:self.beam_size]
        if self.verbosity > 0: print(colors.cyan % '[beam] beam is empty')



class GraphInterface:
    def __init__(self, initial_state, cost, State):
        self.cost = cost
        self._State = State
        self.initial_state = self.State(**initial_state)
    def transition(self, s, a):
        raise NotImplementedError()
    def actions(self, s):
        raise NotImplementedError()
    def State(self, *args, **kwargs):
        return self._State(*args, **kwargs)


class Action:
    def __init__(self, method, args):
        self.method = method
        self.args = args
    def __call__(self):
        return self.method(*self.args)
    def __repr__(self):
        # fix annoyance that frozensets print uglier the regular sets.
        args = [x if not isinstance(x, frozenset) else set(x) for x in self.args]
        return f'{self.method.__name__}{args}'
    def tuple(self):
        return (self.method.__name__, *self.args)
    def __eq__(self, other):
        return self.tuple() == other.tuple()
    def __hash__(self):
        return hash(self.tuple())
    def __lt__(self, other):
        return self.tuple() < other.tuple()


class MacroFold(Action):
    def __init__(self, graph, program, i):
        self.graph = graph
        self.program = program
        self.i = i
    def __repr__(self):
        return f'MacroFold[{self.i}]'
    def tuple(self):
        return ('macro_fold', self.i)
    def __call__(self, ):
        r_ix = self.i
        program = self.program
        rule_states = self.graph.rule_states
        r = program.rules[r_ix]
        key = r
        self.graph.n_macro_fold_lookup  += 1
        if key not in rule_states:
            init = Program(
                [r],
                inputs = Program([Rule(fresh(x)) for x in r.body if not is_const(x)]),
                outputs = Program([Rule(fresh(r.head))]),
            )
            rule_states[key] = init.beam(100_000, 100, verbosity=0, kill=True, cost=self.graph.cost, TRANSFORMS=['fold']).best
        else:
            self.graph.n_macro_fold_success += 1
        #print(f'success: {self.graph.n_macro_fold_success/self.graph.n_macro_fold_lookup:.2%}')
        sol = rule_states[key]
        new_program = list(program)
        new_program.pop(r_ix)
        new_program.extend(sol)
        return TransformedProgram(('fold*', r_ix), program, new_program)


def halt(): pass

# Note: evaluating a state is optional, some algorithms use synthetic
# evaluations and surrogate cost to improve the overall "sample complexity"
# of search or whatever.

class State1:
    def __init__(self, program, depth):
        self.program = program
        self.depth = depth

    def __repr__(self):
        return f'State1({self.program})'

    def __eq__(self, other):
        return self.program == other.program

    def __hash__(self):
        return hash(self.program)


class Graph1(GraphInterface):

    def __init__(self, src, max_depth, TRANSFORMS, cost, tidy=True):
        self.src = src
        self.tidy = tidy

        self.rule_states = {}
        self.n_macro_fold_lookup = 0
        self.n_macro_fold_success = 0

        self.max_depth = max_depth
        self.TRANSFORMS = TRANSFORMS

        super().__init__(
            initial_state = dict(
                program = src,
                depth = 0
            ),
            cost = cost,
            State = State1,
        )

        # Check for spelling mistakes
        SUPPORTED = {'noop', 'megafold', 'megafold-defs', 'fold', 'fold+',
                     'fold*', 'lct',
                     'spec', 'elim', 'unfold'}
        assert set(TRANSFORMS) <= SUPPORTED, set(TRANSFORMS)-SUPPORTED


    # TODO: retire this method
    #
    # [2022-01-31 Mon]: This method will soon be retired in favor of
    # safe-megafold since safe megafold can use any definition that it likes -
    # not just "oneliners" that we introduced by folds. (Note that oneliners are
    # a special case in the fold/unfold literature that goes back to the seminal
    # T&S'84 paper so it makes sense that we started there too! They are alos
    # much faster to pattern match for since its just only permutation not two!)
    def find_defs(self, p):
        ds = []
        for x in p.transforms():
            # TODO: For consistency, both `Fold` and `CSE` below should use
            # `Define` instead to introduce their new rules.
            if isinstance(x, Define): ds.extend(x.defs)
        return ds

    def actions(self, s):

        if s.depth >= self.max_depth:
            return []

        p = s.program

        actions = [Action(halt, [])]

        if 'noop' in self.TRANSFORMS:
            actions.append(Action(p.noop, []))

        if 'spec' in self.TRANSFORMS:
            # for each rule, we can slash at most one of its subgoals
            positions = []
            for r in p:
                positions.append([None] + [
                    j for j, b in enumerate(r.body)
                ])

            for pos in product(*positions):
                q = p.slash('X', dict(enumerate(pos))).prune()
                actions.append(Action(q.noop, []))

        if 'lct' in self.TRANSFORMS:
            # for each rule, we can slash at most one of its subgoals
            positions = []
            for r in p:
                positions.append([None] + [
                    j for j, b in enumerate(r.body)
                ])
            for pos in product(*positions):
                q = p.lct(dict(enumerate(pos))).prune()
                actions.append(Action(q.noop, []))

        if 'megafold' in self.TRANSFORMS:
            for q in p.reversible_megafolds():
                actions.append(Action(q.noop, []))

        if 'megafold-defs' in self.TRANSFORMS:
            defs = self.find_defs(p)
            if defs:
                for q in p.megafolds(defs=Program(defs)):
                    actions.append(Action(q.noop, []))

        for i,r in enumerate(p):

            a = r.analyzer

            # XXX: can cache the available actions in the rule analyzers

            # fold
            Fs = {frozenset(a.v2f[v]) for v in a.can_elim}
            if 'fold' in self.TRANSFORMS:
                for fs in Fs:
                    actions.append(Action(p.hook, [i, fs]))

            if 'fold+' in self.TRANSFORMS:
                for fs in powerset(range(len(r.body))):
                    actions.append(Action(p.hook, [i, fs]))

            if 'fold*' in self.TRANSFORMS:
                if r.analyzer.can_elim:
                    actions.append(MacroFold(self, p, i))

            if 'elim' in self.TRANSFORMS:
                # rule elimination
                if not p.is_output(r.head):
                    actions.append(Action(p.elim, [i]))

            if 'unfold' in self.TRANSFORMS:
                # unfold
                for j in range(len(r.body)):
                    if p.safe_inline(r.body[j]):
                        actions.append(Action(p.unfold, [i, j]))

        return actions

    def post_process(self, program):
        if self.tidy: return program.prune_fast()
        return program

    def transition(self, s, a):

        assert s.depth <= self.max_depth, [a, self.actions(s), s]

        new_program = a()
        if new_program is None:
            next_state = self.State(
                program = s.program,
                depth = self.max_depth+1,
            )
            return next_state

        new_program = self.post_process(new_program)

        #print()
        #print(a)
        #s.program.compare(new_program)
        #new_program = new_program.eliminate_constant_rules()

        next_state = self.State(
            program = new_program,
            depth = s.depth + 1,
        )

        return next_state


class State2:
    def __init__(self, program, todo, depth):
        self.program = program
        self.todo = todo
        self.depth = depth
        self._ds = self.program.degrees()   # serves as program sketch as well as objective function
    def __repr__(self):
        todo = self.todo_ix()
        return f'State2({todo}, {self.program})'
    def todo_ix(self):
        todo = []
        for r_ in self.todo:
            found = [i for i, r in enumerate(self.program) if r == r_]
            todo.append(found[0])
        return sorted(todo)
    def __hash__(self):
        return hash(self._ds)    # might not be a great hash
    def __eq__(self, other):
        # XXX: the todo list won't hash equal if the vars in the rules are
        # different
        return self.todo == other.todo and self.program.same(other.program)


class Graph2(GraphInterface):

    def __init__(self, src, max_depth, TRANSFORMS, cost, tidy=True):
        self.src = src

        self.rule_states = {}
        self.n_macro_fold_lookup = 0
        self.n_macro_fold_success = 0

        self.tidy = tidy
        self.max_depth = max_depth
        self.TRANSFORMS = TRANSFORMS

        # Check for spelling mistakes
        SUPPORTED = {'noop', 'fold', 'fold+',
                     'fold*', 'elim', 'unfold'}
        assert set(TRANSFORMS) <= SUPPORTED, set(TRANSFORMS)-SUPPORTED

        super().__init__(
            initial_state = dict(
                program = src,
                todo = OrderedSet(src),
                depth = 0
            ),
            cost = cost,
            State = State2,
        )

    def rule_index(self, state):
        #r_ = self.find_bottleneck(state.todo)
        r_ = list(state.todo)[0]
        # ugly: there might be duplicate rules, just take the first one.
        assert r_ in state.program
        found = [i for i, r in enumerate(state.program) if r == r_]
        return found[0]

    def actions(self, state):

        if not state.todo or state.depth >= self.max_depth:
            return []

        p = state.program
        i = self.rule_index(state)

        actions = [Action(p.noop, [])]

        r = p.rules[i]
        a = r.analyzer

        # fold
        Fs = {frozenset(a.v2f[v]) for v in a.can_elim}
        if 'fold' in self.TRANSFORMS:
            for fs in Fs:
                actions.append(Action(p.hook, [i, fs]))

        if 'fold+' in self.TRANSFORMS:
            for fs in powerset(range(len(r.body))):
                actions.append(Action(p.hook, [i, fs]))

        if 'fold*' in self.TRANSFORMS:
            if a.can_elim:
                actions.append(MacroFold(self, p, i))

        if 'elim' in self.TRANSFORMS:
            # rule elimination
            if not p.is_output(r.head):
                actions.append(Action(p.elim, [i]))

        if 'unfold' in self.TRANSFORMS:
            # unfold
            for j in range(len(r.body)):
                if p.safe_inline(r.body[j]):
                    actions.append(Action(p.unfold, [i, j]))

        return actions

    def post_process(self, program):
        if self.tidy: return program.prune_fast()
        return program

    def transition(self, state, action):
        assert state.todo and state.depth <= self.max_depth, [action, self.actions(state), state]
        new_program = action()
        new_program = self.post_process(new_program)
        return self.State(
            program = new_program,
            todo = self.update_todo(state, new_program),
            depth = state.depth + 1,
        )

    def update_todo(self, state, new_program):
        r = state.program.rules[self.rule_index(state)]
        todo = state.todo - {r}
        old = OrderedSet(state.program)
        new = OrderedSet(new_program)
        # removals
        todo -= (old - new)
        # additions
        todo |= (new - old)
        return todo


if __name__ == '__main__':
    from arsenal.testing_framework import testing_framework
    testing_framework(globals())
