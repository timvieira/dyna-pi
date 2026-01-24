#!/usr/bin/env python3
"""
Benchmark comparing Rust vs Pure Python implementations of the Dyna solver.
"""

import time
from collections import defaultdict

# Import Rust implementation
import dyna_rust


# ============================================================================
# Minimal Pure Python Implementation for Comparison
# ============================================================================

class PyTerm:
    """Simple term representation."""
    __slots__ = ('functor', 'args', '_hash')

    def __init__(self, functor, args):
        self.functor = functor
        self.args = tuple(args)
        self._hash = hash((functor, self.args))

    def __hash__(self):
        return self._hash

    def __eq__(self, other):
        return (isinstance(other, PyTerm) and
                self.functor == other.functor and
                self.args == other.args)

    def __repr__(self):
        if not self.args:
            return self.functor
        return f"{self.functor}({', '.join(map(str, self.args))})"

    def is_ground(self):
        return all(not isinstance(a, PyVar) for a in self.args)


class PyVar:
    """Variable in a term."""
    __slots__ = ('id',)

    def __init__(self, id):
        self.id = id

    def __hash__(self):
        return hash(('$var', self.id))

    def __eq__(self, other):
        return isinstance(other, PyVar) and self.id == other.id

    def __repr__(self):
        return f"_{self.id}"


class PySubst:
    """Substitution mapping variables to terms."""

    def __init__(self):
        self.bindings = {}
        self.next_var = 0

    def fresh_var(self):
        v = self.next_var
        self.next_var += 1
        return v

    def deref(self, term):
        if isinstance(term, PyVar):
            if term.id in self.bindings:
                return self.deref(self.bindings[term.id])
            return term
        elif isinstance(term, PyTerm):
            return PyTerm(term.functor, [self.deref(a) for a in term.args])
        else:
            return term

    def bind(self, var_id, term):
        self.bindings[var_id] = term

    def mgu(self, x, y):
        """Most general unifier. Returns True on success."""
        x = self.deref(x)
        y = self.deref(y)

        if x == y:
            return True

        if isinstance(x, PyVar):
            self.bindings[x.id] = y
            return True

        if isinstance(y, PyVar):
            self.bindings[y.id] = x
            return True

        if isinstance(x, PyTerm) and isinstance(y, PyTerm):
            if x.functor != y.functor or len(x.args) != len(y.args):
                return False
            for a, b in zip(x.args, y.args):
                if not self.mgu(a, b):
                    return False
            return True

        return x == y

    def copy(self):
        s = PySubst()
        s.bindings = self.bindings.copy()
        s.next_var = self.next_var
        return s


class PyRule:
    """A rule: head += body[0] * body[1] * ..."""

    def __init__(self, head, body):
        self.head = head
        self.body = body

    def fresh(self, subst):
        """Freshen variables in this rule."""
        var_map = {}

        def freshen(term):
            if isinstance(term, PyVar):
                if term.id not in var_map:
                    var_map[term.id] = PyVar(subst.fresh_var())
                return var_map[term.id]
            elif isinstance(term, PyTerm):
                return PyTerm(term.functor, [freshen(a) for a in term.args])
            else:
                return term

        return PyRule(freshen(self.head), [freshen(b) for b in self.body])


class PySolver:
    """Pure Python forward-chaining solver."""

    def __init__(self, rules):
        self.rules = rules
        self.chart = {}
        self.change = {}
        self.agenda = []
        self.subst = PySubst()
        self.subst.next_var = 1000

        # Build driver index
        self.driver_index = defaultdict(list)
        for rule_idx, rule in enumerate(rules):
            for subgoal_idx, subgoal in enumerate(rule.body):
                if isinstance(subgoal, PyTerm):
                    key = (subgoal.functor, len(subgoal.args))
                    self.driver_index[key].append((rule_idx, subgoal_idx))

    def update(self, item, delta):
        if delta == 0:
            return

        if item in self.change:
            self.change[item] += delta
        else:
            self.change[item] = delta
            self.agenda.append(item)

    def solve(self):
        # Initialize facts
        for rule in self.rules:
            if not rule.body:
                self.update(rule.head, 1.0)

        # Process agenda
        while self.agenda:
            item = self.agenda.pop(0)
            delta = self.change.pop(item, None)
            if delta is None:
                continue

            old = self.chart.get(item, 0.0)
            new = old + delta

            if abs(new - old) < 1e-10:
                continue

            self.chart[item] = new
            self.drive_rules(item, delta)

    def drive_rules(self, item, delta):
        key = (item.functor, len(item.args))
        drivers = self.driver_index.get(key, [])

        for rule_idx, subgoal_idx in drivers:
            rule = self.rules[rule_idx].fresh(self.subst)
            subgoal = rule.body[subgoal_idx]

            subst = PySubst()
            if not subst.mgu(item, subgoal):
                continue

            self.join_body(rule, 0, subst, 1.0, subgoal_idx, item, delta)

    def join_body(self, rule, idx, subst, accum, trigger_idx, trigger_item, trigger_delta):
        if idx >= len(rule.body):
            head = subst.deref(rule.head)
            if head.is_ground():
                self.update(head, accum)
            return

        subgoal = subst.deref(rule.body[idx])

        if idx == trigger_idx:
            new_subst = subst.copy()
            if new_subst.mgu(subgoal, trigger_item):
                new_accum = accum * trigger_delta
                self.join_body(rule, idx + 1, new_subst, new_accum,
                             trigger_idx, trigger_item, trigger_delta)
            return

        # Query chart for matches
        for chart_item, value in self.chart.items():
            if not isinstance(chart_item, PyTerm):
                continue
            if chart_item.functor != subgoal.functor:
                continue
            if len(chart_item.args) != len(subgoal.args):
                continue

            new_subst = subst.copy()
            if new_subst.mgu(subgoal, chart_item):
                new_accum = accum * value
                self.join_body(rule, idx + 1, new_subst, new_accum,
                             trigger_idx, trigger_item, trigger_delta)

    def lookup(self, term):
        return self.chart.get(term)


# ============================================================================
# Benchmark Functions
# ============================================================================

def create_rust_program(n_edges):
    """Create a transitive closure program using Rust types."""
    Term = dyna_rust.Term
    Rule = dyna_rust.Rule
    rules = []

    # path(X, Y) += edge(X, Y)
    rules.append(Rule(
        Term("path", Term.var(0), Term.var(1)),
        [Term("edge", Term.var(0), Term.var(1))]
    ))

    # path(X, Z) += edge(X, Y) * path(Y, Z)
    rules.append(Rule(
        Term("path", Term.var(0), Term.var(2)),
        [Term("edge", Term.var(0), Term.var(1)),
         Term("path", Term.var(1), Term.var(2))]
    ))

    # Add edge facts (linear chain: 1->2->3->...->n)
    for i in range(1, n_edges + 1):
        rules.append(Rule.fact(
            Term("edge", Term.int(i), Term.int(i + 1))
        ))

    return rules


def create_python_program(n_edges):
    """Create a transitive closure program using Python types."""
    rules = []

    # path(X, Y) += edge(X, Y)
    rules.append(PyRule(
        PyTerm("path", [PyVar(0), PyVar(1)]),
        [PyTerm("edge", [PyVar(0), PyVar(1)])]
    ))

    # path(X, Z) += edge(X, Y) * path(Y, Z)
    rules.append(PyRule(
        PyTerm("path", [PyVar(0), PyVar(2)]),
        [PyTerm("edge", [PyVar(0), PyVar(1)]),
         PyTerm("path", [PyVar(1), PyVar(2)])]
    ))

    # Add edge facts (linear chain: 1->2->3->...->n)
    for i in range(1, n_edges + 1):
        rules.append(PyRule(
            PyTerm("edge", [i, i + 1]),
            []
        ))

    return rules


def benchmark_rust(n_edges, iterations=3):
    """Benchmark Rust implementation."""
    Term = dyna_rust.Term
    rules = create_rust_program(n_edges)

    times = []
    for _ in range(iterations):
        solver = dyna_rust.Solver(rules)

        start = time.perf_counter()
        solver.solve()
        end = time.perf_counter()

        times.append(end - start)

    # Verify correctness
    path_1_n = Term("path", Term.int(1), Term.int(n_edges + 1))
    result = solver.lookup(path_1_n)

    return min(times), result is not None


def benchmark_python(n_edges, iterations=3):
    """Benchmark Python implementation."""
    rules = create_python_program(n_edges)

    times = []
    for _ in range(iterations):
        solver = PySolver(rules)

        start = time.perf_counter()
        solver.solve()
        end = time.perf_counter()

        times.append(end - start)

    # Verify correctness
    result = solver.lookup(PyTerm("path", [1, n_edges + 1]))

    return min(times), result is not None


def run_benchmarks():
    """Run benchmarks with different problem sizes."""
    print("=" * 70)
    print("Transitive Closure Benchmark: Rust vs Pure Python")
    print("=" * 70)
    print(f"{'Edges':>8} {'Rust (ms)':>12} {'Python (ms)':>14} {'Speedup':>10} {'Correct':>10}")
    print("-" * 70)

    sizes = [10, 20, 50, 100, 200, 500, 1000]

    for n in sizes:
        # Run Rust benchmark
        rust_time, rust_correct = benchmark_rust(n)
        rust_ms = rust_time * 1000

        # Run Python benchmark (skip if too slow)
        if n <= 100:
            python_time, python_correct = benchmark_python(n)
            python_ms = python_time * 1000
            speedup = python_time / rust_time
            correct = "✓" if (rust_correct and python_correct) else "✗"
        else:
            python_ms = float('inf')
            speedup = float('inf')
            correct = "✓" if rust_correct else "✗"

        if python_ms == float('inf'):
            print(f"{n:>8} {rust_ms:>12.3f} {'(skipped)':>14} {'>100x':>10} {correct:>10}")
        else:
            print(f"{n:>8} {rust_ms:>12.3f} {python_ms:>14.3f} {speedup:>9.1f}x {correct:>10}")

    print("-" * 70)
    print("\nNote: Transitive closure on a chain of N edges produces O(N²) paths.")
    print("The Rust implementation uses indexed chart lookups for efficiency.")


if __name__ == "__main__":
    run_benchmarks()
