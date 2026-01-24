#!/usr/bin/env python3
"""
CKY Parsing Benchmark: Rust vs Pure Python

CKY (Cocke-Kasami-Younger) is a classic dynamic programming algorithm for
parsing context-free grammars. This benchmark tests parsing performance
with varying sentence lengths and grammar sizes.

The Dyna formulation:
  phrase(X, I, K) += phrase(Y, I, J) * phrase(Z, J, K) * rewrite(X, Y, Z).
  phrase(X, I, J) += word(W, I, J) * rewrite(X, W).
"""

import time
import random
from collections import defaultdict

# Import Rust implementation
import dyna_rust


# ============================================================================
# Minimal Pure Python Implementation
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
# CKY Grammar and Sentence Generation
# ============================================================================

def create_grammar():
    """Create an ambiguous CFG in Chomsky Normal Form (CNF) for stress-testing.

    CNF rules have either:
    - A -> B C (two non-terminals)
    - A -> w (one terminal via lexicon)
    """
    # This grammar is intentionally ambiguous to stress-test the parser
    # PP attachment ambiguity creates exponential ambiguity

    grammar = {
        # Sentence rules
        ('S', 'NP', 'VP'): 1.0,

        # Noun phrase rules - PP attachment creates ambiguity
        ('NP', 'Det', 'N'): 0.3,
        ('NP', 'Det', 'NB'): 0.2,
        ('NP', 'NP', 'PP'): 0.25,     # PP attachment - KEY SOURCE OF AMBIGUITY
        ('NP', 'Adj', 'NP'): 0.15,    # Adjective modification
        ('NP', 'N', 'N'): 0.1,        # Noun compounds

        # Noun bar
        ('NB', 'Adj', 'N'): 0.5,
        ('NB', 'Adj', 'NB'): 0.3,
        ('NB', 'N', 'N'): 0.2,

        # Verb phrase rules - PP attachment creates ambiguity
        ('VP', 'V', 'NP'): 0.4,
        ('VP', 'VP', 'PP'): 0.3,      # PP attachment - KEY SOURCE OF AMBIGUITY
        ('VP', 'V', 'PP'): 0.2,
        ('VP', 'VP', 'NP'): 0.1,      # Extra ambiguity

        # Prepositional phrase
        ('PP', 'P', 'NP'): 1.0,
    }

    lexicon = {
        # Determiners
        ('Det', 'the'): 0.4,
        ('Det', 'a'): 0.3,
        ('Det', 'every'): 0.15,
        ('Det', 'some'): 0.15,

        # Nouns
        ('N', 'dog'): 0.08,
        ('N', 'cat'): 0.08,
        ('N', 'mat'): 0.08,
        ('N', 'man'): 0.08,
        ('N', 'woman'): 0.08,
        ('N', 'park'): 0.08,
        ('N', 'telescope'): 0.08,
        ('N', 'hill'): 0.08,
        ('N', 'time'): 0.08,
        ('N', 'book'): 0.08,
        ('N', 'table'): 0.1,
        ('N', 'room'): 0.1,

        # Verbs
        ('V', 'saw'): 0.2,
        ('V', 'chased'): 0.15,
        ('V', 'ate'): 0.15,
        ('V', 'put'): 0.15,
        ('V', 'read'): 0.15,
        ('V', 'found'): 0.2,

        # Prepositions - many options create more ambiguity
        ('P', 'on'): 0.15,
        ('P', 'in'): 0.15,
        ('P', 'with'): 0.15,
        ('P', 'near'): 0.15,
        ('P', 'under'): 0.15,
        ('P', 'by'): 0.15,
        ('P', 'at'): 0.1,

        # Adjectives
        ('Adj', 'big'): 0.2,
        ('Adj', 'small'): 0.2,
        ('Adj', 'red'): 0.2,
        ('Adj', 'old'): 0.2,
        ('Adj', 'new'): 0.2,
    }

    return grammar, lexicon


def generate_sentence(length):
    """Generate a sentence with PP attachment ambiguity.

    Classic PP attachment ambiguity: "saw the man with the telescope"
    - Did you use the telescope to see?
    - Did the man have the telescope?

    More PPs = exponentially more parses!
    """
    # Base sentence patterns that create PP attachment ambiguity
    if length <= 5:
        # Simple: "the dog saw the cat"
        return ['the', 'dog', 'saw', 'the', 'cat'][:length]

    # Build sentence with multiple PPs for maximum ambiguity
    # Pattern: Det N V Det N (P Det N)*

    sentence = ['the', 'man', 'saw', 'the', 'dog']

    # Add PP modifiers - each one doubles the ambiguity!
    preps = ['with', 'on', 'in', 'near', 'by', 'at', 'under']
    nouns = ['telescope', 'hill', 'park', 'table', 'book', 'room', 'mat']

    pp_count = 0
    while len(sentence) < length and pp_count < len(preps):
        # Add "P the N" pattern
        remaining = length - len(sentence)
        if remaining >= 3:
            sentence.extend([preps[pp_count % len(preps)], 'the', nouns[pp_count % len(nouns)]])
            pp_count += 1
        else:
            break

    return sentence[:length]


# ============================================================================
# Benchmark Functions
# ============================================================================

def create_rust_cky_program(grammar, lexicon, sentence):
    """Create CKY program using Rust types."""
    Term = dyna_rust.Term
    Rule = dyna_rust.Rule
    rules = []

    # Variables: X=0, Y=1, Z=2, I=3, J=4, K=5, W=6

    # Binary rule: phrase(X, I, K) += phrase(Y, I, J) * phrase(Z, J, K) * rewrite(X, Y, Z)
    rules.append(Rule(
        Term("phrase", Term.var(0), Term.var(3), Term.var(5)),
        [Term("phrase", Term.var(1), Term.var(3), Term.var(4)),
         Term("phrase", Term.var(2), Term.var(4), Term.var(5)),
         Term("rewrite", Term.var(0), Term.var(1), Term.var(2))]
    ))

    # Unary/lexical rule: phrase(X, I, J) += word(W, I, J) * rewrite(X, W)
    rules.append(Rule(
        Term("phrase", Term.var(0), Term.var(3), Term.var(4)),
        [Term("word", Term.var(6), Term.var(3), Term.var(4)),
         Term("rewrite", Term.var(0), Term.var(6))]
    ))

    # Add grammar rules as rewrite facts
    for (lhs, *rhs), prob in grammar.items():
        if len(rhs) == 2:
            rules.append(Rule.fact(
                Term("rewrite", Term.atom(lhs), Term.atom(rhs[0]), Term.atom(rhs[1]))
            ))
        elif len(rhs) == 1:
            rules.append(Rule.fact(
                Term("rewrite", Term.atom(lhs), Term.atom(rhs[0]))
            ))

    # Add lexicon as rewrite facts
    for (pos, word), prob in lexicon.items():
        rules.append(Rule.fact(
            Term("rewrite", Term.atom(pos), Term.atom(word))
        ))

    # Add word facts for the sentence
    for i, word in enumerate(sentence):
        rules.append(Rule.fact(
            Term("word", Term.atom(word), Term.int(i), Term.int(i + 1))
        ))

    return rules


def create_python_cky_program(grammar, lexicon, sentence):
    """Create CKY program using Python types."""
    rules = []

    # Variables: X=0, Y=1, Z=2, I=3, J=4, K=5, W=6

    # Binary rule: phrase(X, I, K) += phrase(Y, I, J) * phrase(Z, J, K) * rewrite(X, Y, Z)
    rules.append(PyRule(
        PyTerm("phrase", [PyVar(0), PyVar(3), PyVar(5)]),
        [PyTerm("phrase", [PyVar(1), PyVar(3), PyVar(4)]),
         PyTerm("phrase", [PyVar(2), PyVar(4), PyVar(5)]),
         PyTerm("rewrite", [PyVar(0), PyVar(1), PyVar(2)])]
    ))

    # Unary/lexical rule: phrase(X, I, J) += word(W, I, J) * rewrite(X, W)
    rules.append(PyRule(
        PyTerm("phrase", [PyVar(0), PyVar(3), PyVar(4)]),
        [PyTerm("word", [PyVar(6), PyVar(3), PyVar(4)]),
         PyTerm("rewrite", [PyVar(0), PyVar(6)])]
    ))

    # Add grammar rules as rewrite facts
    for (lhs, *rhs), prob in grammar.items():
        if len(rhs) == 2:
            rules.append(PyRule(
                PyTerm("rewrite", [lhs, rhs[0], rhs[1]]),
                []
            ))
        elif len(rhs) == 1:
            rules.append(PyRule(
                PyTerm("rewrite", [lhs, rhs[0]]),
                []
            ))

    # Add lexicon as rewrite facts
    for (pos, word), prob in lexicon.items():
        rules.append(PyRule(
            PyTerm("rewrite", [pos, word]),
            []
        ))

    # Add word facts for the sentence
    for i, word in enumerate(sentence):
        rules.append(PyRule(
            PyTerm("word", [word, i, i + 1]),
            []
        ))

    return rules


def benchmark_rust_cky(grammar, lexicon, sentence, iterations=3):
    """Benchmark Rust CKY implementation."""
    Term = dyna_rust.Term
    rules = create_rust_cky_program(grammar, lexicon, sentence)

    times = []
    for _ in range(iterations):
        solver = dyna_rust.Solver(rules)

        start = time.perf_counter()
        solver.solve()
        end = time.perf_counter()

        times.append(end - start)

    # Check if sentence parses (S spanning 0 to len)
    goal = Term("phrase", Term.atom("S"), Term.int(0), Term.int(len(sentence)))
    result = solver.lookup(goal)

    # Count chart items
    chart_size = solver.chart_size()

    return min(times), result is not None, chart_size


def benchmark_python_cky(grammar, lexicon, sentence, iterations=3):
    """Benchmark Python CKY implementation."""
    rules = create_python_cky_program(grammar, lexicon, sentence)

    times = []
    for _ in range(iterations):
        solver = PySolver(rules)

        start = time.perf_counter()
        solver.solve()
        end = time.perf_counter()

        times.append(end - start)

    # Check if sentence parses
    goal = PyTerm("phrase", ["S", 0, len(sentence)])
    result = solver.lookup(goal)

    chart_size = len(solver.chart)

    return min(times), result is not None, chart_size


def run_cky_benchmarks():
    """Run CKY parsing benchmarks with different sentence lengths."""
    print("=" * 75)
    print("CKY Parsing Benchmark: Rust vs Pure Python")
    print("=" * 75)
    print(f"{'Length':>8} {'Rust (ms)':>12} {'Python (ms)':>14} {'Speedup':>10} {'Chart':>10}")
    print("-" * 75)

    grammar, lexicon = create_grammar()

    # Test different sentence lengths
    lengths = [5, 8, 11, 14, 17, 20, 26, 32, 40, 50]

    for length in lengths:
        sentence = generate_sentence(length)

        # Run Rust benchmark
        rust_time, rust_parses, rust_chart = benchmark_rust_cky(grammar, lexicon, sentence)
        rust_ms = rust_time * 1000

        # Run Python benchmark (skip if too slow)
        if length <= 17:
            python_time, python_parses, python_chart = benchmark_python_cky(grammar, lexicon, sentence)
            python_ms = python_time * 1000
            speedup = python_time / rust_time if rust_time > 0 else float('inf')
        else:
            python_ms = float('inf')
            speedup = float('inf')

        if python_ms == float('inf'):
            print(f"{length:>8} {rust_ms:>12.3f} {'(skipped)':>14} {'>100x':>10} {rust_chart:>10}")
        else:
            print(f"{length:>8} {rust_ms:>12.3f} {python_ms:>14.3f} {speedup:>9.1f}x {rust_chart:>10}")

    print("-" * 75)
    print("\nNote: CKY parsing has O(n³) time complexity where n is sentence length.")
    print("Chart size grows as O(n² × |G|) where |G| is grammar size.")


if __name__ == "__main__":
    run_cky_benchmarks()
