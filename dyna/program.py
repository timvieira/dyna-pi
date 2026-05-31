"""
Programs and their associated methods.
"""

import numpy as np
from arsenal import colors
from collections import defaultdict
from functools import cached_property, wraps
from itertools import count, combinations
from semirings import base, Float

from dyna.builtin import (
    Builtins, BuiltinConstaint, NotMatchesConstaint, cmps, is_builtin,
)
from dyna import syntax
from dyna.pretty import PrettyPrinter, pp, Escape
from dyna.rule import Rule, is_const
from dyna.term import (
    fresh, Var, unify, snap, Term, unifies, term_vars, covers, gen_functor,
    is_ground, canonicalize, is_var, Product, flatten_op, FreshCache,
    deref, join_f, NoDupsSet,
    Stream, ResultStream, Constant
)
from dyna.util import FrozenBag, tarjan, instance_cache, InstanceCache
from dyna.util.bucket_queue import BucketQueue
from dyna.util import OrderedSet
from dyna.exceptions import DynaParserException


class CostDegrees(tuple):
    def __mul__(self, other):
        return CostDegrees(tuple(reversed(sorted([*self, *other]))))
    def __repr__(self):
        return '∅' if len(self) == 0 else f'{":".join(map(str, self))}'


inf = float('inf')


def _parse(rules, inputs=None, outputs=None):
    if rules == '': return [[], inputs, outputs]  # for efficiency, skip call to `parse`.
    assert isinstance(rules, str)
    rules_ = []; inputs_ = []; outputs_ = []
    for r in syntax.parser(rules):
        if isinstance(r.head, Term) and r.head.fn == '$declare':
            [x] = r.head.args
            if x.fn in {'input', 'inputs', 'params', 'param'}:
                [y] = x.args
                inputs_.extend(Rule(z) for z in flatten_op(y, ';') if z is not None)
            elif x.fn in {'output', 'outputs'}:
                [y] = x.args
                outputs_.extend(Rule(z) for z in flatten_op(y, ';') if z is not None)
            else:   # pragma: no cover
                raise ValueError(f'unrecognized declaration: {x.fn}')
        else:
            rules_.append(r)
    if inputs_ or outputs_:
        if inputs is None: inputs = Program(inputs_)
        if outputs is None: outputs = Program(outputs_)
    return [rules_, inputs, outputs]


def to_collection(f):
    @wraps(f)
    def wrapper(*args, **kwargs):
        return ProgramCollection(list(f(*args, **kwargs)))
    return wrapper


def _subgoal_sort_key(x):
    """Total order on body subgoals, used by `ConstantFolded` to put
    bodies into a canonical order before bucketing (so that rules
    differing only in multiplicative reordering — `*` is commutative —
    merge). Falls back to a string repr when subgoals don't expose a
    structural signature.
    """
    try:
        return ('term', repr(canonicalize(x)) if isinstance(x, Term) else repr(x))
    except TypeError:
        return ('opaque', repr(x))


class Program:

    parent = None   # root programs have no parent; TransformedProgram sets it per-instance

    def __init__(self, rules='', inputs=None, outputs=None, semiring=None, has_builtins=True):
        if isinstance(rules, str):
            try:
                rules, inputs, outputs = _parse(rules, inputs, outputs)
            except DynaParserException as e:
                raise DynaParserException(e) from None

        self.rules = list(rules)
        assert all(isinstance(r, Rule) for r in rules), rules

        self.set_input_types(inputs)
        self.set_output_types(outputs)

        self._caches = InstanceCache()

        self.semiring = semiring
        self.has_builtins = has_builtins

        self._cache_f2r = None
        self._buckets = None
        self.root = self

        self._fresh = FreshCache()

    def set_input_types(self, inputs):
        if isinstance(inputs, str): inputs = Program(inputs)
        assert inputs is None or isinstance(inputs, Program), inputs
        self.inputs = inputs
        return self

    def set_output_types(self, outputs):
        if isinstance(outputs, str): outputs = Program(outputs)
        assert outputs is None or isinstance(outputs, Program), outputs
        self.outputs = outputs
        return self

    def spawn(self, rules=''):
        "Create an empty program with the same 'metadata' as this one."
        return Program(rules = rules,
                       inputs = self.inputs,
                       outputs = self.outputs,
                       semiring = self.semiring,
                       has_builtins = self.has_builtins)

    #___________________________________________________________________________
    # CACHED STUFF

    @cached_property
    def builtins(self):
        assert self.has_builtins
        return Builtins(self)

    @cached_property
    def signature(self):
        """
        Compute a signature for the entire program based on its rules.

        This signature is invariant to rule re-ordering, and inherits the
        invariances of the `rule_signature`.
        """
        return FrozenBag(r.signature for r in self)

    def just_heads(self):
        return [r.head for r in self]

    #___________________________________________________________________________
    #

#    def tight_repr(self, **kwargs):
#        return self.__repr__(
#            **{**dict(numbered=False, indent='', open_brace='', close_brace=''),
#               **kwargs},
#        )

    def __repr__(self, color=True, numbered=True, sep='\n',
                 indent='  ', open_brace='{', close_brace='}', pp=pp):
        lines = []
        if open_brace is not None: lines.append(open_brace)
        for i, r in enumerate(self):

            #if color:
            #    from dyna.pretty import Escape
            #    r = Rule(r.head, *[
            #        Term(Escape(colors.purple % y.fn), *y.args) if self.is_input(y) else y
            #        for y in r.body
            #    ])

            _r = pp(r, color=color)
            lines.append(f'{indent}{i}: {_r}.' if numbered else f'{indent}{_r}.')
        if close_brace is not None: lines.append(close_brace)
        return sep.join(lines)

    # TODO: this method ought to maintain the input/output annotations.
    # TODO: this method needs a way to serialize semiring values
    # TODO: this method needs to save its semiring
    # TODO: I think our best bet is to use pickle for general serialization, rather than this DIY string representation,
    # but the DIY string representation is fine for common cases, I suppose.
    def plaintext(self):
        lines = [f'{pp(r, color=False)}.' for r in self]
        if self.inputs:
            lines.append('input: ' + '; '.join(pp(x, color=False) for x in self.inputs) + '.')
        if self.outputs:
            lines.append('output: ' + '; '.join(pp(x, color=False) for x in self.outputs) + '.')
        return '\n'.join(lines)

#    def _repr_html_(self):
#        return '<table>' + '\n'.join(f'<tr><td>{i}</td><td style="text-align: left; font-family: Monospace;">%s.</td></tr>' % pp(r) for i, r in enumerate(self)) + '</table>'

#    def _repr_html_(self):
#        from pygments.formatters import HtmlFormatter
#        from pygments.lexers import PythonLexer
#        from pygments import highlight
#        from IPython.display import HTML
#
#        code = '\n'.join(pp(r, color=False) + '.' for r in self)
#
#        output = HTML(highlight(code, PythonLexer(), HtmlFormatter(full=True, linenos=True))).data
#
#        output = output.replace(
#            '<pre>',
#            '<pre style="text-align:left;">'
#        ).replace(
#            '<td class="linenos">',
#            '<td class="linenos" style="padding-right: 10px; text-align: right; color: #333;">'
#        )
#
#        return output


    # CSS color for input subgoals highlighted inline in rule bodies.  Inputs
    # are exogenous (see `is_exogenous`), so a distinct purple sets them apart
    # from local items (default), variables (green), and the aggregator (blue).
    html_input_color = '<span style="color: #7b2fbe;">%s</span>'

    # Class-level switch controlling whether `_repr_html_` (the representation
    # Jupyter renders automatically) folds in the input/output declarations.
    # Set `Program.show_types_in_html = False` to suppress them globally, or
    # call `p.to_html(types=False)` for a one-off.
    show_types_in_html = True

    def _repr_html_(self):
        return self.to_html(types=self.show_types_in_html)

    def to_html(self, types=True):
        """Render the program as HTML.

        Input subgoals are highlighted inline in the rule bodies (see
        `html_input_color`).  When `types` is true and the program carries input
        and/or output declarations, those are appended in a single collapsible
        `<details>` block (collapsed by default, so it stays out of the way until
        expanded).  Because `inputs`/`outputs` are themselves `Program`s -- which
        may carry rule bodies, delayed constraints, and even their own
        declarations -- each is rendered by recursing into this same method, so
        arbitrarily general declaration programs display correctly.
        """
        html = self._html_code_block()
        if types and (self.inputs or self.outputs):
            html += self._html_types_section()
        return html

    def _highlight_inputs(self, r):
        """Return a copy of rule `r` whose input subgoals are colored.

        The functor is wrapped in an `Escape` (which `pp` emits verbatim) so the
        arguments still pretty-print normally; arity-0 subgoals are emitted as a
        bare `Escape` to avoid a spurious `foo()`.  Returns `r` unchanged when it
        has no input subgoals.
        """
        if self.inputs is None: return r
        body, changed = [], False
        for y in r.body:
            if isinstance(y, Term) and self.is_input(y):
                changed = True
                colored = self.html_input_color % str(snap(y.fn))
                body.append(Term(Escape(colored), *y.args) if y.args else Escape(colored))
            else:
                body.append(y)
        return Rule(r.head, *body) if changed else r

    def _html_code_block(self):
        "The line-numbered, syntax-colored block of rules, inputs highlighted."
        if len(self) == 0:
            return (
                '<div style="font-family: monospace; border: 1px solid #eee;'
                ' font-size: 14px; padding: 5px; color: #999;">(no rules)</div>'
            )
        linenums = '<br>'.join(map(str, range(len(self))))
        code = '<br/>'.join(pp(self._highlight_inputs(r), color='html')
                            + '<span style="color: blue;">.</span>' for r in self)
        return f"""\
<div style="display: flex; font-family: monospace; border: 1px solid #eee; font-size: 14px !important; text-align: left !important; overflow-x: auto;">\
<div style="line-height: 1.5em; margin: 0; padding: 5px; text-align: right; user-select: none; padding-right: 10px; color: #b3777f; border-right: 1px solid #eee; margin-right: 10px;">{linenums}</div>\
<pre style="line-height: 1.5em; margin: 0; padding: 5px; overflow-x: auto; white-space: nowrap;">\
{code}</pre></div>\
"""

    def _html_types_section(self):
        """A single collapsed `<details>` holding the input/output declarations.

        Each declaration program is rendered by recursing into `to_html`, so the
        general case -- rule bodies, delayed constraints, nested declarations --
        displays correctly to arbitrary depth.
        """
        parts = []
        for label, prog in [('inputs', self.inputs), ('outputs', self.outputs)]:
            if not prog: continue
            parts.append(
                f'<div style="color: #7b2fbe; padding: 3px 0;">{label}:</div>'
                f'{prog.to_html(types=True)}'
            )
        return f"""\
<details style="font-family: monospace; font-size: 14px; border: 1px solid #eee; border-top: none;">\
<summary style="cursor: pointer; padding: 5px; color: #b3777f; background: #fafafa; user-select: none;">\
input/output declarations</summary>\
<div style="padding: 5px;">{''.join(parts)}</div></details>\
"""

    #___________________________________________________________________________
    # Cost functions

#    @staticmethod
#    def timelimited_run(p, D, budget, solver=1, kill=True, throw=False):
#        s = p.solver() if solver == 1 else p.solver2()
#        return s(D, budget=budget, kill=kill, throw=throw)

#    @staticmethod
#    def cost_prefix_firings(D='',budget=None,kill=True,**kwargs):
#        def cost(p): return Program.timelimited_run(p,D,budget=budget,kill=kill,**kwargs).prefix_firings
#        return cost

#    def arity(self):
#        """
#        Return the bag of rule arities.  The bag is represented as a sorted tuple.
#        The arity of a rule is the number of subgoals it has.
#        """
#        return tuple(reversed(sorted([len(r.body) for r in self])))

    @cached_property
    def degree(self):
        return max([r.analyzer.degree for r in self], default = 0)

    @instance_cache
    def degrees(self):
        """
        Sorted list of rule degrees, largest first; this metric is better than
        just the max degree.  It favors having fewer high degree rules,
        as well as favoring shorter programs.
        """
        return CostDegrees(tuple(reversed(sorted([r.analyzer.degree for r in self]))))

    #___________________________________________________________________________
    # Semiring-related methods

    @staticmethod
    def is_const(x):
        return is_const(x)

    @property
    def Semiring(self):
        # annoying distinction between `self.semiring` and `self.Semiring`
        return Float if self.semiring is None else self.semiring

    def lift_semiring(self, semiring):
        t = TransformedProgram(('lift', semiring), self,
                               [r.lift(semiring) for r in self.rules])
        t.semiring = semiring
        return t

    def booleanize(self):
        from dyna.analyze import remove_constants, Boolean
        q = TransformedProgram('booleanize', self, [
            # create free(X) constraints for each non-range-restricted variable X in the rule.
            remove_constants(self, r) for r in self
        ])
        q.semiring = Boolean
        return q

#    def round(self, precision):
#        import warnings
#        warnings.warn('We are going to retire this method as soon as possible; use metric for comparisons.')
#        if precision is None: return self
#        return TransformedProgram(
#            ('round', precision), self,
#            [r.round(precision) for r in self.rules],
#        )

    #___________________________________________________________________________
    # Add remove/access rules

    def __iter__(self):
        return iter(self.rules)

    def __len__(self):
        return len(self.rules)

    def __add__(self, rs):
        if isinstance(rs, str): rs = Program(rs)
        if isinstance(rs, Rule): rs = [rs]
        return self.spawn(list(self) + list(rs))

    def __sub__(self, rs):
        if isinstance(rs, int): rs = [rs]
        new = list(self)
        for i in reversed(sorted(rs)): new.pop(i)
        return self.spawn(new)

    def _update_bucket(self, r):
        assert self._buckets is not None
        # If the RHS of r is a constant, we will merge it into some buckets
        # If the RHS is not a constant, then we do nothing and return None
        C = self.get_const_rhs(r)
        if C is None: return
        h = canonicalize(r.head)
        i = self._buckets.get(h)
        if i is None:
            r = fresh(r)
            # Implementation note: if rules were mutable we could update the rhs
            # of the rule by reference, but they aren't so we add a new rule.
            self._buckets[h] = i = self._add_rule(r)
            #assert self.rules[i] is r
            return i
        else:
            s = self.rules[i]
            [S] = s.body
            self.rules[i] = Rule(s.head, S + C)
            return i

    # Warning: this function just creates an index; it does not merge rules; the
    # index created will just point to the last rule with the canonical head.
    # It won't point to all instances.
    def _make_buckets(self):
        "Initialize the constant-folding buckets."
        self._buckets = {}
        for i, r in enumerate(self):
            C = self.get_const_rhs(r)
            if C is not None:
                h = canonicalize(r.head)
                if self._buckets.get(h) is None:   # use existing bucket
                    self._buckets[h] = i

    # XXX: the main thing going on with update is that we call constant_folding_rhs and fresh
    def update(self, head, *body):
        r = self.constant_folding_rhs(Rule(head, *body))
        if r is None: return    # rule is dead
        if self._buckets is None: self._make_buckets()
        if self._update_bucket(r) is None:   # we couldn't merge this rule with an existing rule via buckets, so add it as a new rule
            self._add_rule(fresh(r))
        return self

    def append(self, r):
        return self.update(r.head, *r.body)

    def _invalidate_caches(self):
        """Drop rule-derived caches after a mutation to `self.rules`.

        Clearing a `cached_property` is O(1) (its value is only recomputed on
        the next read), so calling this per-mutation is cheap: in the
        append-heavy hot loops (`step`, `agenda`, `seminaive`, `newton`) none of
        these caches are read between mutations, so nothing is recomputed.

        Note: `_cache_f2r` is maintained incrementally here and in `pop`, and
        `_buckets` is reset in `pop`, so neither is dropped here.  `builtins` and
        `measure` are deliberately excluded -- they aren't derived from
        `self.rules` (the builtin registry, and the transform history of
        `self.root`, respectively).
        """
        for k in ('signature', '_hash_cache', 'syms', 'degree'):
            self.__dict__.pop(k, None)
        # Clear in place rather than reallocating: `_add_rule` calls this on
        # every append, and the append-heavy hot loops (`step`, `agenda`,
        # `seminaive`, `newton`) would otherwise churn a fresh object per rule.
        self._caches._caches.clear()   # degrees, prune*, ...

    def _add_rule(self, r):
        i = len(self.rules)
        self.rules.append(r)
        if self._cache_f2r is not None:
            self._cache_f2r[r.head.fn].append(i)
        self._invalidate_caches()
        return i

    def pop(self, i):
        "Remove rule at index i from the program"
        r = self.rules.pop(i)

        # `_cache_f2r` and `_buckets` both index rules by *position*. Popping
        # position `i` shifts every later rule down by one, so we can't update
        # them incrementally here: the old `self._cache_f2r[r.head.fn].remove(i)`
        # only dropped index `i` and left every index > i stale (pointing at the
        # wrong rule). Both rebuild lazily from `None` (see `f2r` /
        # `_make_buckets`), so we reset them.

        # For constant rhs rules, the bucket data structure maps a canonicalized
        # head to a rule index that corresponds to where the values for this
        # canonical item will be accumulated. It makes accumulation of rules to
        # a common head, e.g., {x+=2. x+=3} ==> {x+=5}, relatively efficient
        # (constant time).

        # The challenge with making the bucketing strategy incremental is that
        # the rules are numbered by their position in a list, which means that
        # deletion of an index changes all of their positions.  It would be
        # better to use a dictionary.

        # maybe the fix is to have an additional index based on rule id and to tweak
        # the bucket strategy to use ids rather than positions?  This is the real
        # fix that would let pop be incremental, but it is coupled to the
        # position-based rule handle `r.i` (used by derivations, unfold, elim,
        # ...), so it belongs with that cleanup rather than here.

        self._cache_f2r = None
        self._buckets = None
        self._invalidate_caches()
        return r

    def fresh(self):
        return TransformedProgram('fresh', self, [fresh(r) for r in self.rules])

    def sort(self, **kwargs):
        return TransformedProgram('sort', self, list(sorted(self, **kwargs)))

    #___________________________________________________________________________
    # Utilities

    def is_input(self, x):
        if self.inputs is None: return False
        return any(unifies(r.head, x) for r in self.inputs)    # XXX: approximate, doesn't check delayed constraints use Program's query methods

    def is_output(self, x):
        if self.outputs is None: return False
        return any(unifies(r.head, x) for r in self.outputs)

    def safe_inline(self, x):
        return (
            not self.is_input(x) and
            #not is_builtin(x) and
            not self.is_const(x)
        )

    def is_exogenous(self, x):
        "item that is defined elsewhere (i.e., constants, builtins, inputs)"
        return self.is_const(x) or self.is_builtin(x) or self.is_input(x)

    def is_item(self, x):
        return any(unifies(r.head, x) for r in self)   # might be crude (e.g., if X += (f(Y)=X) ...)

    # Classification lives in `dyna.builtin` (the single source of truth, shared
    # with the solvers); kept as a staticmethod so the `self.is_builtin(x)` /
    # `Program.is_builtin(x)` callers stay unchanged.
    is_builtin = staticmethod(is_builtin)

    #___________________________________________________________________________
    # Program equality/comparison

    def __eq__(self, other):
        "Program equality modulo variable renaming and subgoal reordering."
        if isinstance(other, str): other = Program(other)
        if self is other: return True
        if len(self) != len(other): return False
        if self._hash_cache != other._hash_cache: return False
        if self.signature != other.signature: return False
        return self._bucket_equal(other)

    same = __eq__

    def _coerce_semirings(self, other):
        """Coerce `other` to a `Program` and lift whichever side lacks a
        semiring so both share one.  Returns the (possibly replaced)
        `(self, other)` pair.  Shared by the semiring-aware comparisons
        (`metric`, `assert_equal`).
        """
        if isinstance(other, (str, list)): other = Program(other)
        if self.semiring is not None and other.semiring is None:
            other = other.lift_semiring(self.semiring)
        if other.semiring is not None and self.semiring is None:
            self = self.lift_semiring(other.semiring)
        return self, other

    def metric(self, other):
        """Distance between two programs.

        Shapes that get a tolerance-based numerical comparison (the natural
        chart representation):
         - Fully ground programs (every head and body is ground), or
         - Programs whose rules each have a constant-only body but possibly
           nonground heads.

        After `constant_folding` both collapse to "every rule is `head +=
        value`". Heads are aligned modulo variable renaming via
        `canonicalize`. The contribution is the max over heads of
        `Semiring.metric(value_self, value_other)`, with heads present in only
        one program contributing `Semiring.metric(value, zero)`.

        Rules with non-constant bodies (symbolic subgoals — the usual case for
        arbitrary programs) fall back to structural equality: contribution `0`
        if both programs have the exact same multiset of symbolic rules (modulo
        variable renaming and subgoal reordering, via the existing rule
        signature), `inf` otherwise.

        The two contributions are combined via `max`.

        """
        self, other = self._coerce_semirings(other)
        a = self.constant_folding()
        b = other.constant_folding()
        sr = a.Semiring
        A_chart, A_sym = a.chart, a.symbolic
        B_chart, B_sym = b.chart, b.symbolic
        # Numerical part: if both programs have the same chart-key set,
        # max metric across paired values. If the key sets differ, the
        # chart shapes are structurally different — return `inf` so
        # callers using metric for fixpoint convergence keep propagating
        # (matches the old `round(...) == round(...)` semantics where
        # any added/removed rule made the structural `==` false).
        if set(A_chart) != set(B_chart):
            chart_d = float('inf')
        else:
            chart_d = max((sr.metric(A_chart[k], B_chart[k]) for k in A_chart),
                          default=0)
        # Structural part: symbolic rules must match exactly. Use the
        # same bucketing / alignment as `Program.__eq__`.
        sym_d = 0 if Program._symbolic_equal(A_sym, B_sym) else float('inf')
        return max(chart_d, sym_d)

    @staticmethod
    def _symbolic_equal(rules_a, rules_b):
        if len(rules_a) != len(rules_b): return False
        R = defaultdict(list); S = defaultdict(list)
        for r in rules_a: R[r._hash_cache].append(r)
        for s in rules_b: S[s._hash_cache].append(s)
        if R.keys() != S.keys(): return False
        return all(Program._check_bucket(R[b], S[b]) for b in R)

    def _bucket_equal(self, other):
        # For efficiency, we first bucket rules by their signature.  The
        # signature is a hash that is invariant to subgoal reordering and
        # variable renaming. Thus, we only have to align rules that fell into
        # the same bucket.
        R = defaultdict(list); S = defaultdict(list)
#        for r in self:  R[r.signature].append(r)
#        for s in other: S[s.signature].append(s)

        for r in self:  R[r._hash_cache].append(r)
        for s in other: S[s._hash_cache].append(s)

        return (R.keys() == S.keys() and
                all(self._check_bucket(R[b], S[b]) for b in R))

    @staticmethod
    def _check_bucket(Rb, Sb):
        """
        Determine if an alignment of rules in the bucket `Rb` to rules in the bucket
        `Sb` is possible.
        """
        #if len(Rb) != len(Sb): return False   # unnecessary: signature has been checked by this point
        Sb = list(Sb)
        for r in Rb:
            for s in Sb:
                if r.same(s):
                    Sb.remove(s)   # can't match s again
                    break
            else:
                return False
        return True

    @cached_property
    def _hash_cache(self):
        return hash(self.signature)    # XXX: probably much better hash functions

    def __hash__(self):
        return self._hash_cache

    def assert_equal(self, other, precision=5):
        """
        Assert `self` and `other` are equivalent under various superficial
        transformation (subgoal and rule reordering, variable renaming, constant
        folding, and minor variations in numerical precision).

        Warning: `assert_equal` and `__eq__` don't always agree because __eq__ does
        not run `constant_folding` or `rounding`.

        """
        self, other = self._coerce_semirings(other)
        assert self.semiring == other.semiring
        tol = 10 ** (-precision) if precision is not None else 0
        d = self.metric(other)
        assert d <= tol, f'\nmetric={d!r} > tol={tol!r}\n' + self._compare(other)

    def compare(self, other, **kwargs):
        "Compare rules in the program side by side."
        print(self._compare(other, **kwargs))

    def _compare(self, other, precision=None):
        "Compare rules in the program side by side."
        if isinstance(other, str): other = Program(other)
        x = self.constant_folding()
        y = other.constant_folding()
        return x._format_alignment(y, x.align(y))

    def _format_alignment(self, other, alignment):
        if not alignment: return colors.light.cyan % '**both programs are empty**'
        pairs = []
        no_match = colors.light.cyan % '**no match**'
        for i,j in alignment:
            pairs.append([colors.rendering(no_match if i is None else self.rules[i]),
                          colors.rendering(no_match if j is None else other.rules[j])])
        width = max(len(x) for x,_ in pairs)
        lines = []
        for i, (x, y) in enumerate(pairs):
            pad = ' '*(width-len(x))
            idx = colors.light.magenta % f'{i}:'
            lines.append(f'{idx} {x:1s}{pad} │ {y:1s}')
        return '\n'.join(lines)

    def align(self, S):
        """
        Align rules in `self` to those in `S`.  This is used in checking program
        equivalence, which requires a perfect alignment (bijection between
        rules).  Alignment is invariant to variable renaming and subgoal
        reordering.

        """
        Sb = defaultdict(set)
#        for j,s in enumerate(S): Sb[s.signature].add(j)
        for j,s in enumerate(S): Sb[s._hash_cache].add(j)

        unmatched = set(range(len(S)))
        align = []
        for i in range(len(self)):
#            bucket = Sb[self[i].signature]
            bucket = Sb[self.rules[i]._hash_cache]

            for j in bucket:
                if self.rules[i].same(S.rules[j]):   # pragma: no branch
                    align.append((i, j))
                    bucket.remove(j)      # can't match j again
                    unmatched.remove(j)   # can't match j again
                    break
            else:
                align.append((i, None))   # no match found

        for s in unmatched:
            align.append((None, s))

        return align

#    def showdiff(self, other):
#        "Alternative program comparison to compare."
#        if isinstance(other, str): other = Program(other)
#        k = 0; n = 0
#        for i,j in self.align(other):
#            if i is None: print(colors.rendering(colors.green % f'+ {other.rules[j]}'))
#            if j is None: print(colors.rendering(colors.red   % f'- {self.rules[i]}'))
#            if i is not None and j is not None: k += 1
#            n += 1
#        print(colors.yellow % f'similarity: {k}/{n} ({k/n:.1%})')

    def trivial_rename(self, d):
        """
        Experimental kind of equality

        {f1(X,Y) += g(X,Y) * h(Y,Z).}

        {f2([Y',q(X')]) += g(X',Y') * h(Y',Z').

        """
        for ss in self.partial_megafolds(d.fresh(), skip_trivial=False):
            if len(ss) == 1:
                [rr] = ss
                if len(rr.body) == 1 and set(term_vars(rr.head)) == set(term_vars(rr.body)):
                    return ss

    #___________________________________________________________________________
    # Derivations

    def derivations(self, *args, **kwargs):
        # XXX: we use 'naive' instead of 'seminaive' because it it correctly handles builtins.
        #return self.derivations_seminaive(*args, **kwargs)
        return self.derivations_naive(*args, **kwargs)

    def derivations_naive(self, *args, **kwargs):
        return derivations.Naive(self, *args, **kwargs)

    def derivations_seminaive(self, *args, **kwargs):
        return derivations.Seminaive(self, *args, **kwargs)

    def derivations_agenda(self, *args, **kwargs):
        return derivations.agenda(self, *args, **kwargs)

    def sld(self, x):
        if isinstance(x, str): x = syntax.term(x)
        return derivations.sld(self, x)

    def d(self, i):
        "Derivation constructor helper for rule at index `i`."
        # validity of the rule application is checked in Derivation constructor
        if i is None:    # pragma: no cover

            def guess_rule_id(head, *body):
                d = derivations.Derivation(Rule(head, *body), p=self, I=i)
                ii = None
                for iii, r in enumerate(self.rules):
                    if covers(r, d.r):
                        ii = iii
                        break

                if ii is None:
                    print('warning: derivation uses missing rule', d.r)
                    print(' -> derivation:', d)
                    assert 0

                return derivations.Derivation(Rule(head, *body), p=self, I=ii)

            return guess_rule_id

        return (lambda head, *body: derivations.Derivation(Rule(head, *body), p=self, I=i))

    #___________________________________________________________________________
    # Inference

    def __call__(self, data='', budget=None, throw=True, kill=False, solver=None, **kwargs):
        assert not isinstance(data, Program) or self.Semiring == data.Semiring, \
            [self.semiring, data.semiring]
        # Only pick a solver when the caller didn't.  solver1 is faster but
        # cannot enumerate unbound head variables, so it is only safe on
        # range-restricted programs; everything else needs solver2.
        if solver is None:
            solver = 1 if self.is_range_restricted() else 2
        s = self.solver(**kwargs) if solver == 1 else self.solver2(**kwargs)
        s(data, budget=budget, throw=throw, kill=kill)
        return s

    # TODO: Solver.sol() and Program.solve() should probably be unified; same
    # for __call__ probably.
    #
    # TODO: this method (and __call__) need dispatching logic so that it is more
    # likely to "do the right thing" on an arbitrary program.  Historically, it
    # is the "best case solver" that only works on the most narrow set of
    # programs (range-restricted, finite-support), but increasingly it has been
    # a stumbling block for new users (mostly Claude, lol).
    def solve(self, *args, **kwargs):
        return self(*args, **kwargs).sol()

    def user_query(self, q):
        "Query the chart for a subset of items matching the query `q`."
        return self.solver2().user_query(q)

    def assert_equal_query(self, query, want, **kwargs):
        "Check that the `query` against `self` is equal to `want`."
        if isinstance(query, str): query = syntax.term(query)
        if isinstance(want, (float, int)): want = Program([Rule(query, want)])
        if isinstance(want, base.Semiring): want = Program([Rule(query, want)], semiring=type(want))
        self.user_query(query).assert_equal(want, **kwargs)

    def solve_linear(self):
        "Linear solve for linearly recursive programs (Kleene)."
        from dyna.execute.linear import kleene_linsolve
        return kleene_linsolve(self)

    def solver(self, **kwargs):
        "Forward chaining for range-restricted, finite-support programs."
        from dyna.execute.solver import Solver
        return Solver(self, **kwargs)

    def solver2(self, **kwargs):
        "Forward chaining for non-range-restricted programs (no other delayed constraints)."
        from dyna.execute.solver2 import Solver
        return Solver(self, **kwargs)

    def is_range_restricted(self):
        "True iff every variable in each rule's head also appears in its body."
        return all(not (term_vars(r.head) - term_vars(r.body)) for r in self.rules)

    # TODO: add the precision option like agenda.
    def fc(self, *, max_iter=None, chart=None, verbose=False, proj=lambda p: p):
        "Naive forward chaining (possibly with delayed constraints)"
        old = Program([], Program([]), Program([]), semiring=self.Semiring) if chart is None else chart
        for m in (range(max_iter) if max_iter is not None else count()):
            if verbose: print('Iter', m, old)
            new = proj(self.step(old))
            if new == old: break
            old = new
        return new

    def _fc(self, old=None, proj=lambda p: p):
        old = Program([], inputs=Program([]), outputs=Program([]), semiring=self.Semiring) if old is None else old
        while True:
            yield old
            new = proj(self.step(old))
            if new == old: break
            old = new
        return new

    def magic_templates(self):
        "Textbook magic templates, output-directed, on the Boolean semiring."
        # Identify leaves of the coarse dependency graph for use in the ordering heuristic
        cg = self._coarse_graph()
        def is_leaf(a):
            a = snap(a)
            if not isinstance(a, Term): return False
            return all(not cg.g.outgoing[root] for root in cg.nodes.roots(a))

        def reorder(ys, bound):
            "Order body atoms greedily: bind early, demand late."
            bound = set(bound)
            ordered = []
            ys = list(ys)
            while ys:
                def stage(a):
                    # 0: exogenous / dep-graph leaves (binders) — fire first to bind vars
                    # 1: intensional (demanded subgoals) — defer for range-restriction (load-bearing for pass-1 termination)
                    # 2: builtins — most deferred; need their inputs ground
                    if self.is_builtin(a): return 2
                    if not (self.is_exogenous(a) or is_leaf(a)): return 1
                    return 0
                def key(a):
                    av = term_vars(a); new = av - bound
                    return (bool(new),                                 # filters (no new vars) first
                            stage(a),                                  # binders → intensional → builtins
                            not (av & bound) and bool(bound),          # then connected
                            len(new))                                  # most selective
                a = min(ys, key=key)
                ys.remove(a)
                ordered.append(a)
                bound |= term_vars(a)
            return ordered

        magic_fn = self.gen_functor('$magic')
        def magic(t): return Term(magic_fn, t)

        rules = [Rule(magic(r.head), *reorder(r.body, set())) for r in self.outputs]
        for r in self.rules:
            gH = magic(r.head)
            ordered = reorder(r.body, term_vars(r.head))
            rules.append(Rule(r.head, gH, *ordered))                   # guarded answer
            for j, f in enumerate(ordered):                            # demand each idb subgoal
                if not self.is_exogenous(f):                           # facts are guarded too, so still demand them
                    rules.append(Rule(magic(f), gH, *ordered[:j]))     # SIPS prefix only

        tp = TransformedProgram('magic', self, rules).prune_fast()
        tp.magic_fn = magic_fn
        return tp

    def scc_solver(self, *, solver=None, magic=False, data='', budget=None):
        """Goal-directed, two-pass evaluator.

        Pass 1 runs in the Boolean semiring to build an SCC toposort index
        over the output-reachable, derivable hyperedges; pass 2 runs in the
        program's semiring with that index as a `BucketQueue` priority, so
        cyclical subprograms converge before "later" subprograms are pulled.

        With `magic=True`, pass 1 runs on the magic-templates transformation,
        so the index is sound on demand-bounded programs whose bare Boolean
        pass would diverge. Pass-1 interruption is surfaced on the returned
        solver as `.pass1_interrupted`.

        `budget` is applied per pass — passing `budget=t` means each pass
        gets up to `t` seconds, not `t` shared between them.
        """
        if not isinstance(data, Program):
            data = Program(data, semiring=self.Semiring)

        p = self.linearize()

        bound_program = p.magic_templates() if magic else p

        # Only pick a solver when the caller didn't.  Pass 1's solver1 cannot
        # enumerate unbound head variables, so it is only safe when the bound
        # boolean program is range-restricted. (With `magic=True` the magic
        # guard binds the head vars, keeping it range-restricted.)
        if solver is None:
            solver = 1 if bound_program.is_range_restricted() else 2
        solver = Program.solver if solver == 1 else Program.solver2

        s1 = solver((bound_program + data).booleanize())
        s1(budget=budget, throw=False)

        def deps(x):
            # Materialize so that lookup's unify scopes close before tarjan
            # reads the result — otherwise transitive bindings on `x` mutate
            # tarjan's dict-key hash mid-walk.
            out = []
            for r in s1.program.lookup(x):
                for _ in s1.ground_out_rule(r):
                    for b in r.body:
                        if not s1.program.is_exogenous(b):
                            out.append(canonicalize(b))
            return out

        outputs = []
        for o in p.outputs:
            for _ in s1.ground_out_rule(o):
                outputs.append(canonicalize(o.head))
        scc = {x: i for i, xs in enumerate(tarjan(deps, outputs)) for x in xs}

        # Direct map for the common case (canonical-key match); falls
        # back to a functor-indexed `Program` with unify-based lookup
        # for nonground producers. Bucket offset by +1 so a real bucket
        # is never the semiring zero.
        support_map = {k: i + 1 for k, i in scc.items()}
        support = Program([Rule(k, i + 1) for k, i in scc.items()])

        s2 = solver(p + data, AgendaType=BucketQueue)

        def priority(it):
            if not isinstance(it, Term) or p.is_exogenous(it):
                return 0
            hit = support_map.get(it)
            if hit is not None:
                return hit
            it = fresh(it)  # support.lookup may bind vars; protect caller's term
            best = None
            for r in support.lookup(it):
                v = r.body[0] if r.body else 0
                best = v if best is None else min(best, v)
            return best

        s2.priority = priority
        s2(budget=budget, throw=False)
        s2.pass1_interrupted = s1.interrupted
        return s2

    def agenda(self, *, precision=6, max_iter=np.inf):
        "Agenda-based semi-naive evaluation"

        old = Program(semiring=self.Semiring)
        change = self.step(old)
        change.has_builtins = False   # doesn't even matter in this setting because constants and builtins never go on the agenda.
        new = Program(semiring=self.Semiring)

        tol = 10 ** (-precision) if precision is not None else 0

        t = 0
        while len(change) > 0 and t < max_iter:
            t += 1

            # pick an arbitrary rule from the change buffer
            #i = int(np.random.randint(len(change)))
            i = 0    # FIFO
            u = change.pop(i)

            was = new.user_lookup(u.head)
            new.update(u.head, *u.body)
            now = new.user_lookup(u.head)
            if was.metric(now) <= tol: continue

            for r in self:                      # TODO: use indexing here
                for k in range(len(r.body)):
                    for _ in unify(u.head, r.body[k]):
                        change[r.head] = new[r.body[:k]] * Constant(u.body, vs=term_vars(r.body[k])) * old[r.body[k+1:]]

            old.update(u.head, *u.body)

        return new

    def seminaive(self, T=None, verbose=False):
        "semi-naive bottom-up evaluation; equivalent to fc but <= work per iteration."
        t = 0
        m = Program(semiring=self.semiring)
        d = self.step(Program(semiring=self.semiring))   # initialize the chart - will return height 1 derivations
        while True:
            t += 1
            if T is not None and t > T: break
            if verbose: print(colors.light.yellow % f'iter {t}:', f'change {d}')
            old = m
            [m, d] = self.seminaive_update(m, d)
            if len(d) == 0 or old == m: return m
        return m

    def seminaive_update(self, old, d):
        "derive the valuation for derivations of the next height."
        q = Program(semiring=self.semiring, has_builtins=False)
        new = (old + d).constant_folding()

        d.has_builtins = False

        for r in self:
            for k in range(len(r.body)):
                # better to have an outer loop over change to improve the number of "prefix firings"
                for value in d[r.body[k]]:
                    q[r.head] = new[r.body[:k]] * Constant(value, vs=term_vars(r.body[k])) * old[r.body[k+1:]]

        return new, q.constant_folding()

    def newton(self, T=None, verbosity=0, fmt=(lambda x: x.__repr__(numbered=False))):
        """
        Simple implementation of the semiring Newton solver, which is based on
        solving repeated linearization of the program.
        """
        for (t, chart, change_p, change, next_chart) in self._newton():
            if verbosity > 0:
                print(colors.light.yellow % f'iter {t}:')
                print('chart:', fmt(chart))
                print('change_p:', fmt(change_p))
                print('change:', fmt(change))
                print('next_chart:', fmt(next_chart))
            if chart == next_chart:           # fixpoint test
                if verbosity > 0: print(colors.light.yellow % 'converged')
                return next_chart
            if T is not None and t == T:      # no more iterations
                if verbosity > 0: print(colors.light.yellow % 'stopped early')
                return next_chart

    def _newton(self):
        # empty
        chart = Program(semiring=self.semiring)
        # initialize with dim<=1 derivations
        change_p = Program([r for r in self if r.is_const() or r.is_linear()],
                           inputs='', outputs='', semiring=self.semiring, has_builtins=False)
        t = 0
        while True:
            t += 1
            change = change_p.solve_linear()
            next_chart = (chart + change).constant_folding()
            yield (t, chart, change_p, change, next_chart)
            # Linearized program
            next_change_p = Program(semiring=self.semiring, has_builtins=False)
            for r in self:
                x = r.head; ys = r.body; K = len(ys)
                # recursive case
                for k in range(K):
                    if self.is_const(ys[k]): continue
                    next_change_p[x] = next_chart[ys[:k]] * Constant(ys[k], ys[k]) * next_chart[ys[k+1:]]
                # base case
                for i,j in combinations(range(K), 2):
                    if self.is_const(ys[i]) or self.is_const(ys[j]): continue
                    assert i < j
                    next_change_p[x] = next_chart[ys[:i]] * change[ys[i]] * chart[ys[i+1:j]] * change[ys[j]] * chart[ys[j+1:]]
            chart = next_chart
            change_p = next_change_p

    sol = seminaive

    #___________________________________________________________________________
    # Coarse-grained graph analysis

    def _coarse_graph(self):
        from dyna.analyze.coarse_graph import CoarseGraph
        return CoarseGraph(self)

    def coarse_nodes(self):
        return self._coarse_graph().nodes

    def coarse_graph(self):
        return self._coarse_graph().g

    def coarse_hypergraph(self):
        return self._coarse_graph().h

    # Experimental
    def draw(self):
        return self._coarse_graph().h

    #___________________________________________________________________________
    # Lower-level inference utilities

    def step(self, chart):
        "Apply consequence operator to `chart` using rules in this program."
        q = Program([],
                    inputs=chart.inputs,
                    outputs=self.outputs,
                    semiring=self.semiring,
                    has_builtins=self.has_builtins or chart.has_builtins)
        for r in self:
            q[r.head] = chart[r.body]
        return q

    def instantiate(self, chart=None):
        "Instantiate program rules against chart."
        if chart is None: chart = self.agenda()
        G = self.spawn()
        #G.inputs = chart.inputs
        for i, r in enumerate(self.rules):
            with self._fresh(r) as r:
                for v in chart[r.body]:
                    gr, gv = fresh((r, v))
                    gr.i = i
                    gr._contrib_value = gv
                    G.rules.append(gr)
        G.inputs = chart.inputs
        return G

    def show_groundings(self, chart=None, precision=None):
        "Show instantiations of program rules against chart."
        if chart is None: chart = self.agenda()
        for i, r in enumerate(self.rules):
            print(colors.render(colors.dark.magenta % f'# {i}: {r.__repr__(color=False)}'))
            with self._fresh(r) as r:
                for v in chart[r.body]:
                    if isinstance(v, tuple) and len(v) >= 1: v = np.prod(v)
                    if precision is not None: v = round(v, precision)
                    pre = colors.magenta % f'{v}:'
                    print(f'{pre} {r}')

    def multiple(self, r):
        """
        Check the rule for infinite multiplicities (i.e., nonground subgoals
        with nonzero values).
        """
        if any(is_var(X) for X in term_vars(r.body) - term_vars(r.head)):
            return self.Semiring.multiple(inf)
        else:
            return self.Semiring.one

    def user_lookup(self, x):
        if isinstance(x, str): x = syntax.term(x)
        return Program(
            [fresh(r) for r in self.lookup(x)],
            inputs = self.inputs,
            outputs = Program([Rule(x)]),
            semiring = self.Semiring,
        ).constant_folding()

    #def user_lookup_experimental(self, x):
    #    """
    #    Lookup any valid right-hand side.
    #    (cf. user_lookup allows single subgoals and results are formatted differently)
    #    """
    #    assert isinstance(x, str)
    #    xs = Program(f'tmp += {x}.')[0].body
    #    return Program([fresh(Rule(Term('$lookup', *xs), *r)) for r in self[xs]])

    def __getitem__(self, xs):
        "Lookup method, returns a `ResultStream`."
        if not isinstance(xs, tuple):
            return ResultStream(self.lookup_vals, xs)
        elif len(xs) == 0:
            return Constant(self.Semiring.one)
        elif len(xs) == 1:   # special case to avoid extra semiones
            return self[xs[0]]
        else:
            return self[xs[0]] * self[xs[1:]]

    def join(self, *xs):
        yield from join_f(self.lookup_vals, *xs)

    # XXX: Experimental method for adding a rule with potentially delayed
    # subgoals coming from a stream of bodies
    def __setitem__(self, x, ys):
        if not isinstance(ys, Stream): ys = Constant(ys, vs=term_vars(ys))
        vars_was = term_vars(x) | term_vars(ys)   # used to detect 'dropped variables'
        for y in ys:                                 # iterate the stream
            if not isinstance(y, tuple): y = (y,)
            r = Rule(x, *y)
            # Below, we re-run term_vars on vars_was to drop variables that got bound
            # by the product iterator.
            if not (set(term_vars(vars_was)) <= set(term_vars(r))):
                r = Rule(x, *y, self.Semiring.multiple(inf))
            self.append(r)
        return self

    def lookup_vals(self, q):
        "returns a Product type"
        if is_const(q):
            if self.has_builtins:
                yield Product([q])
        else:
            for r in self.lookup(q):
                yield r.body

    # XXX: This method exists primarily because it tells us which rule was used
    # (if any) to derive the contribution to `q`'s value.  This is done in the
    # `.i` attribute ("i" stand for index) of the rule that was returned.  It is
    # a kludgy as `Rule` do not "formally" have `i` attributes.  I would love to
    # eliminate this method in favor of `lookup_vals`.
    def lookup(self, q):
        """
        Perform a single-step of [partial] backward chaining, which may delay
        certain constraints, such as "immature" built-ins and input relations.
        Returns a stream of rules paired with substitutions (implemented by
        in-place mutation).
        """

        q = snap(q)

        if self.is_const(q):
            if self.has_builtins: yield q
            return

        if isinstance(q, Var):
            for i, r in enumerate(self.fresh()):
                r.i = i
                for _ in unify(r.head, q):
                    yield r
            return

        assert isinstance(q, Term) and not isinstance(q, Rule), q

        # TODO: need to test this more.
        if q.fn == '$lift':
            yield Rule(q, self.Semiring.lift(*q.args))
            return

        #assert not self.is_const(q), q

        # For the input params, which are abstract relations, we have no choice
        # but to leave as delayed constraints.
        if self.is_input(q):
            r = Rule(q, q)
            r.i = None
            yield r
            # Note: We fall thru (rather than return) in case there are also
            # rules that fire on q.
            return

        # ______________________________________________________________________
        # BUILTINS
        if self.has_builtins:

            if q.fn in cmps and q.arity == 2:
                x,y = q.args
                x = snap(x)
                y = snap(y)
                if is_ground(x) and is_ground(y):
                    if cmps[q.fn](x, y):
                        r = Rule(q, self.Semiring.one)   # success
                        r.i = None
                        yield r
                    return            # failure
                else:
                    r = Rule(q, q)    # delayed
                    r.i = None
                    yield r

            if q.fn == '=' and q.arity == 2:
                [X,Y] = q.args
                for _ in unify(X,Y):
                    r = Rule(q, self.Semiring.one)
                    r.i = None
                    yield r
                return

            if q.fn == 'is':
                b = self.builtins
                if b.is_ready(q):    # evaluate subgoal if it's ready
                    for _ in b(q):
                        r = Rule(q, self.Semiring.one)
                        r.i = None
                        yield r
                else:
                    r = Rule(q, q)   # leave subgoal delayed if it's not ready
                    r.i = None
                    yield r
                return

            if isinstance(q, BuiltinConstaint):
                yield from q.run(self)
                return

            if q.fn == '$not_matches':
                yield from NotMatchesConstaint(*q.fargs).run(self)
                return

        # END BUILTINS
        # ──────────────────────────────────────────────────────────────────────

        ix = self.f2r(q.fn)

        # Match rules by head
        for i in ix:
            with self._fresh(self.rules[i]) as r:
                r.i = i
                for _ in unify(r.head, q):
                    yield r

    #___________________________________________________________________________
    # Rule indexing

    # Note: We do this indexing lazily (and incrementaly) - especially since most programs
    # during transform search won't change the rules very much or even access
    # the index at all.
    def f2r(self, f):
        if self._cache_f2r is None:
            # Rule indexing by head functor
            syms = self.syms
            f2r = defaultdict(list)
            for i, r in enumerate(self):
                if isinstance(r.head,  Term):
                    f2r[r.head.fn].append(i)
                else:
                    # head is a variable
                    assert isinstance(r.head, Var), r
                    for f in syms: f2r[f].append(i)   # every functor uses matches the wild rule.
            self._cache_f2r = f2r
        return self._cache_f2r.get(f, [])

    #___________________________________________________________________________
    # Symbol management

    @cached_property
    def syms(self):
        # track the set of symbols defined in this program to avoid potential
        # errors in gensym; this can happen when I copy a program with a
        # previous batch of gensyms in it!
        syms = set()
        for r in self:
            if isinstance(r.head, Term):
                syms.add(r.head.fn)
            for b in r.body:
                if isinstance(b, Term):
                    syms.add(b.fn)
        return syms

    def gen_functor(self, prefix='$gen'):
        "Generate a fresh item name that does not appear in `self` to avoid collisions"
        # Global counter
        f = gen_functor(prefix)
        assert f not in self.syms
        return f

    def _gen_functor(self, prefix):
        "Generate a functor that does not appear in this program."
        # Local counter
        c = 1
        f = prefix
        while f in self.syms:
            c += 1
            f = f'{prefix}{c}'
        return f

    #___________________________________________________________________________
    # Constant folding, running builtins, constraint propagation

    def constant_folding(self):
        """Fold constants within each rule's body, drop rules whose
        constant body folds to zero, and merge rules with constant RHSs
        that share a head (up to variable renaming). See
        `ConstantFolded` for the result shape.
        """
        return ConstantFolded(self)

    # XXX: Warning! this implementation assumes multiplication is commutative.
    def constant_folding_rhs(self, r):
        "Folding constants within the rule r, returns None if r goes to zero."
        assert isinstance(r, Rule), r
        C = self.Semiring.one; xs = []
        for x in r.body:
            if self.is_const(x):
                C *= deref(x)     # Note: `deref` here in case a subgoal was a bare variable
            else:
                xs.append(x)
        if self.Semiring.metric(C, self.Semiring.zero) <= 1e-7:  # drop the rule
            return
        elif C == self.Semiring.one and len(xs) > 0:
            return Rule(r.head, *xs)
        else:
            return Rule(r.head, C, *xs)

    def get_const_rhs(self, r):
        "Return a semiring value if the rhs of r is a constant and None otherwise."
        if len(r.body) == 0:
            return self.Semiring.one
        if len(r.body) == 1:
            x = r.body[0]
            if self.is_const(x):
                return x

    def snap_unifications(self):
        """
        Resolve all unification constraints.

        The dual of this method (`normalize_unification2`) normalizes unifications to a
        collection of shallow equality predicates.
        """
        new = self.spawn()
        for r in self:
            for ys in r.body.snap_unifications():
                new.append(Rule(r.head, *ys))
        return new

    def run_builtins(self):
        R = self.spawn()
        for r0 in self:
            # run to fixpoint (would be more efficient to use an agenda; maybe
            # we can use constraint-propagation library?  The challenge is if
            # the builints are not semi-deterministic).
            old = r0.to_program()
            while True:
                new = self.spawn()
                for r in old:
                    for ys in self._run_builtins(r.body):
                        new.append(Rule(r.head, *ys))
                if old == new: break
                old = new
            R = R + old
        return R

    def _run_builtins(self, ys):
        if len(ys) == 0:
            yield Product()
            return
        else:
            if self.is_builtin(ys[0]):
                for v in self.lookup_vals(ys[0]):
                    for vs in self._run_builtins(ys[1:]):
                        yield v * vs
            else:
                for vs in self._run_builtins(ys[1:]):
                    yield ys[0] * vs

    #def rewrites(self, rewrites):
    #    "Apply rewrites to the bodies of all rules in this program."
    #    if isinstance(rewrites, str):
    #        from dyna import ConstraintPropagation
    #        rewrites = ConstraintPropagation(rewrites)
    #    rs = []
    #    for r in self:
    #        u = rewrites(r.body)
    #        if u is not None: rs.append(Rule(r.head, *u))
    #    return TransformedProgram('rewrites', self, rs)

    #___________________________________________________________________________
    # Program transformations

    def noop(self):
        "no-op: Identity transformation"
        return self

    def reset_transform_history(self):
        "reset transformation history (i.e., remove parent pointers)"
        return self.spawn(list(self.rules))

    def elim(self, s, **kwargs):
        #try:
        return self.linearize(driver=self.rules[s].head).linear_rule_elimination(s, **kwargs)
        #except AssertionError as e:
        #    import warnings
        #    warnings.warn(str(e))
        #    return self

    def linear_rule_elimination(self, s, **kwargs):
        from dyna.transform.rule_elimination import LinearRuleElimination
        return LinearRuleElimination(self, s, **kwargs)

    def elim_p(self, i, **kwargs):
        "shorthand for `elim(i).prune(**kwargs)`"
        return self.elim(i).prune(**kwargs)

    def unfold(self, i, j, **kwargs):
        "Apply unfolding transformation"
        from dyna.transform.unfold import Unfold
        return Unfold(self, i, j, **kwargs)

    # TODO: add max_iters option
    def unfold_x(self, x, verbosity=0):
        """
        Unfold this program until all of the `x` items are gone.
        Warning: This procedure may not terminate if `x` is recursive.
        """
        if isinstance(x, str): x = syntax.term(x)
        old = self
        while True:
            if verbosity > 0: print('unfold_all:', old)
            new = old._unfold_x(x)
            if new is None or new == old: return old
            old = new

    def _unfold_x(self, x):
        "Unfold the first `x` subgoal in the program; helper for the `unfold_x` method."
        for i, r in enumerate(self):
            for j, y in enumerate(r.body):
                if unifies(x, y):
                    return self.unfold(i, j).prune_fast()

    def manual_fold(self, r, j, S, defs=None):
        "Manually specified fold; safety not guaranteed."
        from dyna.transform.fold import Fold
        if isinstance(r, str): [r] = Program(r)
        return Fold(parent=self, r=r, S=S, j=j, defs=defs)   # might be unsafe!

    def basic_fold(self, r, j, S, defs=None):
        "Manually specified fold; safety checked by reversibility."
        # We conjecture that a new program `q = (p - Rs) + r` is equivalent to `p`
        # We accept the fold if q.unfold(r,i) = p.
        # When defs=None, we use the result program (denoted q below) to unfold wrt.
        new = self.manual_fold(r=r, S=S, j=j, defs=defs)
        if not new.safe_by_rev: raise ValueError('invalid fold')
        return new

    def define(self, defs):
        """
        Augment program with a new definition.
        Warning: we do not check for duplicate definitions.
        """
        if isinstance(defs, str): defs = Program(defs)
        return Define(self, defs)

    def hook(self, i, js):
        """
        Add a new definition based on the "hook trick" where

          i: index of rule of a rule
          js: factor indices in rule i to fold into their own rule

        The new definition is grafted into the new program via fold.

        """
        r = self.rules[i]
        tmp_rule = self.loop_absorption(i, js)
        rev_rule = Rule(r.head, tmp_rule.head, *[f for j,f in enumerate(r.body) if j not in js])
        return self.define([tmp_rule]).basic_fold(rev_rule, j=0, S={i})

    def loop_absorption(self, i, js, name='$gen'):
        """
        Generate a new definition using the loop absorption recipe (aka hook trick).
        """
        return self._loop_absorption(i, js, self.gen_functor(name))

    def _loop_absorption(self, i, js, name):
        "Generate a new definition using the loop absorption recipe"
        assert isinstance(i, int), i
        r = self.rules[i]

        rev_fs = [f for j,f in enumerate(r.body) if j not in js]
        tmp_fs = [r.body[j] for j in js]

        # Which variable are eliminated by the fold?  Variables only appear in `js`,
        # not in `head` or other `remaining_factors`.
        elim_vars = term_vars(r.body) - (term_vars(rev_fs) | term_vars(r.head))
        out_vars = (term_vars(tmp_fs) - elim_vars)

        # Warning: sorting variables can lead to instability
        tmp_rule = Rule(Term(name, *out_vars), *tmp_fs)

        return tmp_rule

    @to_collection
    def unfolds(self, defs=None, heads=None, body=None):
        "Enumerate all available unfold actions"
        for i, r in enumerate(self):
            if heads is not None and not unifies(r.head, heads): continue
            for j, x in enumerate(r.body):
                if body is not None and not unifies(x, body): continue
                if self.safe_inline(x):
                    yield self.unfold(i, j, defs=defs)

    @to_collection
    def partial_megafolds(self, defs=None, Rs=None, skip_trivial=True, skip_zero_width=True):
        """
        Enumerate all the ways to fold together rules in `self` according to the
        folder definitions `defs`.  Warning: fold safety is not checked here.
        """

        if defs is None: defs = self
        if defs is self: defs = defs.fresh()
        if Rs is None: Rs = self.fold_proposals(defs=defs, skip_trivial=skip_trivial, skip_zero_width=skip_zero_width)

        for r in Rs:
            for new in self.folds_by(r=r, js=r.j, defs=defs):
                if new.partially_safe:
                    yield new

    @to_collection
    def reversible_megafolds(self, defs=None, Rs=None, skip_trivial=True, skip_zero_width=True):
        """
        Enumerate all the ways to fold together rules in `self` according to the
        folder definitions `defs`.
        """
        from dyna.transform import fold_r_S, prune_r_S

        if defs is None: defs = self
        if defs is self: defs = defs.fresh()
        if Rs is None: Rs = self.fold_proposals(defs=defs, skip_trivial=skip_trivial, skip_zero_width=skip_zero_width)
        for r in Rs:
            yield from fold_r_S(self, defs, r, prune_r_S(self, r))

    @to_collection
    def megafolds(self, *args, **kwargs):
        "Enumerate safe megafolds"
        # pylint: disable=no-member  # @to_collection returns a ProgramCollection, but @wraps hides it from astroid
        return self.partial_megafolds(*args, **kwargs).filter(lambda x: x.safe_by_smt)

    @to_collection
    def folds_by(self, r, js=None, defs=None):
        from dyna.transform.fold import Fold
        if isinstance(r, str): [r] = Program(r)
        if defs is None: defs = self
        if isinstance(js, int): js = [js]
        if js is None: js = range(len(r.body))
        for j in js:
            A = self.align(r.unfold(j, defs=defs))
            S = frozenset({i for i,j in A if j is not None})
            if None not in S:
                yield Fold(parent=self, r=r, S=S, defs=defs, j=j)

    def fold_proposals(self, defs, skip_trivial=True, skip_zero_width=True):
        """
        Enumerate folded rules for use in the generalized folding transformation
        based on the definitions `defs`.  Returns a set of rules that *may* be useful
        for generalized folds.
        """
        proposals = NoDupsSet([], Rule.same)
        for i in range(len(defs)):
            d_sig = defs.rules[i]._body_fns
            for j in range(len(self)):
                if skip_zero_width and (len(self.rules[j].body) == 0 or len(defs.rules[i].body) == 0):
                    continue
                p_sig = self.rules[j]._body_fns
                is_sub = all(d_sig[k] <= p_sig[k] for k in d_sig)
                if not is_sub: continue   # skip because it is guaranteed to be unproductive
                for u in self.rules[j].folds_by(defs.rules[i]):
                    #if not defs.safe_inline(u.body[u.j]): continue
                    if skip_trivial and len(u.body) == 1 and u.head == u.body[0]: continue
                    # Experimental - Disallowing empty matches reduces many of
                    # the crummy fold proposals. This improves efficiency.
                    # However, it looks like this kind of fold is useful for the
                    # evenodd_list example so we shouldn't prune it - we should
                    # somehow give it low priority.
                    proposals.add(u)
                    #got.append(u)
                #if len(got) == 0 and not self[j].same(defs[i]):
                #    print('try fold:', parent[j])
                #    print('      by:', defs[i])
                #    print('    p-sig:', p_sig)
                #    print('    d-sig:', d_sig)
                #    for u in got: print('  ->', u)
        return proposals

    def to_collection(self):
        "Convert this program into a (singleton) `ProgramCollection`."
        return ProgramCollection([self])

    def slash(self, x, *args, **kwargs):
        "Apply the speculation transformation"
        from dyna.transform.slash import Slash
        return Slash(self, x, *args, **kwargs)

    def lct(self, *args, **kwargs):
        "Apply the left-corner transformations"
        from dyna.transform.lct import LCT
        return LCT(self, *args, **kwargs)

    #___________________________________________________________________________
    # Measure-based transformation safety checks

    @cached_property
    def measure(self):
        "Build a measure-based safety checker from this program's transformation history."
        from dyna.transform.measure import make_smt_measure
        return make_smt_measure(self.root)

    @cached_property
    def safe_by_smt(self):
        "Check the measure-based safety condition"
        return self.measure(self).is_safe()

    #___________________________________________________________________________
    # Program specialization methods

    @instance_cache
    def prune_fast(self, **kwargs):
        "Program specialization: remove dead and useless rules with coarse-grained reachability analysis"
        from dyna.analyze.dead import prune_fast
        return prune_fast(self, **kwargs)

    @instance_cache
    def prune_very_fast(self):
        from dyna.analyze.dead import prune_very_fast
        return prune_very_fast(self)

    @instance_cache
    def prune_bottom_up(self, **kwargs):
        return self.prune(bottom_up_only=True, **kwargs)

    @instance_cache
    def prune(self, specialize=True, bottom_up_only=False, **kwargs):
        """
        Program specialization: remove dead and useless rules with fine-grained reachability analysis,
        and it will specialize rules (including splitting) when static variable assignments are known.
        """
        from dyna.analyze.dead import _prune_specialize, _prune_dead
        if bottom_up_only:
            s = self.type_analysis(input_type=self.inputs, rewrites='', use_insts=False, **kwargs)
        else:
            s = self.usefulness_analysis(**kwargs)
        if specialize:
            return _prune_specialize(self, s.chart)
        else:
            return _prune_dead(self, s.chart)

    # TODO: Should the default behavior for `abbreviate` be to abbreviate with
    # respect to the /useful/ items rather than the /possible/ items?
    def abbreviate(self, *, types=None, **kwargs):
        "Program specialization transformation that will split items based on inferred, disjoint simple types"
        from dyna.analyze.abbreviate import Abbreviate
        if types is None: types = self.type_analysis()
        #if types is None: types = self.usefulness_analysis()
        return Abbreviate(self, types, **kwargs)

    #___________________________________________________________________________
    # Program normalization

    def linearize(self, driver=None):
        """
        Split overlapping body subgoals into fresh copies so every rule is locally linear.
        Note: this should not be confused with the type of linearization done in Newton's
        algorithm or `solve_linear`.
        """
        tmps = OrderedSet()
        for i, s in enumerate(self):
            #print('rule', s)
            for j, x in enumerate(s.body):
                if driver is not None and not unifies(x, driver): continue
                if self.is_const(x): continue
                if self.is_builtin(x): continue
                for k in range(j+1, len(s.body)):
                    y = s.body[k]
                    if unifies(x, y):
                        tmps.add((i,k))

        if not tmps:
            return self

        new_rules = list(self)
        for i, k in tmps:
            r = new_rules[i]
            bs = list(r.body)
            # replace in body
            h = Term(self.gen_functor(), *r.body[k].args)
            bs[k] = h
            new_rules.append(fresh(Rule(h, r.body[k])))
            new_rules[-1].analyzer.linearized = True   # tag the rule's analyzer
            new_rules[i] = fresh(Rule(r.head, *bs))

        return TransformedProgram('linearize-rhs', self, new_rules)

    def normalize_unification2(self):
        """
        Normalize each rule so every body subgoal is either a flat predicate
        call (all args are Vars) or a shallow unification `V = T(V1, ..., Vn)`
        / `V = V'` / `V = constant`. Nested term structure in the head or body
        is lifted into fresh `=` constraints.

        The dual of this method (`snap_unifications`) resolves all
        unifications by inlining.

        Idempotent: calling on an already-normalized program is a no-op
        (modulo the transform-name wrapper). Body subgoals that are already
        in normal form are recognized and passed through unchanged, instead
        of getting re-wrapped with fresh-Var alias chains like
        `$Gen' = $Gen, $Gen = T`.

        >>> p = Program('goal(W) += foo(X), bar([X|Xs], W).')
        >>> n1 = p.normalize_unification2()
        >>> n2 = n1.normalize_unification2()
        >>> str(n1) == str(n2)
        True
        """

        # TODO: We currently have an issue with (S is X' + S') because it is a
        # nested term with outer functor `is`.
        #
        # TODO: If a variable appears twice as an argument to a subgoal, do we
        # need to create a tmp variable and add an equality check?  (this is how
        # we did things in the 2013 compiler's SSA normalization pass.)
        #
        # TODO: We could do another pass to split instances of a repeated
        # variables; the normal form should ensure that every variable is
        # 'assigned' to once (SSA).

        def normalize(x):

            result = []
            def f(x):
                "convert a structured term into a series of flat unifications"
                if isinstance(x, (list, tuple)): return [f(y) for y in x]
                elif isinstance(x, Var): return x
                elif isinstance(x, Term):
                    # replace structured argument with a fresh variable $X
                    # defined by a simple unification constraint (i.e., a
                    # unification constraint with at most one function symbol).
                    z = Var()   # new variable
                    result.append(Term('=', z, Term(x.fn, *f(x.args))))
                    return z
                else:
                    z = Var()   # new variable
                    result.append(Term('=', z, x))
                    return z

            f(x)
            return result

        def is_normal_form(y):
            """A body subgoal is in normal form if it is either a flat call
            `pred(V1, ..., Vn)` (all args are Vars) or a shallow unification
            `V = T(V1, ..., Vn)` / `V = V'` / `V = constant`."""
            if not isinstance(y, Term):
                return False
            if y.fn == '=' and len(y.args) == 2:
                v, rhs = y.args
                if not isinstance(v, Var):
                    return False
                if isinstance(rhs, Var):
                    return True
                if isinstance(rhs, Term):
                    return all(isinstance(a, Var) for a in rhs.args)
                return True  # constant
            return all(isinstance(a, Var) for a in y.args)

        nrs = []
        for r in self:
            [*tmps, [_, _, h]] = normalize(r.head)
            ys = list(tmps)
            for y in r.body:
                if is_normal_form(y):
                    ys.append(y)
                else:
                    [*tmps, [_, _, yy]] = normalize(y)
                    ys.extend(tmps)
                    ys.append(yy)

            nrs.append(Rule(h, *ys))

        return TransformedProgram('normalize-unification', self, nrs)

    #___________________________________________________________________________
    # Analysis

    def type_analysis(self, input_type=None, rewrites='', **kwargs):
        from dyna.analyze import TypeAnalyzer
        if input_type is None: input_type = self.generic_input_type_bindings()
        return TypeAnalyzer(self, input_type, rewrites, **kwargs)

    def usefulness_analysis(self, *, input_type=None, output_type=None, use_insts=True, **kwargs):
        # we don't need to infer binding states in this analysis
        s = self._useful(output_type=output_type).type_analysis(input_type=input_type, use_insts=use_insts, **kwargs)
        # hack the chart to include items that are possible and useful -- i.e.,
        # derived items tagged as $both.
        s.chart = (Program('X += $useful(X).') + s.chart.spawn()).unfold(0,0,defs=s.chart)
        return s

    def _useful(self, output_type=None):
        "Define the set of useful items for this program given the `output_type`"
        if output_type is None: output_type = self.outputs
        if isinstance(output_type, str): output_type = Program(output_type)

        def u(x): return Term('$useful', x)

        new = []
        def add(*xs): new.append(Rule(*xs))

        # Note: keep the revised rules in their original order in the new
        # program.  All new rules for magic item will go after.
        for r in self:
            add(r.head, *r.body)

        for t in output_type:
            add(u(t.head), t.head, *t.body)    # possible outputs are useful

        for r in self:
            h = r.head; b = r.body
            for k in range(len(b)):
                if self.is_const(b[k]) or self.is_builtin(b[k]): continue
                add(u(b[k]), u(h), *b)

        return TransformedProgram('useful', self, new)

    def generic_input_type_bindings(self, generic='$bound'):
        if self.inputs is None: return self.spawn()
        return Program([
            Rule(t.head, *[Term(generic, v) for v in term_vars(t.head)])
            for t in self.inputs
        ], f'{generic}(_).')

#    def generic_input_type_any(self):
#        if self.inputs is None: return Program()
#        return self.inputs

    # TODO: rename?
    def show_analyzers(self):
        print('Analysis {')
        print(colors.yellow % f'  % degree={self.degree}')
        for i, r in enumerate(self):
            x = r.analyzer
            c = colors.orange if x.degree == self.degree else colors.dark.yellow
            E = {v: x.v2f[v] for v in x.can_elim}
            info = f'\t% degree={x.degree}'
            p = PrettyPrinter()
            if x.can_elim:
                can_elim = p(set(E))
                info = f'{info}, can_elim={can_elim}'
            print(f'  {i}:', p(x.rule), colors.render(c % info))
        print('}')
        return self

    #___________________________________________________________________________
    # Utilities for transformation sequences

    def transforms(self):
        x = self
        while isinstance(x, TransformedProgram):
            yield x
            x = x.parent
        yield x

    def show_transforms(self, show_program=False):
        print()
        print(colors.dark.yellow % '## Transforms')
        prev = None
        for x in reversed(list(self.lineage())):
            if isinstance(x, TransformedProgram):
                print(colors.render(colors.yellow % f'{x.name}'))
            else:
                print(colors.yellow % 'original')
            if show_program: print(x)
            prev = x

    def lineage(self):
        x = self
        while isinstance(x, TransformedProgram):
            yield x
            x = x.parent
        yield x

    #___________________________________________________________________________
    # Optimizers

    def optimizer(self, **kwargs):
        from dyna.search import AgendaBasedSearch
        return AgendaBasedSearch(self, **kwargs)

    def binarize(self):
        """
        McAllester (2002)'s rule binarization transformation (uses left-to-right
        binarization).  For better results, run optimizing binarization.
        """
        q = self
        i = 0
        while i < len(q):
            r = q.rules[i]
            K = len(r.body)
            if K > 2: q = q.hook(i, range(1,K))   # takes the first two subgoals arbitrarily
            i += 1
        return q

    def search_graph(
            self,
            max_depth = 10000,
            TRANSFORMS = ('fold*', 'unfold', 'elim'),
            graph = 2,
            cost = degrees,
            tidy = True,
    ):
        from dyna.search import Graph1, Graph2

        if graph == 1:
            return Graph1(
                src = self,
                max_depth = max_depth,
                TRANSFORMS = TRANSFORMS,
                cost = cost,
                tidy = tidy,
            )

        else:
            return Graph2(
                src = self,
                max_depth = max_depth,
                TRANSFORMS = TRANSFORMS,
                cost = cost,
                tidy = tidy,
            )

    def beam(
            self,
            reps,
            beam_size,
            checkpoint = None,
            max_depth = 10000,
            TRANSFORMS = ('fold*', 'unfold', 'elim'),
            graph = 2,
            cost = degrees,
            tidy = True,
            **kwargs,
    ):
        from dyna.search import BeamSearch
        return BeamSearch(
            G = self.search_graph(
                graph = graph,
                max_depth = max_depth,
                TRANSFORMS = TRANSFORMS,
                tidy = tidy,
                cost = cost,
            ),
            program = self,
            reps = reps,
            beam_size = beam_size,
            checkpoint = checkpoint,
            **kwargs,
        )

#    def mcts(self, reps, checkpoint = None, max_depth = 10000, TRANSFORMS = ('fold*', 'unfold', 'elim'),
#             graph = 2, tidy = True, cost = degrees, **kwargs):
#        from dyna.search import MCTS
#        return MCTS(
#            G = self.search_graph(
#                graph = graph,
#                max_depth = max_depth,
#                TRANSFORMS = TRANSFORMS,
#                cost = cost,
#                tidy = tidy,
#            ),
#            program = self,
#            reps = reps,
#            checkpoint = checkpoint,
#            **kwargs,
#        )

    # XXX: this method has a subtle bug: in order to have a coherent bijection, we
    # require a canoncial path between derivations - we cannot mix and match which
    # derivations are mapping on a call-by-call basis!  This should be an easy fix.
    def Transform(self, d, target):
        """
        Derivation mapping. This method will compose derivation mappings in a
        network of strongly equivalent programs
        """

        if isinstance(d, (tuple, list)):
            return d.__class__([self.Transform(y, target) for y in d])

        if derivations.Derivation.base(d): return d
        source = d.p

        assert target.root == source.root

        # We can find a path for source to target by going through their common root node
        # (which exists by assumption).
        if target not in set(source.transforms()) and source not in set(target.transforms()):
            return source.root.Transform(source.Transform(d, source.root), target)

        if source is target:   # exactly the same program
            return d

        elif source == target:  # an equal, but not exact, match (allows superfical differences)

            # simple transform: renames the rules according to the alignment between
            # source and target.
            alignment = dict(source.align(target))
            return target.d(alignment[d.i])(
                d.head,
                *[source.Transform(y, target) for y in d.body]
            )

        elif source in set(target.transforms()):
            if source == target.parent:
                return target.transform(d)
            else:
                return target.parent.Transform(source.Transform(d, target.parent), target)

        else:
            if source.parent == target:
                return source.untransform(d)
            else:
                return source.parent.Transform(source.Transform(d, source.parent), target)


class TransformedProgram(Program):
    def __init__(self, name, parent, program):
        self.name = name
        self.parent = parent
        super().__init__(
            program,
            inputs = parent.inputs,
            outputs = parent.outputs,
            semiring = parent.semiring,
            has_builtins = parent.has_builtins,
        )
        self.root = parent.root


# TODO: add a check for overlap -- if we add a new rule it needs a distinct name
# space (i.e., a sufficient "fresh" name) or else we run the risk of this
# transformation not being semantics-preserving.  It is more nuanced than this,
# as this has to be the case for *all* programs in a provenance tree.  Note that
# Tim's thesis makes the simplifying assumption that all definitions appear in
# the original program so all transformed programs inherit from it.  We may also
# need to assume that unfold/fold by `defs` need to have related transformation
# histories they can't be unrelated programs as they should have incompatible
# measure (need to check if the measure safety system actually gets that
# right!).
#
class Define(TransformedProgram):
    "Definition introduction transform"
    def __init__(self, parent, defs):
        self._old_ix = range(len(parent))
        self._new_ix = range(len(parent), len(parent) + len(defs))
        self.defs = defs
        super().__init__(f'define({defs})', parent, list(parent) + list(defs))


# TODO: move to transform submodule
class ConstantFolded(TransformedProgram):
    """Output of `Program.constant_folding`. Folds per-rule constants,
    drops rules whose constant body folds to zero, and merges rules
    that share a canonical (head, symbolic-body) skeleton — the
    constant coefficients of mergeable rules are accumulated via the
    semiring `+`.

    The skeleton-based merge generalizes the original "single-constant
    body" vertical-fold: rules like

        a(X,Y) += 1.0  * (X<Y).
        a(X,Y) += 0.5  * (X<Y).
        a(X,Y) += 0.25 * (X<Y).

    all share the canonical skeleton `(a(X,Y), [(X<Y)])` and merge
    into a single rules:

        a(X,Y) += 1.75 * (X<Y).

    Cached attributes:

    - `chart`: `{canonical_head: value}` for rules whose folded body is
      a single semiring constant (skeleton has empty symbolic part).
    - `merged`: `{skeleton_key: (head, xs, value)}` for rules with
      a symbolic body — `value` is the accumulated coefficient,
      `xs` the (representative) symbolic subgoals.
    - `symbolic`: list of merged rules emitted from `merged`. Kept
      under the historical name so `Program.metric` can read it.
    """
    def __init__(self, parent):
        sr = parent.Semiring
        # First pass: per-rule fold; drops zero-folded rules.
        intermediate = []
        for r in parent:
            r = parent.constant_folding_rhs(r)
            if r is not None:
                intermediate.append(r)
        # Second pass: bucket rules by canonical (head, symbolic-body)
        # skeleton, accumulating the constant coefficient. Pure-chart
        # rules (empty symbolic) and rules with mergeable symbolic
        # bodies (e.g. `a(X,Y) += c1 * b(X,Y)` and `a(X,Y) += c2 *
        # b(X,Y)` collapsing to `a(X,Y) += (c1+c2) * b(X,Y)`) share
        # this code path.
        #
        # Body subgoals are sorted into a canonical order before the
        # skeleton key is built so that rules differing only in
        # multiplicative reordering (`*` is commutative) merge.
        #
        # Some Term subclasses (e.g. `Derivation`) have non-variadic
        # `__init__`s and don't survive `canonicalize` — those rules
        # fall back to "skeleton key is the rule itself", which keeps
        # them un-merged but doesn't crash.
        merged = {}
        for r in intermediate:
            C, xs = self._split_const_and_symbolic(parent, r)
            # Bucket key uses xs in canonical order (so commutative `*`
            # reorderings merge), but the emitted rule keeps the
            # first-seen rule's xs order — downstream code (e.g.
            # `Program.unfold(rule_i, subgoal_j)`) refers to subgoals
            # by position and would be sensitive to a reorder here.
            xs_sorted = sorted(xs, key=_subgoal_sort_key)
            key = canonicalize(Term('$skel', r.head, *xs_sorted))
            if key in merged:
                head_, xs_, total = merged[key]
                merged[key] = (head_, xs_, total + C)
            else:
                merged[key] = (r.head, xs, C)
        # Emit one rule per merged bucket. Drop the explicit C when
        # it's the multiplicative identity (the same convention as
        # `constant_folding_rhs`).
        chart = sr.chart()
        symbolic = []
        for head, xs, total in merged.values():
            if not xs:
                chart[canonicalize(head)] += total
            elif total == sr.one:
                symbolic.append(Rule(head, *xs))
            else:
                symbolic.append(Rule(head, total, *xs))
        self.chart = chart
        self.merged = merged
        self.symbolic = symbolic
        rules = list(symbolic) + [Rule(x, C) for x, C in chart.items()]
        super().__init__('constant_folding', parent, rules)

    @staticmethod
    def _split_const_and_symbolic(parent, r):
        """Return `(C, xs)` where `C` is the constant coefficient of
        `r` (defaulting to `Semiring.one`) and `xs` is the list of
        non-constant body subgoals. After `constant_folding_rhs`, a
        rule's body is either `[*xs]` (no explicit constant, C=1) or
        `[C, *xs]` (constant in body[0]).
        """
        if r.body and parent.is_const(r.body[0]):
            return deref(r.body[0]), list(r.body[1:])
        return parent.Semiring.one, list(r.body)


from dyna.programs import ProgramCollection
from dyna import derivations
