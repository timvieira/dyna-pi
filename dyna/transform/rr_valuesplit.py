"""
Disjoint case-splitting for the value-split gap.

The path-phantom transform (rr_phantom2.py) refuses a position that is phantom
in some rules but specific (a constant) in others, e.g.

    f(1) += 2.        % specific
    f(X) += 3.        % general (phantom at position 0)
    goal += f(X).

because position 0 is not *uniformly* phantom (f(1)=5, f(2)=3).  This module
closes that gap with a provably-sound **default + exception** decomposition,
exploiting that overlapping heads sum (verified: f(1)=2+3=5):

    f(..v..) = f_default(..)  ⊕  f_spec(..v..)

where `f_default` is the general (phantom) rules with the split position
projected away (the value common to every coordinate), and `f_spec` is the
specific (constant) rules.  This is a genuine partition of f's *rules* by the
semiring `+`, so it needs no disequality guards and no type-merge heuristic — it
is sound by linearity of `+` over the rule set.

A consumer that sums over the split position distributes the same way:

    goal += f(X)   ==>   goal += inf * f_default   +   goal += f_spec(X)

The first term is the cofinite/default part (range-restricted: a scalar times a
witness count); the second reads the finite-support `f_spec` (range-restricted:
X is bound by f_spec).  Reads at a constant coordinate keep reading the
recovered `f`.

Scope: constant/variable overlap at a top-level position, the canonical
value-split (`test_infinite_multiplicity`).  Diagonal overlap (`q(X,X)`/`q(X,Y)`)
and recursive overlap are not handled here and fall through to the conservative
phantom transform (sound, unprojected).
"""

from dyna import TransformedProgram, Rule, Term, term_vars, snap, is_var, fresh
from dyna.term import Var
from dyna.builtin import is_builtin
from dyna.transform.rr_phantom import _pos_phantom_in_rule, phantom_positions


def _classify(program, rules, i):
    """Classify position i across a predicate's rules as a value-split:
    every rule must have a constant ('spec') or a single-occurrence
    unconstrained variable ('gen') at position i, with at least one of each."""
    P = phantom_positions(program)   # for propagation in _pos_phantom_in_rule
    spec, gen = [], []
    for r in rules:
        arg = snap(snap(r.head).args[i])
        if is_var(arg):
            if _pos_phantom_in_rule(program, r, i, P):
                gen.append(r)
            else:
                return None            # variable but not phantom -> not splittable
        elif program.is_const(arg) or (isinstance(arg, Term) and not is_var(arg)):
            # a constant or a ground structured term at position i
            if term_vars(arg):
                return None            # structured-with-vars -> out of scope
            spec.append(r)
        else:
            return None
    if spec and gen:
        return spec, gen
    return None


def _drop_arg(t, i, newfn):
    args = [t.args[j] for j in range(t.arity) if j != i]
    return Term(newfn, *args)


class ValueSplit(TransformedProgram):
    """Default+exception decomposition for constant/variable overlaps, composed
    with the path-phantom projection for the resulting general part."""

    def __init__(self, program):
        groups = {}
        for r in program.rules:
            h = snap(r.head)
            if isinstance(h, Term):
                groups.setdefault((h.fn, h.arity), []).append(r)

        # find the splittable (predicate, position) pairs
        splits = {}   # (fn,arity) -> (i, spec_rules, gen_rules)
        for (fn, arity), rules in groups.items():
            if program.inputs is not None and any(
                    isinstance(snap(t.head), Term) and (snap(t.head).fn, snap(t.head).arity) == (fn, arity)
                    for t in program.inputs):
                continue
            for i in range(arity):
                c = _classify(program, rules, i)
                if c is not None:
                    splits[(fn, arity)] = (i, c[0], c[1])
                    break

        default_fn, spec_fn = {}, {}
        for key in splits:
            default_fn[key] = program._gen_functor(key[0] + '_dft')
            spec_fn[key] = program._gen_functor(key[0] + '_spc')

        def split_read(t):
            "If t reads a split predicate at a variable position, return (default_lit, spec_lit); else None."
            t = snap(t)
            if not isinstance(t, Term) or is_builtin(t):
                return None
            key = (t.fn, t.arity)
            if key not in splits:
                return None
            i = splits[key][0]
            arg = snap(t.args[i])
            if not is_var(arg):
                return None            # constant read -> leave reading recovered f
            return _drop_arg(t, i, default_fn[key]), Term(spec_fn[key], *t.args)

        new_rules = []

        # 1. definitions of the split predicates: default (projected) + spec (renamed)
        for key, (i, spec, gen) in splits.items():
            fn, arity = key
            for r in gen:
                r = fresh(r)
                head = snap(r.head)
                vanished_var = snap(head.args[i])
                nh = _drop_arg(head, i, default_fn[key])
                r2 = Rule(nh, *r.body)
                if vanished_var not in term_vars(r2):
                    pass   # projected away on the head; body unaffected
                new_rules.append(r2)
            for r in spec:
                r = fresh(r)
                head = snap(r.head)
                new_rules.append(Rule(Term(spec_fn[key], *head.args), *r.body))
            # recovery so that direct/output reads of f still work
            fvars = [Var() for _ in range(arity)]
            new_rules.append(Rule(Term(fn, *fvars),
                                  Term(default_fn[key], *[fvars[j] for j in range(arity) if j != i])))
            new_rules.append(Rule(Term(fn, *fvars), Term(spec_fn[key], *fvars)))

        # 2. consumers: split each body read of a split predicate at a variable
        defined = set(splits)
        for r in program.rules:
            head = snap(r.head)
            if (head.fn, head.arity) in defined:
                continue   # already handled as a definition above
            # find split reads in the body
            split_positions = [k for k, b in enumerate(r.body) if split_read(b) is not None]
            if not split_positions:
                new_rules.append(fresh(r))
                continue
            # split on the first such read (handle one per rule; common case)
            k = split_positions[0]
            dft_lit, spc_lit = split_read(r.body[k])
            # default version
            body_d = list(r.body); body_d[k] = dft_lit
            rd = Rule(head, *body_d)
            vanished = term_vars(r) - term_vars(rd)
            summed = vanished - term_vars(head)
            for v in sorted(summed, key=str):
                rd = Rule(rd.head, *rd.body, program.Semiring.multiple(float('inf')))
            new_rules.append(rd)
            # spec version
            body_s = list(r.body); body_s[k] = spc_lit
            new_rules.append(Rule(head, *body_s))

        super().__init__('value-split', program, new_rules)
        self._splits = splits

        from dyna.analyze.range_restriction import is_rule_range_restricted
        self.residual_layer = self.spawn(
            [r for r in self.rules if not is_rule_range_restricted(self, r)])
        self.engine_layer = self.spawn(
            [r for r in self.rules if is_rule_range_restricted(self, r)])
