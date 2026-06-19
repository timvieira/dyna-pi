"""Deforestation passes for producer/consumer algebraic data channels.

This module currently implements a deliberately small, conservative pass for the
classic pattern

    gen(A, Acc, X) * equal(X, In)

where `gen` is a difference-list CFG generator and `equal` is structural list
equality against an observed input.  The residual program uses suffix-list tails
as finite states and introduces a span predicate.

The pass is intentionally phrased as a Dyna-to-Dyna transformation: it removes
only the recognized generator/equality definitions and emits ordinary Dyna rules.
It does not require demand-driven execution, and it does not rely on a
parser-specific CKY template beyond the residual predicate shape discovered from
this producer/consumer pattern.
"""

from dataclasses import dataclass

from dyna import Product, Rule, Subst, Term, TransformedProgram, Var, fresh


NIL = Term('$nil')


def CONS(head, tail):
    return Term('$cons', head, tail)


@dataclass(frozen=True)
class DifferenceListDeforestationSpec:
    """Names used by the difference-list/intersection idiom.

    The defaults match the example in the tests.  `span_fn` and `suffix_fn` may
    be left as `None`; the transform will choose `$span`/`$suffix`, avoiding
    collisions with symbols already present in the program.
    """

    gen_fn: str = 'gen'
    equal_fn: str = 'equal'
    rule_term_fn: str = 'rule_term'
    rule_bin_fn: str = 'rule_bin'
    root_fn: str = 'root'
    source_fn: str = 'source_string'
    eq_fn: str = 'eq'
    span_fn: str | None = None
    suffix_fn: str | None = None


def _matches(rule, head_pattern, body_patterns):
    """Yield matches of `head_pattern += body_patterns` against `rule`.

    Body matching is conjunctive/subset-style: `body_patterns` may cover a
    subset of the rule body, and the unmatched body factors are returned as
    residual factors.  This lets the transform preserve extra weights/guards on
    the source rules.
    """

    subst = Subst().cover(head_pattern, rule.head)
    if subst is None:
        return
    yield from Product(body_patterns).covers(rule.body, subst)


def _require_one(program, head_pattern, body_patterns, label):
    found = []
    for i, rule in enumerate(program):
        for subst, _align, remaining in _matches(rule, head_pattern, body_patterns):
            found.append((i, rule, subst, remaining))
            break
    if len(found) != 1:
        raise ValueError(f'expected exactly one {label} rule, found {len(found)}')
    return found[0]


def _require_at_least_one(program, head_pattern, body_patterns, label):
    found = []
    for i, rule in enumerate(program):
        for subst, _align, remaining in _matches(rule, head_pattern, body_patterns):
            found.append((i, rule, subst, remaining))
            break
    if not found:
        raise ValueError(f'expected at least one {label} rule')
    return found


def _compile_difference_list_intersection(parent, spec):
    span_fn = spec.span_fn or parent._gen_functor('$span')
    suffix_fn = spec.suffix_fn or parent._gen_functor('$suffix')

    # ------------------------------------------------------------------
    # Recognize terminal generator rule:
    #   gen(A, Acc, [W|Acc]) += rule_term(A, W) * extra.
    A = Var('A'); Acc = Var('Acc'); W = Var('W')
    term_i, term_rule, term_subst, term_remaining = _require_one(
        parent,
        Term(spec.gen_fn, A, Acc, CONS(W, Acc)),
        [Term(spec.rule_term_fn, A, W)],
        'difference-list terminal generator',
    )

    # Recognize binary generator rule:
    #   gen(A, Acc, X) += rule_bin(A,B,C) * gen(C,Acc,Mid) * gen(B,Mid,X) * extra.
    A = Var('A'); Acc = Var('Acc'); X = Var('X')
    B = Var('B'); C = Var('C'); Mid = Var('Mid')
    bin_i, bin_rule, bin_subst, bin_remaining = _require_one(
        parent,
        Term(spec.gen_fn, A, Acc, X),
        [
            Term(spec.rule_bin_fn, A, B, C),
            Term(spec.gen_fn, C, Acc, Mid),
            Term(spec.gen_fn, B, Mid, X),
        ],
        'difference-list binary generator',
    )

    # Recognize structural list equality.  These rules are removed after fusion.
    base_i, _base_rule, _base_subst, _base_remaining = _require_one(
        parent,
        Term(spec.equal_fn, NIL, NIL),
        [],
        'structural equality base',
    )

    X0 = Var('X'); Xs = Var('Xs'); Y0 = Var('Y'); Ys = Var('Ys')
    rec_i, _rec_rule, _rec_subst, _rec_remaining = _require_one(
        parent,
        Term(spec.equal_fn, CONS(X0, Xs), CONS(Y0, Ys)),
        [Term(spec.equal_fn, Xs, Ys), Term(spec.eq_fn, X0, Y0)],
        'structural equality recursive case',
    )

    # Recognize all top-level intersections of a root generator with the source.
    S = Var('S'); Str = Var('Str'); In = Var('In')
    goal_matches = _require_at_least_one(
        parent,
        Var('Head'),
        [
            Term(spec.root_fn, S),
            Term(spec.gen_fn, S, NIL, Str),
            Term(spec.source_fn, In),
            Term(spec.equal_fn, Str, In),
        ],
        'top-level generator/source intersection',
    )

    remove = {term_i, bin_i, base_i, rec_i, *(i for i, *_ in goal_matches)}
    new_rules = [rule for i, rule in enumerate(parent) if i not in remove]

    # ------------------------------------------------------------------
    # Suffix-state automaton for the observed source list.
    #   $suffix(In)   += source_string(In).
    #   $suffix(Rest) += $suffix([V|Rest]).
    In = Var('In')
    V = Var('V')
    Rest = Var('Rest')
    new_rules.append(fresh(Rule(
        Term(suffix_fn, In),
        Term(spec.source_fn, In),
    )))
    new_rules.append(fresh(Rule(
        Term(suffix_fn, Rest),
        Term(suffix_fn, CONS(V, Rest)),
    )))

    # Terminal residual:
    #   span(A, [V|Acc], Acc) += suffix([V|Acc]) * rule_term(A,W) * eq(W,V) * extra.
    A = term_subst(Var('A'))   # will not work: use stable pattern vars below
    # The comments above describe the source-level binding.  Recreate the source
    # pattern variables so we can read their substitutions from the match.
    TA = Var('A'); TAcc = Var('Acc'); TW = Var('W')
    # Re-match in a tiny local scope to get handles for the actual source variables.
    # This avoids relying on variable names: the substitutions map pattern Var
    # objects to the variables/terms in the source rule.
    term_pat_head = Term(spec.gen_fn, TA, TAcc, CONS(TW, TAcc))
    term_pat_body = [Term(spec.rule_term_fn, TA, TW)]
    [(term_subst2, _align, _remaining)] = list(_matches(term_rule, term_pat_head, term_pat_body))
    A = term_subst2(TA); Acc = term_subst2(TAcc); W = term_subst2(TW)
    V = Var('V')
    start_tail = CONS(V, Acc)
    term_extra = [term_rule.body[k] for k in term_remaining]
    new_rules.append(fresh(Rule(
        Term(span_fn, A, start_tail, Acc),
        Term(suffix_fn, start_tail),
        Term(spec.rule_term_fn, A, W),
        Term(spec.eq_fn, W, V),
        *term_extra,
    )))

    # Binary residual:
    #   span(A, X, Acc) += rule_bin(A,B,C) * span(B,X,Mid) * span(C,Mid,Acc) * extra.
    BA = Var('A'); BAcc = Var('Acc'); BX = Var('X')
    BB = Var('B'); BC = Var('C'); BMid = Var('Mid')
    bin_pat_head = Term(spec.gen_fn, BA, BAcc, BX)
    bin_pat_body = [
        Term(spec.rule_bin_fn, BA, BB, BC),
        Term(spec.gen_fn, BC, BAcc, BMid),
        Term(spec.gen_fn, BB, BMid, BX),
    ]
    [(bin_subst2, _align, _remaining)] = list(_matches(bin_rule, bin_pat_head, bin_pat_body))
    A = bin_subst2(BA); Acc = bin_subst2(BAcc); X = bin_subst2(BX)
    B = bin_subst2(BB); C = bin_subst2(BC); Mid = bin_subst2(BMid)
    bin_extra = [bin_rule.body[k] for k in bin_remaining]
    new_rules.append(fresh(Rule(
        Term(span_fn, A, X, Acc),
        Term(spec.rule_bin_fn, A, B, C),
        Term(span_fn, B, X, Mid),
        Term(span_fn, C, Mid, Acc),
        *bin_extra,
    )))

    # Top-level residual(s): replace root/gen/source/equal by root/source/span.
    for _i, goal_rule, _subst, remaining in goal_matches:
        GS = Var('S'); GStr = Var('Str'); GIn = Var('In')
        H = Var('Head')
        goal_pat_head = H
        goal_pat_body = [
            Term(spec.root_fn, GS),
            Term(spec.gen_fn, GS, NIL, GStr),
            Term(spec.source_fn, GIn),
            Term(spec.equal_fn, GStr, GIn),
        ]
        [(goal_subst, _align, _remaining)] = list(_matches(goal_rule, goal_pat_head, goal_pat_body))
        S = goal_subst(GS); In = goal_subst(GIn)
        extra = [goal_rule.body[k] for k in remaining]
        new_rules.append(fresh(Rule(
            goal_rule.head,
            Term(spec.root_fn, S),
            Term(spec.source_fn, In),
            Term(span_fn, S, In, NIL),
            *extra,
        )))

    return new_rules


class DeforestDifferenceLists(TransformedProgram):
    """Fuse a difference-list generator with structural equality on its output.

    The residual program uses suffix list tails as chart states.  For a source
    list of length `n`, there are only `n+1` suffix states, so the binary CFG
    rule has the usual cubic span/split search space.
    """

    def __init__(self, parent, **kwargs):
        self.spec = DifferenceListDeforestationSpec(**kwargs)
        rules = _compile_difference_list_intersection(parent, self.spec)
        super().__init__('deforest-difference-lists', parent, rules)


def deforest_difference_lists(program, **kwargs):
    """Return a Dyna-to-Dyna deforestation of the recognized DL/intersection idiom."""

    return DeforestDifferenceLists(program, **kwargs)
