from lark.lark import Lark
from lark.visitors import Transformer
from lark.exceptions import LarkError

from functools import lru_cache

from dyna.exceptions import DynaParserException
from dyna.term import Term, Var, fresh, flatten, flatten_op
from dyna.rule import Rule


class DynaTransformer(Transformer):

    def __init__(self):
        self.i = 0
        super().__init__()

    #__________________________________________________________________________
    # Input-output declarations

    def params(self, x):
        [t,arg,_] = x
        return Rule(Term('$declare', Term(t.strip()[:-1], arg)))

    #__________________________________________________________________________
    # List pattern-matching syntax.

    def list_pattern_rest(self, x):
        *xs, y = x
        for x in reversed(xs):
            y = Term('$cons', x, y)
        return y

    def list_pattern(self, xs):
        y = Term('$nil')
        for x in reversed(xs):
            y = Term('$cons', x, y)
        return y

    def list_pattern_empty(self, _):
        return Term('$nil')

    #__________________________________________________________________________
    # binary operators

    def chained_compare(self, x):
        if len(x) == 1:
            return x[0]
        else:
            # take adjacent pairs:
            #   0    1   2    3   4    5   6    7   8
            # [x0, op0, x1, op1, x2, op2, x3, op3, x4, ...]
            # (x0  op0  x1)     (x2  op2  x3)      ...
            #          (x1  op1  x2)     (x3  op3  x4)   ...
            conjunct = None
            for i in range(0, len(x)-2):
                if i % 2 == 1: continue
                a, op, b = x[i:i+3]
                y = Term(str(op.value), a, b)
                conjunct = Term(',', conjunct, y) if i > 0 else y
        return conjunct

    def binop(self, x):
        [a,op,b] = x
        if op == 'for':        # "for" desugars as "," with arguments swapped.
            return Term(',', b, a)
        else:
            return Term(str(op), a, b)

    def unary_op(self, x):
        [op, a] = x
        return Term(str(op), a)

    def noop(self, x):
        [x] = x
        return x

    #__________________________________________________________________________
    # rule and rules

    def rule(self, x):
        [a, _] = x
        if isinstance(a, Term) and (a.fn in AGGRS):
            [_, head, value] = a
            return fresh(Rule(head, *(bb for b in flatten(value) for bb in flatten_op(b, '*'))))
        else:
            return fresh(Rule(a))

    def rules(self, rs):
        return rs

    #___________________________________________________________________________
    # variables, functors, terms

    def functor(self, x):
        [token] = x
        return str(token.value)

    def single_quote_functor(self, x):
        [token] = x
        return str(token.value)[1:-1]   # drop the single quotes

    @lru_cache(None)
    def _make_variable(self, x):
        return Var(x)

    def variable(self, x):
        [token] = x
        return self._make_variable(str(token.value))

    def anon_var(self, _=None):
        self.i += 1
        return self._make_variable(f'$Gen{self.i}')

    def args(self, x):
        return list(x)

    def term(self, x):
        if len(x) == 1:
            [fn] = x
            return Term(fn)
        else:
            [fn, args] = x
            assert fn != '$term'
            return Term(fn, *args)

    def tick_op(self, x):
        from dyna import Symbol
        [value] = x
        return Symbol(str(value))

    #___________________________________________________________________________
    # Literals

    def inf(self, _):
        return float('inf')

    def true(self, _):
        return True

    def false(self, _):
        return False

    def string(self, x):
        [s] = x
        return s[1:-1].replace('\\"', '"')   # remove outer quotes and escaped quotes

    def float(self, x):
        [a] = x
        return float(a)

    def int(self, x):
        [a] = x
        return int(a)


class Parser:

    def __init__(self, grammar):
        self.grammar = grammar
        self.transformer = DynaTransformer()
        self.parser = Lark(grammar,
                           parser = 'lalr',
                           lexer = 'contextual',
                           propagate_positions = True,
                           transformer = self.transformer)

    def __call__(self, src):
        "Returns the list of rules contained in `src`."
        try:
            return self.parser.parse(src)
        except LarkError as e:
            raise DynaParserException('\n' + e.get_context(src))

    def term(self, x, freshen=True):
        assert isinstance(x, str), f'got {type(x).__name__}: {x!r}'
        y = self(f'({x})?')
        return fresh(y) if freshen else y


grammar = r"""
%import common.ESCAPED_STRING
%import common.WS
%import common.NEWLINE
%ignore WS
%ignore COMMENT

///////////////////////////////////////////////////////////////////////////////
// Input/Output declarations

PARAMS.10000000: /(params|inputs?|outputs?):\s+/
params: PARAMS expr1 EOR

///////////////////////////////////////////////////////////////////////////////
// LEXERS

AGG.100000: ( /[+]=/ | /:-/ )

FLOAT.10000000: /[\-+]?[0-9]*((\.[0-9]+(e[\-+]?[0-9]+)?)|(e[\-+]?[0-9]+))/    // 1e5 and 1.0 and -1.0e+5

INT: /[\-+]?[0-9]+/

VAR: /[$]*[A-ZΑΒΓΔΕΖΗΘΙΚΛΜΝΞΟΠΡΣΤΥΦΧΨΩ][a-zA-Z0-9'"_αβγδεζηθικλμνξοπρστυφχψωΑΒΓΔΕΖΗΘΙΚΛΜΝΞΟΠΡΣΤΥΦΧΨΩ₀₁₂₃₄₅₆₇₈₉]*/

EQ: "="
LTE: "<="
GTE: ">="
GT: ">"
LT: "<"

FUNCTOR1: /([$]?[a-zαβγδεζηθικλμνξοπρστυφχψω∂]["'a-zA-Z0-9_αβγδεζηθικλμ$νξοπρστυφχψωΑΒΓΔΕΖΗΘΙΚΛΜΝΞΟΠΡΣΤΥΦΧΨΩ∂₀₁₂₃₄₅₆₇₈₉]*)/
FUNCTOR2: /('[^']+')/

COMMENT: "%" /[^\n\r]*/ (NEWLINE|/$/)

EOR: /\.\s+/
   | /\.\s*$/
   | /\.(?=[^\d])/

///////////////////////////////////////////////////////////////////////////////
// LANGUAGE

?start:  rules | query
?query: expr1 "?"

rules: ( rule | params )*

rule: expr1  EOR

literal: ESCAPED_STRING -> string
       | INT            -> int
       | FLOAT          -> float
       | "true"         -> true
       | "false"        -> false
       | list           -> noop
       | /inf/          -> inf
       | /∞/            -> inf

variable: VAR  -> variable
        | "_"  -> anon_var

term: functor args
    | "`" expr1 "`"      -> tick_op
    | functor

args: "(" expr2 [ "," expr2 ]* [","]? ")"
    | "(" ")"

list: "[" expr3 [ "," expr3 ]* "|" expr3 "]" -> list_pattern_rest
    | "[" expr3 [ "," expr3 ]* "]"           -> list_pattern
    | "[" "]"                                -> list_pattern_empty

functor: FUNCTOR1 -> functor
       | FUNCTOR2 -> single_quote_functor

?p0: term
   | literal
   | variable
   | "(" expr1 ")"

"""

#_______________________________________________________________________________
# Infrastructure for operator arity, fixity, associativity, and precedence

# Constants that describe operator associativity
R = 'R'; L = 'L'; N = 'N'
prefix, postfix = 'prefix', 'postfix'


class Op:
    def __init__(self, *, op, arity, priority, evaluation, callback):
        assert isinstance(op, str), [type(op), op]
        self.op = str(op)
        self.arity = arity
        self.priority = priority
        self.evaluation = evaluation
        self.callback = callback
    def __repr__(self):
        return f'{self.__class__.__name__}({self.op})'


class BinOp(Op):
    def __init__(self, op, priority, assoc, callback=None, evaluation=None):
        assert assoc in (R, L, N), assoc
        assert isinstance(priority, (int, float)), [type(priority), priority]
        self.assoc = assoc
        if callback is None: callback = 'binop'
        super().__init__(op=op, arity=2, priority=priority, evaluation=evaluation, callback=callback)

    def render(self, OP, i):
        if self.assoc == L: l, r = i, i-1
        if self.assoc == R: l, r = i-1, i
        if self.assoc == N: l, r = i-1, i-1
        return f'?p{i}: p{l} {OP} p{r} -> {self.callback}  |  p{i-1} -> noop'


class UnaryOp(Op):
    def __init__(self, op, priority, position='prefix', callback=None, evaluation=None):
        assert position in {prefix, postfix}
        self.position = position
        if callback is None: callback = 'unary_op'
        super().__init__(op=op, arity=1, priority=priority, evaluation=evaluation, callback=callback)

    def render(self, OP, i):
        if self.position == 'prefix':
            return f'?p{i}: {OP} p{i} -> {self.callback}  |  p{i-1} -> noop'
        else:
            return f'?p{i}: p{i} {OP} -> {self.callback}  |  p{i-1} -> noop'


class NullOp(Op):
    def __init__(self, op, priority, callback=None, evaluation=None):
        if callback is None: callback = 'term'
        super().__init__(op=op, arity=0, priority=priority, evaluation=evaluation, callback=callback)

    def render(self, OP, i):
        return f'?p{i}: {OP} -> {self.callback}  |  p{i-1} -> noop'


class ChainedCompare:
    def __init__(self, priority):
        self.op = None
        self.priority = priority
    def render(self, _, i):
        # [2019-03-10 Sun] Note: We needed to make chained comparisons and
        # ordinary comparisons one rule.
        return f"""?p{i}: p{i-1} ( (LT|LTE|GT|GTE) p{i-1} )*     -> chained_compare"""


def add_ops(ops):

    Sym2Lex = {'=': 'EQ',
               '<=': 'LTE',
               '>=': 'GTE',
               '>': 'GT',
               '<': 'LT'}

    G = []
    expr1 = expr2 = expr3 = None
    for i, z in enumerate(sorted(ops, key=lambda x: -x.priority), start=1):

        # Figure out where these special positions are:
        #  - expr1: most general context
        #  - expr2: doesn't take the top-level comma as an operator (used in term and list)
        #  - expr3: list syntax: doesn't take the top-level comma and `|` has special meaning.
        if z.op == '|': expr3 = i-1
        if z.op == ',': expr2 = i-1
        expr1 = i

        if z.op is not None:
            if z.op in Sym2Lex:      # avoid lexer conflicts on '='
                OP = Sym2Lex[z.op]
            else:
                G.append(f'OP{i}: "{z.op}"')
                Sym2Lex[z.op] = OP = f'OP{i}'
        else:
            OP = None

        G.append(z.render(OP, i))

    G.extend([
        f'?expr1: p{expr1}',
        f'?expr2: p{expr2}',
        f'?expr3: p{expr3}',
    ])

    return '\n'.join(r.strip() for r in G)


AGGRS = [
#    'min=',
#    'max=',
#    'set=',
#    'bag=',
#    'def=',
    ':-',
    '+=',
#    '*=',
#    '&=',
#    '?=',
#    ':=',
#    '|=',
#    '->',
#    '=',
]


# Note: Be careful not to include duplicate operations as they cause some
# strange parsing errors.
ops = [
    # chained comparison operations
    ChainedCompare(5),

    # aggregators
    BinOp('?=',   0,    N),
    BinOp('+=',   0,    N),
    BinOp('*=',   0,    N),
    BinOp(':=',   0,    N),
    BinOp('min=', 0,    N),
    BinOp('max=', 0,    N),
    BinOp(':-',   0,    N),
    BinOp('->',   0,    N),
    BinOp('|=',   0,    N),
    BinOp('&=',   0,    N),
    BinOp('set=', 0,    N),
    BinOp('bag=', 0,    N),
    BinOp('def=', 0,    N),

    # binary operations
    BinOp(   '|',     2, R),
    BinOp(    ',',  1.1, L),
    BinOp(   '^',     8, R),
    BinOp(   '/',   7.5, L),
    BinOp(  '//',   7.5, L),
    BinOp( r'\\',   7.5, L),    # single backslash
    BinOp(   '*',     7, L),
    BinOp(   '@',   7.1, L),
    BinOp(   '#',   7.2, L),
    BinOp(   '+',     6, L),
    BinOp(   '-',   6.5, L),
    BinOp( 'mod',   4.0, L),
    BinOp(   ':',   4.1, L),
    BinOp(  '==',     4, N),
    BinOp(  '!=',     4, N),
    BinOp(  'is',   3.9, R),
    BinOp(  '<-',   3.9, R),
    BinOp( '<--',   3.9, R),
    BinOp( '-->',   3.9, R),
    BinOp(  '~>',   3.9, R),
    BinOp(  '->',   3.9, R),
    BinOp(  '<~',   3.9, R),
    BinOp(   '~',   3.9, R),
    BinOp(  '::',   3.9, R),
    BinOp(  '↦',   3.8, L),
    BinOp(  '=>',   3.8, R),
    BinOp(  'in',     4, N),
    BinOp(  '∈',     4, N),
    BinOp(   '!',     4, L),
    BinOp( '=/=',     4, N),
    BinOp(   '&',     3, R),
    BinOp(   '=',   1.5, N),
    BinOp( 'for',  1.03, R),
    BinOp(   ';',     0, L),

    # nullary operations
    NullOp(   '*', 110),
    NullOp(   '!', 109),
    NullOp(   '?', 109),

    # prefix operations
    UnaryOp('not',  9),
    UnaryOp(  '+',  9),
    UnaryOp(  '-',  9),
    UnaryOp(  '~',  9),
    UnaryOp(   '&', 9),
    UnaryOp(   '*', 9),
    UnaryOp(   '!', 9.1),
    UnaryOp(   '?', 9),

    # postfix operations
    UnaryOp(    '!', 9.1, position='postfix'),
    #UnaryOp(    '?',   9, position='postfix'),

]


parser = Parser(grammar + add_ops(ops))
term = parser.term
