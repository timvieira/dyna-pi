"""
Pretty printer for term (term, var, rule, constants, etc)
"""
# TODO: need to escape the single quote in these cases
#  19: $inst(2, p("<.>", '#I'', '#K'') / p(".", '#I'', '#K'')) += 1.0.

import re
from dyna.term import Var, Term, snap, NIL, snap, vars, OrderedSet
from dyna.rule import Rule
from dyna.syntax import ops, ChainedCompare, BinOp, UnaryOp
#from arsenal import colors
from arsenal.terminal import superscript, subscript


# TODO: tie in with the parser to see how whether the current functor is a known binop.
binops = {f.op: f for f in ops if isinstance(f, BinOp)}

# [2022-01-02 Sun] Below, we patch the binop table to ordering relations, which
# are parsed specially to allow for operator chaining.
binops['<'] = \
binops['>'] = \
binops['>='] = \
binops['<='] = ChainedCompare(5)

binops['\\'] = binops['\\\\']   # annoying patch

unaryops = {str(f.op) for f in ops if isinstance(f, UnaryOp)}


AGG = {'+=', '=', '->', 'max=', 'min=', 'set=', 'bag=', ':-', ':=', '*=', '&=',
       '|=', '?='}


def binop(x):
    "find Binop instance for x's functor or return None"
    x = snap(x)
    if isinstance(x, Term):
        return binops.get(snap(x.fn))


def priority(x):
    return float('inf') if x is None else x.priority


def assoc(x):
    return None if x is None else x.assoc


class parens:
    def __init__(self, x):
        self.x = x


def pp(_X, **kwargs):
    return PrettyPrinter(**kwargs)(_X)


class Escape:
    def __init__(self, x):
        assert isinstance(x, str)
        self.x = x
    def __repr__(self):
        return self.x


class html_colors:
    magenta = '<span style="color: #aa6699;">%s</span>'
    blue = '<span style="color: blue;">%s</span>'
    red = '<span style="color: red;">%s</span>'
    green = '<span style="color: green;">%s</span>'
    render = lambda x: x


class no_colors:
    magenta = '%s'
    blue = '%s'
    red = '%s'
    green= '%s'
    render = lambda x: x


import arsenal
ansi_colors = arsenal.colors


class PrettyPrinter:
    "Stateful pretty printer."

    def __init__(self, vs=None, color=True, **kwargs):
        if vs is None: vs = {}
        self.vs = vs
        self.kwargs = kwargs
        self.var_color = {}
        self.color = None
        self.set_color(color)

    def set_color(self, color):
        if color is True:
            self.color = ansi_colors
        elif color == 'html':
            self.color = html_colors
        else:
            self.color = no_colors

    def print(self, *args, **kwargs):
        print(' '.join(a if isinstance(a, str) else self(a)
                       for a in args), **kwargs)

    def __call__(self, x, color=None):
        if color is not None:
            was = self.color
            self.set_color(color)
            y = self.wrap(x)
            self.color = was
            return y
        else:
            return self.wrap(x)

    def wrap(self, x):
        x = snap(x)

        #assert x is not None

        if isinstance(x, parens):
            return f'({self(x.x)})'

        elif isinstance(x, tuple):
            if len(x) == 1: return f'({self(x[0])},)'
            return f'({", ".join(self(y) for y in x)})'

        elif isinstance(x, (frozenset, set, OrderedSet)):
            return f'{{{", ".join(self(y) for y in x)}}}'

        elif isinstance(x, list):
            return f'[{", ".join(self(y) for y in x)}]'

        elif isinstance(x, dict):
            return f'{{{", ".join(self(k) + ": " + self(v) for k,v in x.items())}}}'

        elif isinstance(x, Var):

            # Special handling for variable display names that occur more
            # than once, but with different underlying varibles!
            if x.name not in self.vs:
                self.vs[x.name] = {}

            # we have seen this name before
            # but is it actually the *same* variable?
            if id(x) not in self.vs[x.name]:   # has a rename
                dups = len(self.vs[x.name])
                if dups == 0:
                    # first instance keeps the nice name
                    self.vs[x.name][id(x)] = x.name
                else:
                    # later instance get an ugly auto-generated name
                    self.vs[x.name][id(x)] = f'${x.name}{dups}'

            return self.var_color.get(id(x), '%s') % self.vs[x.name][id(x)]

        elif isinstance(x, bool):
            return str(x).lower()   # booleans and null are lower case

        elif isinstance(x, str):
            x = repr(x)    # should be a double-quoted string, unlike Python
            x = f'"{x[1:-1]}"'   # TODO: need to redo escapes
            return x

        elif isinstance(x, Rule):

            # enable variable coloring in rules
            # TODO: disable head variable coloring for nested rules
            if self.color:
                bs = vars(x.body)
                hs = vars(x.head)
                local = bs - hs
#                for v in (hs | bs):
#                    var_color[id(v)] = colors.white
                # local variables are highlighted in grey

                for v in vars(x):
                    self.var_color[id(v)] = self.color.green
                
#                for v in local:
#                    self.var_color[id(v)] = self.color.green
#                for v in hs:
#                    self.var_color[id(v)] = self.color.green
#                    self.var_color[id(v)] = colors.blue
#                # non-range-restricted variables are highlighted in red.
#                for v in (hs - bs):
#                    self.var_color[id(v)] = self.color.dark.white

            # put parens around heads that are binary operators
            # TODO: handle other cases as well, e.g., unary operators
            h = self(x.head)
            if isinstance(x.head, Term) and x.head.arity == 2 and (x.head.fn in binops):
                h = f'({h})'

            #pre = (colors.dark.white % f'{x.i}:') if hasattr(x, 'i') else ''
            pre = ''
            if x.body:

                def wrap(z):
                    if isinstance(z, Rule): return parens(z)
                    if not isinstance(z, (Var, Term)):
#                        if hasattr(z, 'fsa'):
#                            return Escape(f'<div style="display: inline; border:thin solid red;">{z.fsa.min()._repr_html_()}</div>')
#                        if hasattr(z, '_repr_html_'):
#                            return z._repr_html_()
#                        elif hasattr(z, '_repr_svg_'):
#                            return z._repr_svg_()
#                        else:
                        return Escape(self.color.render(self.color.magenta % (z,)))

                    return z

                B = wrap(x.body[0])
                for i in range(1, len(x.body)):
                    B = Term('*', B, wrap(x.body[i]))

                aggr = self.color.blue % '+='

                return f'{pre}{h} {aggr} {self(B)}'
            else:
                return f'{pre}{h}'

        elif isinstance(x, Term):
            return self.pp_term(x)

        else:
            return repr(x)

    def pp_term(self, x):
        x = snap(x)
        fn = snap(x.fn)

        if not isinstance(fn, str):
            return f'{self(fn)}({",".join(self(y) for y in x.args)})'

#        elif isinstance(x, Rule):
#            if x.body:
#                return f'{self(x.head)} += {" * ".join(self(b) for b in x.body)}.'
#            else:
#                return f'{self(x.head)}.'

        elif x.arity == 0:
            if x == NIL:
                return self.pp_list(x)
            elif fn in {'?', '!', '*'}:
                return fn
            else:
                return self.pp_functor(fn)

        elif x.arity == 1:
            fn = str(fn)

            if fn in unaryops:
                if fn == 'not': fn = 'not '
                [y] = x.args

                # XXX: remove parens when precedence is clear.
                if isinstance(y, Term) and y.arity == 2 and y.fn in binops:
                    return f'{fn}({self(y)})'
                return f'{fn}{self(y)}'

            else:
                return self.pp_term_default(x)

        elif x.arity == 2:
            assert not isinstance(fn, Var)
            # Handle some overrides

            if fn == '$cons':    # pretty-print `$cons/2` lists.
                return self.pp_list(x)

#            elif fn == 'is':
#                return self(Term('↦', x.args[1], x.args[0]))

            else:
                return self.pp_infix(x) or self.pp_term_default(x)

        else:
            return self.pp_term_default(x)

    def pp_infix(self, x):
        x = snap(x)
        fn = snap(x.fn)
        assert isinstance(fn, str)

        # overrides for whitespace
        infix = {
            # comma and colon have different spacing
            ',': ', ',
            ';': '; ',
            ':': ':',
            '>': ' > ',
            '>=': ' >= ',
            '<=': ' <= ',
            '<': ' < ',
            '==>': ' ==> ',
            ':-': ' :- ',
            '->': ' -> ',
        }.get(fn)

        if (fn in binops) or (infix is not None):
            # The default display is spaces around the infix operator
            infix = infix or f' {fn} '
            [_, a, b] = x

            #print('==========================')
            #print('pretty printing infix binop:', 'fn:', func(x), func(a), func(b))
            #print('  x=', func(x), priority(func(x)), assoc(func(x)))
            #print('  a=', func(a), priority(func(a)), assoc(func(a)))
            #print('  b=', func(b), priority(func(b)), assoc(func(b)))

            # [2020-04-16 Thu] Handle operator associativity. The expression
            # `1+2+3+4` parses as left-assoc, i.e., `((1+2)+3)+4`. We can omit
            # the parens when pretty printing because they can be inferred from
            # context.  On the other hand, 1+(2+(3+4)) uses parens to override
            # the parser's left-assoc. So it should print with the parens in
            # order to parse as the same term.  (This is a little funny because
            # these expressions are semantically equivalent in the case of + on
            # numbers.)  Some operators are not associative (semantically), for
            # example the pairing operator an implementation may parse as left
            # or right assoc by convention.

            A = self(a); B = self(b)

            if priority(binop(a)) <= priority(binop(x)):
                if (priority(binop(a)) == priority(binop(x))
                    and assoc(binop(a)) == 'L'):
                    pass
                else:
                    A = f'({A})'

            if priority(binop(b)) <= priority(binop(x)):
                if (priority(binop(b)) == priority(binop(x))
                    and assoc(binop(b)) == 'R'):
                    pass
                else:
                    B = f'({B})'

            return f'{A}{infix}{B}'

    def pp_term_default(self, x):
        [fn, *args] = snap(x)
        fn = snap(fn)
        return f'{self.pp_functor(fn)}({",".join(self(a) for a in args)})'

    def pp_functor(self, x):
        y = str(x)
        # the pattern below should match the pattern for `FUNCTOR1` in the
        # front-end parser.
        #
        # TODO: The patterm below is going to be perpetually out of date with
        # the functor pattern in the grammar.  Figure out how to keep them in
        # sync to avoid the headache.
        if not re.match("^([$_]*['\"a-zαβγδεζηθικλμνξο∂πρστυφχψωϯ☐¿$♦]['\"a-zA-Z0-9_αβγδεζηθικλ∂μνξοπρστυφχψω∘ϯ♦$☐˽ΑΒΓΔΕΖΗΘΙΚΛΜΝΞΟΠΡΣΤΥΦΧΨΩ₀₁₂₃₄₅₆₇₈₉]*)$", y):
            y = f"'{y}'"
        return y

    def pp_list(self, x):
        xs = []
        y = x
        while True:
            y = snap(y)
            if isinstance(y, Term) and y == NIL and y.arity == 0:
                return f'[{",".join(self(x) for x in xs)}]'
            elif isinstance(y, Term) and y.fargs[0] == '$cons':
                [_,a,y] = y.fargs
                xs.append(a)
            else:
                return f'[{",".join(self(x) for x in xs)}|{self(y)}]'
