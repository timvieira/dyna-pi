import os, hashlib, re, subprocess, webbrowser
import numpy as np

from ansi2html import Ansi2HTMLConverter
from arsenal import colors
from contextlib import contextmanager
from distutils.spawn import find_executable
from IPython.display import display, SVG, Image, HTML
from path import Path


from collections import Counter
def FrozenBag(elements):
    return frozenset(Counter(elements).items())

def display_groundings(*args, **kwargs):
    return display(HTML(render_groundings(*args, **kwargs)))

def render_groundings(self, chart=None, precision=None):
    "Show instaniations of program rules against chart."
    lines = ['<table style="font-family: Courier New,monospace;">']
    if chart is None: chart = self.agenda()
    for i, r in enumerate(self.rules):
        lines.append(f"""\
        <tr style="border: thin solid black;"><th></th>
        <th style="text-align: left; vertical-align: top;">{r.__repr__(color=False)}
        </th></tr>
        """)
        with self._fresh(r) as r:
            for v in chart[r.body]:
                if isinstance(v, tuple) and len(v) >= 1: v = np.prod(v)
                if precision is not None: v = round(v, precision)
                lines.append(f"""\
                <tr><td>{v}</td><td style="text-align: left; vertical-align: top;">
                {r.__repr__(color=False)}
                </td></tr>""")
    lines.append('</table>')
    return '\n'.join(lines)


def render_chart_and_groundings(self, chart, new_chart, **kwargs):
    left = chart.sort().__repr__(numbered=False, open_brace='', close_brace='', indent='', color=False).strip()
    right = render_groundings(self, chart, **kwargs)
    #display(HTML('<strong>Change in chart</strong>')); chart.compare(new_chart)
    return f"""<table>
    <tr style="border: thin solid black;">
    <th style="text-align: left; min-width: 200px;">Chart</th>
    <th style="text-align: left;">Rule instantiations</th>
    </tr>
    <tr>
    <td style="text-align: left; vertical-align: top;"><pre>{left}</pre></td>
    <td style="text-align: left; vertical-align: top;">{right}</td>
    </tr>
    </table>
    <table style="width: 100%; border: thin solid black;"><tr><th style="text-align: center;">
      done {Ansi2HTMLConverter().convert(colors.mark(chart == new_chart))}
    </th></tr></table>
    <table>
    <tr>
    <th style="text-align: left; min-width: 200px; border: thin solid black;">Computation graph</th>
    </tr>
    <tr>
    <td>
    {self.instantiate(chart).coarse_hypergraph()._repr_html_()}
    </td>
    </tr>
    """


def display_chart_and_groundings(self, chart, new_chart, **kwargs):
    return display(HTML(render_chart_and_groundings(self, chart, new_chart, **kwargs)))


def open_html(html):   # pragma: no cover
    "useful in notebook when the object is too big to see; so we open it a separate tab."
    if hasattr(html, '_repr_svg_'): html = html._repr_svg_()
    if hasattr(html, '_repr_html_'): html = html._repr_html_()
    if isinstance(html, HTML): html = html.data
    if isinstance(html, SVG): html = html.data
    filename = f'/tmp/{hashit(html)}.html'
    with open(filename, 'w', encoding='utf-8') as f:
        f.write(html)
    webbrowser.open(filename)


def hashit(x):
    "Content-based hashing"
    return hashlib.sha1(x.encode('utf-8')).hexdigest()


class latex:
    def __init__(self, code, force=False):
        self.code = code
        self.name = hashit(self.code)
        self.force = force

        self.f_svg = Path(f'/tmp/{self.name}.svg')
        self.f_tex = Path(f'/tmp/{self.name}.tex')
        self.f_pdf = Path(f'/tmp/{self.name}.pdf')
        self.f_png = Path(f'/tmp/{self.name}.png')

    @staticmethod
    def escape(x):
        x = str(x)
        return (
            remove_ansi(
                re.sub(
                    r'([\\$~])',
                    lambda m: {
                        '\\': r'$\backslash$',
                        '~': '$\sim$',
                        '$': '\$',
                       }[m.group(1)],
                    x
                ),
                lambda m: '{\color{magenta}%s}' % m.group(1)
            )
            .replace('∂', r'$\partial$')
            .replace('⋅', r'${\cdot}$')
            .replace('ε', r'$\varepsilon$')
            .replace('|', r'$\mid$')
            .replace('_', r'\_')
        )

    def _repr_svg_(self):
        return self.to_svg()

    def open(self):   # pragma: no cover
        self.to_svg()
        webbrowser.open(self.f_svg)

    def to_svg(self):
        assert isinstance(self.code, str)

        if self.force or not self.f_svg.exists():

            with open(self.f_tex, 'w', encoding='utf-8') as f:
                f.write(self.code)

            try:
                run_cmd([
                    'pdflatex', '-interaction=nonstopmode',
                    '-output-directory=/tmp',
                    self.f_tex,
                ])

            except AssertionError as e:                  # pragma: no cover
                print(colors.light.red % 'ERROR:', e)
                print('OFFENDING TIKZ CODE:', self.code)
                raise e

            if 1:
                # Inkscape
                run_cmd([
                    'inkscape', '--without-gui',
                    self.f_pdf,
                    f'--export-plain-svg={self.f_svg}',
                ])

            else:
                # pdf2svg
                run_cmd(['pdf2svg', self.f_pdf, self.f_svg])

        return open(self.f_svg, encoding='utf-8').read()

    def to_png(self, *args, **kwargs):
        # Inkscape: pdf -> png
        self.to_svg(*args, **kwargs)
        run_cmd([
            'inkscape', '--without-gui', self.f_pdf,
            f'--export-png={self.f_png}',
        ])
        return Image(self.f_png)


class tikz(latex):

    header = r"""
    \documentclass[tikz]{standalone}
    \usepackage{tikz}
    \usepackage{tikz-qtree}
    \usetikzlibrary{automata,positioning}
    %s
    %s
    \begin{document}
    \begin{tikzpicture}[%s]
    %s
    \end{tikzpicture}
    \end{document}
    """

    def __init__(self, code, libs=(), opts='', preamble='', **kwargs):
        super().__init__(self.header % ('\n'.join(
            r'\usetikzlibrary{%s}' % x
            for x in libs
        ), preamble, opts, code), **kwargs)


def run_cmd(cmd):
    assert isinstance(cmd, list)

    if not find_executable(cmd[0]):
        raise Exception(f'The `{cmd[0]}` executable was not found - please make sure it is installed.')

    cmd = [str(x) for x in cmd]
    try:
        assert 0 == subprocess.call(cmd, stderr=subprocess.PIPE, stdout=subprocess.PIPE), \
            f'\n\nFailed to execute command:\n\n    {" ".join(cmd)}\n'
    except AssertionError as e:                # pragma: no cover
        print(colors.light.red % 'ERROR:', e)
        raise e


class graphviz:

    def __init__(self, code, force=False):
        self.code = code
        self.force = force
        self.base = Path(f'/tmp/{hashit(code)}')
        self.f_dot = self.base + '.dot'
        self.f_svg = self.base + '.svg'
        self.f_png = self.base + '.png'

    def to_svg(self):
        if not self.f_svg.exists() or self.force:
            with open(self.f_dot, 'w', encoding='utf-8') as f:
                f.write(self.code)
            cmd = f'dot -Tsvg {self.f_dot} -o {self.f_svg}'
            try:
                run_cmd(cmd.split())
            except AssertionError:       # pragma: no cover
                print(self.code)
                raise
        return open(self.f_svg, encoding='utf-8').read()

    def to_png(self):
        if not self.f_png.exists() or self.force:
            with open(self.f_dot, 'w', encoding='utf-8') as f:
                f.write(self.code)
            cmd = f'dot -Tpng {self.f_dot} -o {self.f_png}'
            try:
                run_cmd(cmd.split())
            except AssertionError:      # pragma: no cover
                print(self.code)
                raise
        return Image(self.f_png)

    def _repr_html_(self):
        return self.to_svg()

    def open(self):    # pragma: no cover
        self.to_svg()
        webbrowser.open(self.f_svg)


dot2svg = lambda *args, **kwargs: graphviz(*args, **kwargs).to_svg()


def escape_str(x):
    return str(x).replace('"', r'\"')


def escape_html(x):
    return x.replace('&', '&amp;').replace('<', '&lt;').replace('>', '&gt;')


def remove_ansi(x, callback='\1'):
    return re.sub(r'\033\[.*?m(.*?)\033\[0m', callback, x)


@contextmanager
def setunset(obj, attr, val):
    was = getattr(obj, attr)
    setattr(obj, attr, val)
    yield
    setattr(obj, attr, was)


#_______________________________________________________________________________
# TODO: I don't like this solution, but the alterative is inefficient because it
# is constantly doing hash+eq on programs.

from frozendict import frozendict
from functools import wraps

class InstanceCache:
    def __init__(self):
        self._caches = {}

    def get_cache(self, func):
        if func not in self._caches: self._caches[func] = {}
        return self._caches[func]

def instance_cache(func):

    @wraps(func)
    def wrapper(self, *args, **kwargs):
        cache = self._caches.get_cache(func)
        key = (args, frozendict(kwargs.items()))
        if key in cache: return cache[key]
        result = func(self, *args, **kwargs)
        cache[key] = result
        return result

    return wrapper
