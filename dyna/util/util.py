import hashlib
import re
import subprocess
import webbrowser
import numpy as np

from ansi2html import Ansi2HTMLConverter
from arsenal import colors
from contextlib import contextmanager
import shutil
from IPython.display import display, SVG, Image, HTML
from path import Path


import ipywidgets as widgets

def interactive_forward_chaining(p):
    import dyna

    chart = dyna.Program(inputs='')
    iterates = [chart]
    while True:
        new_chart = p.step(chart)
        iterates.append(new_chart)
        if chart == new_chart: break
        chart = new_chart

    def my_update_function(current_index):
        dyna.util.display_chart_and_groundings(p, iterates[current_index-1], iterates[current_index])

    return FunctionDisplay(my_update_function, start=1, end=len(iterates)-1)


# visualization utility used in demo
class FunctionDisplay:
    def __init__(self, update_function, start, end):
        """
        Initialize the display with a function and a range of values.

        Parameters:
        - update_function: A function that takes a single argument (the current index)
          and updates the display based on this index.
        - start: The starting value of the index.
        - end: The ending value of the index.
        """
        self.update_function = update_function
        self.current_index = start
        self.start = start
        self.end = end
        self.output = widgets.Output()

        # Initialize UI components
        self.prev_button = widgets.Button(description='Prev')
        self.next_button = widgets.Button(description='Next')
        self.buttons = widgets.HBox([self.prev_button, self.next_button])

        # Setup event handlers
        self.prev_button.on_click(self.on_prev_clicked)
        self.next_button.on_click(self.on_next_clicked)

        # Display the initial UI setup
        display(self.buttons, self.output)
        self.update_display()

    def on_prev_clicked(self, b):
        if self.current_index > self.start:
            self.current_index -= 1
            self.update_display()

    def on_next_clicked(self, b):
        if self.current_index < self.end:
            self.current_index += 1
            self.update_display()

    def update_display(self):
        with self.output:
            self.output.clear_output()
            # Call the update function with the current index.
            self.update_function(self.current_index)


def format_table(rows, headings=None, table_style=''):
    def fmt(x):
        try:
            return x._repr_html_()
        except AttributeError:
            try:
                return x._repr_svg_()
            except AttributeError:
                return str(x)
    return (
        f'<table style="{table_style}">'
         + ('<tr style="font-weight: bold;">' + ''.join(f'<th>{x}</th>' for x in headings) +'</tr>' if headings else '')
         + ''.join('<tr>' + ''.join(f'<td>{fmt(x)}</td>' for x in row) +  ' </tr>' for row in rows)
         + '</table>'
    )


def display_table(*args, **kwargs):
    display(HTML(format_table(*args, **kwargs)))


from collections import Counter
def FrozenBag(elements):
    return frozenset(Counter(elements).items())


def display_groundings(*args, **kwargs):
    return display(HTML(render_groundings(*args, **kwargs)))


def render_groundings(self, chart=None):
    "Show instantiations of program rules against chart."
    return self.show_groundings(chart)._repr_html_()


class GroundingsPrinter:
    """
    A surface-aware pretty-printer for a program's groundings, as returned by
    `Program.show_groundings`: ANSI-colored text in a console (via `__repr__`)
    and an HTML table in a notebook (via `_repr_html_`).

    The grounding data itself lives on `Program` -- `Program.groundings(chart)`
    yields the `Grounding(i, rule, value)` records, and `Program.instantiate`
    collects them into a `Program`.  This class only decides how to display
    them.  `hide/only/filter` return a new printer with some source rules
    collapsed -- dropped from the console view, tucked into a `<details>` block
    in the notebook view.
    """

    def __init__(self, program, chart=None, hidden=()):
        self.program = program
        self.chart = chart
        self.hidden = frozenset(hidden)

    def _groups(self):
        "Group groundings by source rule: yield (i, source_rule, [(value, ground_rule), ...])."
        rows = {}
        for g in self.program.groundings(self.chart):
            v = g.value
            if isinstance(v, tuple) and len(v) >= 1: v = np.prod(v)
            rows.setdefault(g.i, []).append((v, g.rule))
        for i, r in enumerate(self.program.rules):
            yield i, r, rows.get(i, [])

    # -- view modifiers (each returns a new printer) ------------------------

    def _clone(self, hidden):
        return GroundingsPrinter(self.program, self.chart, hidden)

    def hide(self, *idxs):
        "Collapse the given source rules out of the display."
        return self._clone(self.hidden | set(idxs))

    def show(self, *idxs):
        "Un-hide the given source rules."
        return self._clone(self.hidden - set(idxs))

    def only(self, *idxs):
        "Show only the given source rules (collapse the rest)."
        return self._clone(set(range(len(self.program.rules))) - set(idxs))

    def filter(self, keep):
        "Keep source rules where `keep(i, rule)` is true; collapse the rest."
        return self._clone(frozenset(i for i, r in enumerate(self.program.rules)
                                     if not keep(i, r)))

    # -- rendering ----------------------------------------------------------

    def __repr__(self):
        "Show instantiations of program rules against chart."
        lines = []
        for i, r, rows in self._groups():
            lines.append(colors.render(colors.dark.magenta % f'# {i}: {r.__repr__(color=False)}'))
            if i in self.hidden:
                lines.append(colors.dark.white % f'  ({len(rows)} grounding{"" if len(rows) == 1 else "s"} hidden)')
                continue
            for v, gr in rows:
                pre = colors.magenta % f'{v}:'
                lines.append(f'{pre} {gr}')
        return '\n'.join(lines)

    def _repr_html_(self):
        # Outline/tree layout: each source rule is a collapsible <details> node
        # whose summary is the *uninstantiated* rule (label-style `#i:` prefix),
        # with its instantiations nested beneath it -- indented under a left
        # guide line.  The nesting makes the template read as the parent heading,
        # clearly separate from its instances (the template is not itself a fact;
        # confusing it for one would double-count).  Rules use the
        # `color='html'`/`roles` convention (input/output items colored by role).
        # Smooth expand/collapse: animate the <details> content's block-size via
        # the ::details-content pseudo-element.  Works where supported (current
        # Chromium / Jupyter); elsewhere it just opens/closes instantly.
        css = ('<style>'
               '.grnd{interpolate-size:allow-keywords}'
               '.grnd::details-content{block-size:0;overflow:clip;'
               'transition:block-size .2s ease,content-visibility .2s;'
               'transition-behavior:allow-discrete}'
               '.grnd[open]::details-content{block-size:auto}'
               '</style>')
        def html(rule):
            return rule.__repr__(color='html', roles=self.program._io_roles(rule))
        blocks = []
        for i, r, rows in self._groups():
            body = '\n'.join(
                f'<tr><td style="vertical-align: top; padding-right: 1em; color: #888;">{v}</td>'
                f'<td style="text-align: left; vertical-align: top;">{html(gr)}</td></tr>'
                for v, gr in rows)
            open_attr = '' if i in self.hidden else ' open'
            blocks.append(f"""\
<details{open_attr} class="grnd" style="font-family: Courier New,monospace; margin: 1px 0;">
<summary style="cursor: pointer;"># {i}: {html(r)}</summary>
<div style="margin-left: 0.55em; padding-left: 1em; border-left: 1px solid #ccc;"><table>{body}</table></div>
</details>""")
        return css + '\n' + '\n'.join(blocks)


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
    """
#    <table>
#    <tr>
#    <th style="text-align: left; min-width: 200px; border: thin solid black;">Computation graph</th>
#    </tr>
#    <tr>
#    <td>
#    {self.instantiate(chart).coarse_hypergraph()._repr_html_()}
#    </td>
#    </tr>
#    </table>



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
                        '~': r'$\sim$',
                        '$': r'\$',
                       }[m.group(1)],
                    x
                ),
                lambda m: r'{\color{magenta}%s}' % m.group(1)
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

    if not shutil.which(cmd[0]):
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
# TODO: I don't like this solution, but the alternative is inefficient because it
# is constantly doing hash+eq on programs.

from functools import wraps

def instance_cache(func):
    """Memoize a method per instance, keyed by its arguments.

    Contract for the host class: it must define `self._caches = {}` and clear
    it (e.g. `self._caches.clear()`) whenever state the cached methods depend on
    mutates -- the decorator never invalidates on its own.  See `Program`, which
    clears it from `_invalidate_caches` on every rule mutation.

    All decorated methods share the one dict, disambiguated by `func` in the
    key, so a single `clear()` drops every method's cache at once.  Arguments
    must be hashable.  Note the key does not normalize call form, so `f(True)`,
    `f(x=True)`, and `f()` (with `x` defaulting to `True`) cache separately.
    """

    @wraps(func)
    def wrapper(self, *args, **kwargs):
        cache = self._caches
        key = (func, args, tuple(sorted(kwargs.items())))
        if key in cache: return cache[key]
        result = cache[key] = func(self, *args, **kwargs)
        return result

    return wrapper
