from setuptools import setup, find_packages

setup(name='dyna',
      version='0.9',
      description='',
      author='Tim Vieira',
      install_requires=[
          'arsenal',     # http://github.com/timvieira/arsenal
          'semirings',   # http://github.com/timvieira/semirings
          'orderedset',
          'frozendict',
          'lark-parser',
          'ansi2html',
          'networkx',
          'z3-solver',
          'sympy',
          'graphviz',
          'rich',
          'IPython',
          'svgling',
          # -------------------------------------------------------------------
          # development
          'coveragepy',
          'pytest',
          'pytest-cov',
          'pytest-timeout',
      ],
      packages = find_packages(),
)
