from setuptools import setup, find_packages

setup(name='dyna',
      version='0.9',
      description='',
      author='Tim Vieira',
      install_requires=[
          #'arsenal>=3',       # http://github.com/timvieira/arsenal
          #'git+https://github.com/timvieira/arsenal',
          'arsenal @ git+https://github.com/timvieira/arsenal',
          'semirings>=0.3',   # http://github.com/timvieira/semirings
          'orderedset',
          'frozendict',
          'lark-parser',
          'ansi2html',
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
