COVERAGE="$@"

if [ -z "$COVERAGE" ]; then
    COVERAGE_OPTS=""
    echo "running without coverage"
else
    COVERAGE_OPTS="\
      --cov-config=.coveragerc \
      --cov dyna/
     "
   echo "running with coverage"
fi

# Note: test_fold_unfold and test_rule_elimination require non-global gensyms so
# we run them before anything that might set that variable -- this is pretty
# gross.  We should just set the global gensym flag appropriately in these test
# modules.
#
FILES=""
FILES="$FILES `find dyna/ -name '*.py'` "
FILES="$FILES `find test/ -name '*.py'` "


pytest --timeout 20 --color=yes $COVERAGE_OPTS $FILES

if [ -z "$COVERAGE" ]; then
    echo "no coverage"
else
    coverage html --rcfile .coveragerc --include './*' -d .coverage-report
    xdg-open .coverage-report/index.html
fi
