#!/usr/bin/env bash
function red    { echo -e "\e[31m$@\e[0m"; }
function yellow { echo -e "\e[33m$@\e[0m"; }
function green  { echo -e "\e[32m$@\e[0m"; }
function blue   { echo -e "\e[34m$@\e[0m"; }
function purple { echo -e "\e[35m$@\e[0m"; }
function cyan   { echo -e "\e[36m$@\e[0m"; }

function bright_red    { echo -e "\e[31;1m$@\e[0m"; }
function bright_yellow { echo -e "\e[33;1m$@\e[0m"; }
function bright_green  { echo -e "\e[32;1m$@\e[0m"; }
function bright_blue   { echo -e "\e[34;1m$@\e[0m"; }
function bright_purple { echo -e "\e[35;1m$@\e[0m"; }
function bright_cyan   { echo -e "\e[36;1m$@\e[0m"; }


function run {
    echo
    green "****************************************************************************"
    green "$@"
    python $@
}

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
