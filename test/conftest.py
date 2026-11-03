"""
Tests marked `@pytest.mark.timelimit` are SKIPPED whenever coverage is on
(`--cov`), which includes every CI run.

Why: these tests rely on `arsenal.robust.timelimit`, which interrupts the
running code with a SIGALRM-raised `Timeout` (e.g., to stop a solver on a
program that never terminates). Under coverage, coverage's C tracer takes a
non-reentrant lock (`Collector.lock_data`) around every traced call. If the
`Timeout` lands just after that lock is acquired, the lock is never released
and the next traced call blocks forever. pytest-timeout cannot rescue it,
because `timelimit` suspends pytest-timeout's own timer while the block runs,
so CI just hangs until the 15-minute job limit.

Measured: with coverage, a loop over the budget tests deadlocked within 3
rounds in 3 of 3 runs, and 2 of 6 full-suite runs hung. Without coverage there
were 0 hangs in 600 rounds. The marked tests still run in local runs without
`--cov`.

Effect: CI does not exercise solver budgets (`budget=`), `ProgramCollection.race`,
or `scc_solver`'s budget-truncated pass.
"""
import pytest


def pytest_collection_modifyitems(config, items):
    coverage_on = bool(config.getoption('cov_source', default=None)) \
        and not config.getoption('no_cov', default=False)
    if not coverage_on:
        return
    skip = pytest.mark.skip(
        reason='timelimit (SIGALRM) can deadlock coverage\'s tracer lock under --cov; see test/conftest.py'
    )
    for item in items:
        if 'timelimit' in item.keywords:
            item.add_marker(skip)
