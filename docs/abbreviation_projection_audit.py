#!/usr/bin/env python
"""
Research prototype for auditing abbreviation projections.

This script intentionally does not participate in abbreviation code generation.
It reports where the current implementation drops `$free` variables from typed
branches and classifies those drops as conservative candidates that still need a
rule-instance flow proof.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass, field
from typing import Iterable

from dyna import Program, Term, term_vars
from dyna.analyze.abbreviate import freebies


@dataclass(frozen=True)
class DropCandidate:
    variable: str
    status: str
    reason: str


@dataclass
class BranchAudit:
    index: int
    head: str
    retained: list[str]
    dropped: list[str]
    candidates: list[DropCandidate] = field(default_factory=list)


def _ordinary_constraints(rule) -> list[Term]:
    return [
        b
        for b in rule.body
        if isinstance(b, Term) and b.fn not in {"$free", "$bound"}
    ]


def _sorted_vars(xs: Iterable[object]) -> list[str]:
    return sorted({str(x) for x in xs})


def audit_program(program: Program) -> list[BranchAudit]:
    types = program.type_analysis()
    types.chart = types.chart.sort()

    audits: list[BranchAudit] = []
    for index, branch in enumerate(types.chart):
        free_vars = freebies(branch)
        retained = set(term_vars(branch)) - free_vars
        ordinary = _ordinary_constraints(branch)

        candidates: list[DropCandidate] = []
        for var in sorted(free_vars, key=str):
            if any(var in term_vars(constraint) for constraint in ordinary):
                candidates.append(
                    DropCandidate(
                        variable=str(var),
                        status="retain",
                        reason="ordinary constraint mentions variable",
                    )
                )
            else:
                candidates.append(
                    DropCandidate(
                        variable=str(var),
                        status="candidate-pass-through",
                        reason="branch-local constraints do not reject; flow proof required",
                    )
                )

        audits.append(
            BranchAudit(
                index=index,
                head=str(branch.head),
                retained=_sorted_vars(retained),
                dropped=_sorted_vars(free_vars),
                candidates=candidates,
            )
        )

    return audits


def case_infinite() -> Program:
    return Program(
        """
        goal += f(X).
        f(1) += 2.
        f(X) += 3.
        g(X) += 4 * f(X).
        outputs: goal.
        """
    )


def case_list_beta() -> Program:
    return Program(
        """
        beta([X,Y|Xs]) += edge(X,Y) * beta([Y|Xs]).
        beta([X]) += stop(X).
        goal += start(X) * beta([X|Xs]).
        outputs: goal.
        inputs: start(_); edge(_,_); stop(_).
        """
    )


def case_cky() -> Program:
    return Program(
        """
        p(X, I, K) += rewrite(X, Y, Z) * p(Y, I, J) * p(Z, J, K).
        p(X, I, K) += rewrite(X, Y) * p(Y, I, K).
        p(X, I, K) += rewrite(X, Y) * word(Y, I, K).
        goal += length(N) * p("ROOT", 0, N).
        inputs: rewrite(X,Y,Z); rewrite(X,Y); word(W,I,K); length(N).
        outputs: goal.
        """
    )


def case_unary_slash() -> Program:
    return case_cky().slash("p(X',I',K')", {1: 1}).prune()


def case_left_child_slash() -> Program:
    return case_cky().slash("p(X',I',K')", {0: 1}).prune()


CASES = {
    "infinite": case_infinite,
    "list-beta": case_list_beta,
    "unary-slash": case_unary_slash,
    "left-child-slash": case_left_child_slash,
}


def print_audit(name: str, audits: list[BranchAudit]) -> None:
    print(f"## {name}")
    for audit in audits:
        if not audit.dropped and not any(
            token in audit.head for token in ("beta", "/", "f(", "g(")
        ):
            continue

        print(f"branch {audit.index}: {audit.head}")
        print(f"  retained: {audit.retained}")
        print(f"  current dropped/free: {audit.dropped}")
        for candidate in audit.candidates:
            print(
                "  "
                f"{candidate.variable}: {candidate.status} "
                f"({candidate.reason})"
            )
    print()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "cases",
        nargs="*",
        help=f"cases to run; choices: {', '.join(sorted(CASES))}",
    )
    args = parser.parse_args()

    names = args.cases or sorted(CASES)
    unknown = sorted(set(names) - set(CASES))
    if unknown:
        parser.error(f"unknown cases: {', '.join(unknown)}")

    for name in names:
        print_audit(name, audit_program(CASES[name]()))


if __name__ == "__main__":
    main()
