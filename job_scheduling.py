#!/usr/bin/env python3

import argparse
import sys
from pathlib import Path

import z3


def main(argv=None) -> None:
    args = _parse_argv(argv)

    solver = z3.Optimize()

    n_jobs = 10
    jobs = list(range(1, n_jobs + 1))
    start_fn = z3.Function("start", z3.IntSort(), z3.IntSort())
    end_fn = z3.Function("end", z3.IntSort(), z3.IntSort())
    z3_total_runtime = z3.Int("total_runtime")

    for i in jobs:
        # Start must be >= 0
        solver.add(start_fn(i) >= 0)
        # Set running time for job i (i + 10) for i = 1, 2, ..., 10
        solver.add(end_fn(i) == (start_fn(i) + i + 10))
        # All jobs must finish before total_runtime
        solver.add(end_fn(i) <= z3_total_runtime)

    # Job 3 may only start if jobs 1 and 2 have been finished
    solver.add(start_fn(3) >= end_fn(1))
    solver.add(start_fn(3) >= end_fn(2))

    # Job 6 may only start if jobs 2 and 4 have been finished
    solver.add(start_fn(6) >= end_fn(2))
    solver.add(start_fn(6) >= end_fn(4))

    # Job 7 may only start if jobs 1, 4 and 5 have been finished
    solver.add(start_fn(7) >= end_fn(1))
    solver.add(start_fn(7) >= end_fn(4))
    solver.add(start_fn(7) >= end_fn(5))

    # Job 8 may only start if jobs 3 and 6 have been finished
    solver.add(start_fn(8) >= end_fn(3))
    solver.add(start_fn(8) >= end_fn(6))

    # Job 9 may only start if jobs 6 and 7 have been finished
    solver.add(start_fn(9) >= end_fn(6))
    solver.add(start_fn(9) >= end_fn(7))

    # Job 10 may only start if jobs 8 and 9 have been finished
    solver.add(start_fn(10) >= end_fn(8))
    solver.add(start_fn(10) >= end_fn(9))

    if args.question > 1:
        # Job 7 should not start earlier than job 8
        solver.add(start_fn(8) <= start_fn(7))

    if args.question > 2:
        # Jobs 3, 4, 5 cannot run at the same time
        q2_jobs = [3, 4, 5]
        for job1 in q2_jobs:
            for job2 in filter(lambda x: x != job1, q2_jobs):
                solver.add(
                    z3.Or(
                        start_fn(job1) >= end_fn(job2),
                        end_fn(job1) <= start_fn(job2),
                    ),
                    z3.Or(
                        start_fn(job1) >= end_fn(job2),
                        end_fn(job1) <= start_fn(job2),
                    ),
                )

    # Objective
    obj = solver.minimize(z3_total_runtime)
    result = solver.check()

    if result == z3.sat:
        total_runtime = solver.lower(obj).as_long()
        print("Total runtime:", total_runtime)
    else:
        print("Unsatisfiable")

    sys.exit(0)


def _parse_argv(argv) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        prog=Path(__file__).stem,
        formatter_class=argparse.ArgumentDefaultsHelpFormatter,
    )

    parser.add_argument(
        "-q",
        "--question",
        type=int,
        choices=[1, 2, 3],
        default=1,
        help=(
            "Question number 1) Base case. 2) Job 7 should start earlier"
            + "than 8. 3) Jobs 3, 4 and 5 cannot run at the same time."
        ),
    )

    return parser.parse_args(argv)


if __name__ == "__main__":
    main()
