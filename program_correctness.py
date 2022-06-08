#!/usr/bin/env python3

import argparse
import sys
from pathlib import Path

import z3


def main(argv=None) -> None:
    _ = _parse_argv(argv)

    n_steps = 10

    for n in range(1, 11):
        solver = z3.Solver()
        _add_program_formula(solver, n, n_steps=n_steps)
        result = solver.check()

        # If sat we know that the crash state is reachable
        # otherwise we cannot possible reach that state.
        if result == z3.sat:
            print(f"Value {n} might crash!")
        else:
            print(f"Value {n} is safe!")


def _add_program_formula(
    solver: z3.Solver,
    crash_n: int,
    n_steps: int = 10,
):
    a_fn = z3.Function("a", z3.IntSort(), z3.IntSort())
    b_fn = z3.Function("b", z3.IntSort(), z3.IntSort())

    # Initialization
    solver.add(a_fn(0) == 1, b_fn(0) == 1)

    for i in range(1, n_steps + 1):
        solver.add(
            z3.Or(
                z3.And(
                    a_fn(i) == a_fn(i - 1) + 2 * b_fn(i - 1),
                    b_fn(i) == b_fn(i - 1) + i,
                ),
                z3.And(
                    b_fn(i) == a_fn(i - 1) + b_fn(i - 1),
                    a_fn(i) == a_fn(i - 1) + i,
                ),
            ),
        )

    # We want to know if we might reach the crash state
    solver.add(b_fn(n_steps) == 600 + crash_n)


def _parse_argv(argv) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        prog=Path(__file__).stem,
        formatter_class=argparse.ArgumentDefaultsHelpFormatter,
    )

    return parser.parse_args(argv)


if __name__ == "__main__":
    main()
