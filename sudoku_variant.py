#!/usr/bin/env python3

import collections
import sys
from typing import Mapping, Tuple

import z3

N_ROWS = 9
N_COLS = 9


def main() -> None:
    solver = z3.Solver()

    # Function mapping cells to values
    cell_fn = z3.Function(
        "C",
        z3.IntSort(),
        z3.IntSort(),
        z3.IntSort(),
    )

    _add_formula(solver, cell_fn)

    solver.check()
    # print(solver.model())

    # Get mapping from cell coordinates to value.
    # There might be better ways to do it but I
    # just want something that puts the sudoku on
    # the screen.
    cell_fn_v = solver.model()[cell_fn].as_list()
    cell_fn_map = collections.defaultdict(lambda: cell_fn_v[-1])
    for p1, p2, v in cell_fn_v[:-1]:
        cell_fn_map[(p1.as_long(), p2.as_long())] = v.as_long()

    _show_sudoku(cell_fn_map)

    sys.exit(0)


def _show_sudoku(grid: Mapping[Tuple[int, int], int]) -> None:
    for row in range(N_ROWS):
        for col in range(N_COLS):
            print(grid[(row, col)], end="")
            if (col + 1) % 3 == 0 and (col + 1) < N_ROWS:
                print(" | ", end="")
            elif (col + 1) < N_ROWS:
                print(" ", end="")

        print("")
        if (row + 1) % 3 == 0:
            print("-" * 21)


def _add_formula(
    solver: z3.Solver,
    cell_fn: z3.FuncDeclRef,
) -> None:
    # Sudoku grid is numbered from the top left cell which
    # is assigned coordinate (0, 0). Where the first number
    # represents the row and the second the column. Thereby,
    # the bottom right cell has coordinates (8, 8)

    _add_basic_sudoku_formula(solver, cell_fn)
    _add_variant_sudoku_formula(solver, cell_fn)


def _add_basic_sudoku_formula(
    solver: z3.Solver,
    cell_fn: z3.FuncDeclRef,
) -> None:
    rows = list(range(N_ROWS))
    cols = list(range(N_COLS))

    # All cells value between 1 and 9
    for row in rows:
        for col in cols:
            solver.add(0 < cell_fn(row, col))
            solver.add(10 > cell_fn(row, col))

    # All row/col values distinct
    for row in rows:
        solver.add(z3.Distinct(*[cell_fn(row, col) for col in cols]))

    for col in cols:
        solver.add(z3.Distinct(*[cell_fn(row, col) for row in rows]))

    # All square numbers are different
    for sq_h, sq_v in zip(range(0, 3), range(0, 3)):
        h_start = sq_h * 3
        h_end = h_start + 3
        v_start = sq_v * 3
        v_end = v_start + 3

        solver.add(
            z3.Distinct(
                *[
                    cell_fn(row, col)
                    for row in range(v_start, v_end)
                    for col in range(h_start, h_end)
                ]
            )
        )


def _add_variant_sudoku_formula(
    solver: z3.Solver,
    cell_fn: z3.FuncDeclRef,
) -> None:
    _add_variant_sudoku_formula_lt(solver, cell_fn)
    _add_variant_sudoku_formula_consecutive(solver, cell_fn)


def _add_variant_sudoku_formula_lt(
    solver: z3.Solver,
    cell_fn: z3.FuncDeclRef,
):
    # first cell number is less than second cell
    lt_pairs = [
        ((row, col - 1), (row, col))
        for row, rng in (
            (1, range(4, 9)),
            (3, range(1, 6)),
            (5, range(4, 9)),
            (7, range(1, 6)),
        )
        for col in rng
    ]

    for (first_r, first_c), (second_r, second_c) in lt_pairs:
        solver.add(cell_fn(first_r, first_c) < cell_fn(second_r, second_c))


def _add_variant_sudoku_formula_consecutive(
    solver: z3.Solver,
    cell_fn: z3.FuncDeclRef,
) -> None:
    # Numbers on both cell are consecutive, that is
    # they differ by exactly one.

    # Horizontal left cell
    h_cons_pairs = (
        [(0, 1), (0, 3), (0, 6)]
        + [(2, 1), (2, 3), (2, 4)]
        + [(4, 0), (4, 1), (4, 3), (4, 5), (4, 7)]
        + [(5, 2)]
        + [(6, 2)]
        + [(7, 5)]
    )

    # Vertical top cell
    v_cons_pairs = (
        [(0, 5)]
        + [(1, 6)]
        + [(2, 6), (2, 8)]
        + [(3, 2), (3, 6), (3, 8)]
        + [(5, 2), (5, 3), (5, 5), (5, 6)]
    )

    # Consecutive pairs cells from previous lists
    cons_pairs = [
        (
            (row, col),
            (row, col + 1),
        )
        for row, col in h_cons_pairs
    ]
    cons_pairs += [
        (
            (row, col),
            (row + 1, col),
        )
        for row, col in v_cons_pairs
    ]

    # Cell values are consecutive
    for (first_r, first_c), (second_r, second_c) in cons_pairs:
        f_value = cell_fn(first_r, first_c)
        s_value = cell_fn(second_r, second_c)

        solver.add(
            z3.Or(
                (f_value + 1 == s_value),
                (f_value == s_value + 1),
            ),
        )


if __name__ == "__main__":
    main()
