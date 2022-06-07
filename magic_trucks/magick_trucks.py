#!/usr/bin/env python3

import argparse
import sys
from pathlib import Path

import z3


def main(argv=None) -> None:
    args = _parse_argv(argv)

    solver = z3.Optimize()

    truck_fn = z3.Function("T", z3.IntSort(), z3.IntSort(), z3.IntSort())
    p_num = z3.Int("p_num")
    goods_chr = ("n", "p", "s", "c", "d")
    weights = (800, 1100, 1000, 2500, 200)
    pallets = (4, p_num, 8, 10, 20)
    trucks = (1, 2, 3, 4, 5, 6, 7, 8)
    capacities = (8000, 8000, 8000, 8000, 8000, 8000, 8000, 8000)

    goods = {char: value for value, char in enumerate(goods_chr, start=1)}

    # Transport all pallets
    for c, n_pallets in zip(goods_chr, pallets):
        solver.add(n_pallets == z3.Sum([truck_fn(truck, goods[c]) for truck in trucks]))

    # Capacity limit
    for truck, capacity in zip(trucks, capacities):
        goods_weights = [
            w * truck_fn(truck, goods[c]) for w, c in zip(weights, goods_chr)
        ]
        solver.add(capacity >= z3.Sum(goods_weights))

    # Number of pallets is greater than or equal to 0
    # Number of pallets in a truck is at most 8
    for truck in trucks:
        solver.add(z3.Sum([truck_fn(truck, goods[good_c]) for good_c in goods]) <= 8)
        for good_c in goods_chr:
            solver.add(0 <= truck_fn(truck, goods[good_c]))

    # Skipples need to be cooled (trucks 1, 2 and 3)
    skipples = goods["s"]
    for truck in [4, 5, 6, 7, 8]:
        solver.add(0 == truck_fn(truck, skipples))

    # Nuzzles are very valuable not two on the same truck
    nuzzles = goods["n"]
    for truck in trucks:
        solver.add(1 >= truck_fn(truck, nuzzles))

    # If question 2 prittles and crottles are explosive
    if args.question == 2:
        print("Adding question 2 constraints")
        prittles = goods["p"]
        crottles = goods["c"]
        for truck in trucks:
            solver.add(
                z3.Implies(
                    truck_fn(truck, prittles) > 0,
                    truck_fn(truck, crottles) == 0,
                )
            )
            solver.add(
                z3.Implies(
                    truck_fn(truck, crottles) > 0,
                    truck_fn(truck, prittles) == 0,
                )
            )

    # Optimize number of prittles pallets
    obj = solver.maximize(p_num)

    solver.check()
    if solver.lower(obj).as_long() != solver.upper(obj).as_long():
        print("[WARNING] Could not find optimal solution")

    print("Number of prittles pallets:", solver.lower(obj))
    # print(solver.model())
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
        choices=[1, 2],
        default=1,
        help="Question number 1) Base case. 2) Prittles and crottles explode when together.",
    )

    return parser.parse_args(argv)


if __name__ == "__main__":
    main()
