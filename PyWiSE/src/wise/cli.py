import argparse
import sys

import z3
from antlr4.error.Errors import ParseCancellationException

import wise
from wise.bugfinder import find_bugs, BugFound, find_bugs_depth_first, \
    find_bugs_assuming
from wise.helpers import is_unsat, simplify_expr
from wise.parser import parse_imp, parse_bexpr

# Exit Codes
USAGE_ERROR = 2
DATA_FORMAT_ERROR = 65


def main():
    parser = argparse.ArgumentParser(
        prog="wise",
        description="A Python implementation of the verified symbolic executor WiSE "
        + f"(v{wise.__version__})",
        formatter_class=argparse.ArgumentDefaultsHelpFormatter,
    )

    parser.add_argument(
        "-n",
        "--nodes",
        type=int,
        default=50,
        help="the number of symbolic states to explore",
    )

    parser.add_argument(
        "--depth-first",
        type=bool,
        action=argparse.BooleanOptionalAction,
        default=False,
        help="run symbolic execution in depth-first mode (not as in original WiSE)",
    )

    parser.add_argument(
        "--simplify",
        type=bool,
        action=argparse.BooleanOptionalAction,
        default=True,
        help="simplify output path conditions",
    )

    parser.add_argument(
        "--prune-early",
        type=bool,
        action=argparse.BooleanOptionalAction,
        default=True,
        help="check intermediate states for satisfiability and prune unsatisfiable ones",
    )

    parser.add_argument(
        "-a",
        "--assumption",
        required=False,
        help="an optional initial assumption",
    )

    parser.add_argument(
        "file",
        metavar="FILE",
        type=argparse.FileType("r", encoding="UTF-8"),
        help="the IMP file to execute",
    )

    args = parser.parse_args()

    nodes = args.nodes
    depth_first = args.depth_first
    simplify = args.simplify
    assumption = parse_bexpr(args.assumption) if args.assumption is not None else None
    file_name = args.file.name
    file_contents = args.file.read()

    try:
        parsed = parse_imp(file_contents)
    except ParseCancellationException:
        print(f"Error parsing file {file_name}")
        sys.exit(DATA_FORMAT_ERROR)

    print(f"Analyzing file {file_name}\n")

    if depth_first:
        stream = find_bugs_depth_first(parsed, assumption)
    elif assumption is not None:
        stream = find_bugs_assuming(parsed, assumption)
    else:
        stream = find_bugs(parsed)

    bug_found = False
    for _ in range(nodes):
        next_result = next(stream)
        if isinstance(next_result, BugFound):
            bug_found = True
            print("BUG FOUND")
            path, store, _ = next_result.s

            if simplify:
                path = simplify_expr(path)

            print(f"  Path:          {path}")
            print(f"  Example Input: {example_input(path)}")
            print(f"  Store:         {store}")

    if not bug_found:
        print(f"No bug found at depth {nodes}.")


def example_input(path):
    solver = z3.Solver()
    solver.add(path.to_smt())
    assert solver.check() == z3.sat
    model = solver.model()

    return ", ".join(
        map(
            lambda p: f"{p[0]} := {p[1]}",
            sorted(
                {str(decl): model[decl].as_long() for decl in model.decls()}.items()
            ),
        )
    )


if __name__ == "__main__":
    main()
