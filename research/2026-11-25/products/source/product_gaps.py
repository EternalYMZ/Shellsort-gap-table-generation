"""Generate all gaps a**i * b**j < n in descending order."""
import argparse


def product_gaps(n, a, b):
    if n < 2 or min(a, b) < 2:
        raise ValueError("n and both bases must be at least two")
    gaps = set()
    # Enumerate powers with integers so boundary products are exact.
    first = 1
    while first < n:
        gap = first
        while gap < n:
            gaps.add(gap)  # Bases may share powers.
            gap *= b
        first *= a
    return sorted(gaps, reverse=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    for arg in ("n", "a", "b"):
        parser.add_argument(arg, type=int)
    args = parser.parse_args()
    print(*product_gaps(args.n, args.a, args.b))
