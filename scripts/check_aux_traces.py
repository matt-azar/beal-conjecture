"""Compute the necessary Frey trace sets from both integral twists at auxiliary primes."""

import argparse
from dataclasses import dataclass
from math import gcd, isqrt


@dataclass(frozen=True)
class Family:
    d: int
    p: int
    eta_trace: int
    eta_coefficient: int
    branches: tuple


FAMILIES = {
    167: Family(167, 11, 3, 7, ((1, 4), (23, 7))),
    2471: Family(2471, 31, 90621, 391, ((5, 23), (67, 8))),
}

# Signed representatives of the residue classes in docs/auxiliary-traces.md.
EXPECTED_2471 = {
    3: ((-4, 0), (-4, 0)),
    5: ((-2, 2), (-2, 2)),
    11: ((-12, -4, 0, 4), (-12, -4, 0, 4)),
    13: ((-6, -2, 2), (-6, -2, 2)),
    17: ((-2, 0, 4, 8), (-8, -6, 2, 4, 6)),
    61: ((-6,), (8,)),
    683: ((-2,), (-2,)),
    1117: ((-2, 5), (-2, 5)),
    1303: ((-8, 9), (-8, 9)),
    1489: ((-8,), (-8,)),
    1861: ((-5,), (-5,)),
    2357: ((-13,), (-13,)),
    2543: ((1, 6), (1, 6)),
    2729: ((-6, 11), (-6, 11)),
    3163: ((4,), (4,)),
}


EXPECTED_167 = {
    3: ((-4, 0), (-4, 0)),
    5: ((0, 4), (-4, 2)),
    7: ((-4, -3, 0), (-4, -3, 0)),
    13: ((-4, -2, 2, 4), (-5, -4, 0, 4)),
    23: ((0, 2), (0, 2)),
    43: ((-4, 2), (3, 5)),
    89: ((-3,), (-3,)),
    199: ((5,), (5,)),
    353: ((3,), (3,)),
    397: ((-5,), (-5,)),
}


def multiply(left, right, d, q):
    """Multiply coefficient pairs for the basis 1,s with s² = -d."""
    u, v = left
    r, t = right
    return ((u*r - d*v*t) % q, (u*t + v*r) % q)


def field_power(base, exponent, d, q):
    result = (1, 0)
    while exponent:
        if exponent % 2:
            result = multiply(result, base, d, q)
        base = multiply(base, base, d, q)
        exponent //= 2
    return result


def admissible_b(family, q, x, k):
    """One representative per sign pair, including zero when admissible."""
    reps = range((q + 1) // 2)
    a = pow(family.d, (x - 1) // 2, q)
    half = pow(2, -1, q)
    eta = (family.eta_trace * half % q, family.eta_coefficient * half % q)
    root = next((r for r in range(q) if (r*r + family.d) % q == 0), None)
    if root is not None:
        powers = {pow(y, family.p, q) for y in range(q)}
        factors = [(r, pow(eta[0] + eta[1]*r, k, q)) for r in (root, -root)]
        return [b for b in reps
                if all(factor * (b*b + a*r) % q in powers for r, factor in factors)]

    order = q*q - 1
    if gcd(family.p, order) == 1:
        return list(reps)
    eta_k = field_power(eta, k, family.d, q)
    accepted = []
    for b in reps:
        value = multiply(eta_k, (b*b, a), family.d, q)
        if value == (0, 0) or field_power(value, order // family.p, family.d, q) == (1, 0):
            accepted.append(b)
    return accepted


def trace_set(family, q, x, reps):
    """Count points at good b and use the lowered trace at multiplicative b."""
    fiber_sizes = [0] * q
    for y in range(q):
        fiber_sizes[y*y % q] += 1
    constant = pow(family.d, x, q)
    traces = set()
    p = family.p
    for b in reps:
        a2 = 2*b*b % q
        a4 = (b**4 + constant) % q
        if a4:
            affine_count = sum(fiber_sizes[t*((t + a2)*t + a4) % q] for t in range(q))
            trace = q - affine_count
        else:
            trace = (fiber_sizes[2] - 1) * (q + 1)
        traces.add((trace + p//2) % p - p//2)
    return tuple(sorted(traces))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("primes", nargs="*", type=int, help="default: all primes in the table")
    parser.add_argument("--show-b", action="store_true", help="also print normalized b up to sign")
    parser.add_argument("--base", type=int, choices=tuple(FAMILIES), default=2471)
    args = parser.parse_args()
    family = FAMILIES[args.base]
    expected = EXPECTED_167 if args.base == 167 else EXPECTED_2471
    for q in args.primes or expected:
        if q < 3 or gcd(q, 2*family.d*family.p) != 1 or any(q % n == 0 for n in range(2, isqrt(q) + 1)):
            parser.error(f"{q} must be prime and coprime to 2·{family.d}·{family.p}")
        row = []
        for x, k in family.branches:
            reps = admissible_b(family, q, x, k)
            traces = trace_set(family, q, x, reps)
            row.append(traces)
            detail = f", b up to sign={reps}" if args.show_b else ""
            print(f"q={q}, x={x}, k={k}: traces={traces}{detail}")
        if q in expected and tuple(row) != expected[q]:
            raise ValueError(f"Unexpected trace sets at {q}: {row}")


if __name__ == "__main__":
    main()
