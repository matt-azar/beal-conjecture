"""Replay the class numbers, ideal generators and local obstructions in docs/descent.md."""

import argparse
from dataclasses import dataclass
from math import gcd, isqrt


@dataclass(frozen=True)
class Case:
    d: int
    p: int
    class_number: int
    trace: int
    coefficient: int
    # Each row gives a modulus, one root of -d and the expected cumulative survivors.
    checks: tuple


CASES = (
    Case(167, 11, 11, 3, 7, (
        (121, 14, {0, 1, 4, 6}),
        (199, 80, set()),
    )),
    Case(2471, 31, 62, 90621, 391, (
        (961, 90, {1, 2, 6, 7, 8, 9, 12, 16, 19, 20, 22, 23, 29}),
        (683, 332, {19, 23}),
        (1117, 552, {19}),
        (2791, 1030, set()),
    )),
)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def reduced_forms(discriminant):
    """Enumerate primitive reduced positive definite forms with boundary signs."""
    for a in range(1, isqrt(-discriminant // 3) + 1):
        for b in range(-a, a + 1):
            c, remainder = divmod(b * b - discriminant, 4 * a)
            if remainder or a > c or gcd(a, b, c) != 1:
                continue
            if b < 0 and (abs(b) == a or a == c):
                continue
            yield a, b, c


def local_twists(case, m, root, imaginary_coefficient):
    """Test both reductions using one b; every residue, including zero, is allowed."""
    require(m % 2 and gcd(m, case.d) == 1, f"Invalid modulus {m}")
    require((root**2 + case.d) % m == 0, f"Invalid root modulo {m}")
    inv_two = pow(2, -1, m)
    eta_plus = (case.trace + case.coefficient * root) * inv_two % m
    eta_minus = (case.trace - case.coefficient * root) * inv_two % m
    powers = {pow(t, case.p, m) for t in range(m)}
    squares = {b*b % m for b in range(m)}
    shift = imaginary_coefficient * root % m
    pairs = [((b2 + shift) % m, (b2 - shift) % m) for b2 in squares]
    classes = set()
    for k in range(case.p):
        left = pow(eta_plus, k, m)
        right = pow(eta_minus, k, m)
        if any(left*u % m in powers and right*v % m in powers for u, v in pairs):
            classes.add(k)
    return classes


def verify(case):
    d, p = case.d, case.p
    require(d % 16 == 7 and all(d % (i*i) for i in range(2, isqrt(d) + 1)),
            "Expected a squarefree radicand congruent to 7 modulo 16")
    require(p > 2 and all(p % i for i in range(2, isqrt(p) + 1)), "Expected an odd prime")
    h = sum(1 for _ in reduced_forms(-d))
    require(h == case.class_number and h % p == 0 and h % (p*p) != 0,
            "Expected a class group with exactly p elements of p-power order")
    require(case.trace % 2 == case.coefficient % 2 == 1, "Expected two odd coefficients")
    require(case.trace**2 + d * case.coefficient**2 == 4 * 2**p, "Incorrect norm of eta")
    # An element of norm two would give a^2 + d*b^2 = 8.
    require(d > 8 and isqrt(8)**2 != 8, "Norm-two exclusion does not apply")
    print(f"d={d}, p={p}, h={h}, norm(eta)={2**p}")
    surviving = set(range(p))
    for m, root, expected in case.checks:
        local = local_twists(case, m, root, d)
        surviving &= local
        require(surviving == expected, f"Unexpected survivors modulo {m}")
        print(f"  m={m}, root={root}, local={sorted(local)}, intersection={sorted(surviving)}")
    require(not surviving, "A twist survived all moduli")


def scan_exponents(case):
    """A finite search over exponent classes; the proof of periodicity is in the notes."""
    if case.d == 167:
        moduli = (89, 121, 199, 353, 397)
        expected = {1: {4}, 23: {7}}
    else:
        # These nine moduli also suffice when the principal class must be retained.
        moduli = (683, 961, 1117, 1303, 1489, 2357, 2543, 2791, 3163)
        expected = {5: {23}, 31: {0}, 67: {8}, 93: {0}}

    modulus_roots = []
    for m in moduli:
        root = next(s for s in range(m) if (s*s + case.d) % m == 0)
        modulus_roots.append((m, root))

    survivors = {}
    for x in range(1, 4*case.p, 2):
        if case.d == 167:
            # Necessary condition for the original equation at the inert prime 23.
            fourths = {pow(b, 4, 23) for b in range(23)}
            powers = {pow(c, case.p, 23) for c in range(23)}
            if not any((pow(case.d, x, 23) + f) % 23 in powers for f in fourths):
                continue
        # At 2471 the varying-base proof requires a sweep including the principal class.
        remaining = set(range(1 if case.d == 167 else 0, case.p))
        for m, root in modulus_roots:
            coefficient = pow(case.d, (x - 1)//2, m)
            remaining &= local_twists(case, m, root, coefficient)
            if not remaining:
                break
        if remaining:
            survivors[x] = remaining
    require(survivors == expected, f"Unexpected odd-exponent survivors: {survivors}")
    label = "nonprincipal twists" if case.d == 167 else "all twists"
    print(f"d={case.d}, x modulo {4*case.p}, {label}: {survivors}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--exponents", action="store_true", help="also replay the odd-exponent sieve")
    args = parser.parse_args()
    for case in CASES:
        verify(case)
        if args.exponents:
            scan_exponents(case)
