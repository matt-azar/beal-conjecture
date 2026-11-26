"""Construct the two binary forms for the remaining d=2471, p=31 branches."""

import argparse
from math import comb, gcd


D = 2471
P = 31
# A pair (a,b) denotes a + b*w, with w^2 = w - 618.
ETA = (45115, 391)
FIRST = (7, 3)
SECOND = (-83, 1)


def multiply(z, w):
    a, b = z
    c, e = w
    return a*c - 618*b*e, a*e + b*c + b*e


def power(z, n):
    result = (1, 0)
    while n:
        if n % 2:
            result = multiply(result, z)
        z = multiply(z, z)
        n //= 2
    return result


def conjugate(z):
    a, b = z
    return a + b, -b


def norm(z):
    a, b = z
    return a*a + a*b + 618*b*b


def require(condition, message):
    if not condition:
        raise ValueError(message)


def form_coefficients():
    """Return coefficients of H,F in descending powers of u."""
    scale = power(conjugate(ETA), 8)
    divisor = norm(ETA)**8
    h, f = [], []
    for j in range(P + 1):
        term = multiply(power(FIRST, P-j), power(SECOND, j))
        a, b = multiply(term, scale)
        weight = comb(P, j)
        require(a % divisor == b % divisor == 0, f"Nonintegral term at j={j}")
        h.append(weight * (a // divisor))
        f.append(weight * (b // divisor))
    return h, f


def evaluate(coefficients, u, v):
    return sum(c * u**(P-j) * v**j for j, c in enumerate(coefficients))



def lift_root(f, q, root, derivative, exponent):
    """Hensel lift the simple root of F(T,1) to modulus q^exponent."""
    m = q
    inverse = pow(derivative, -1, q)
    for _ in range(1, exponent):
        value = 0
        for coefficient in f:
            value = (value*root + coefficient) % (m*q)
        require(value % m == 0, "Hensel input is not a root")
        root += (-value // m * inverse % q) * m
        m *= q
    require(evaluate(f, root, 1) % m == 0, "Hensel lift failed")
    return root, m


def combine_congruences(first, second):
    a, m = first
    b, n = second
    return a + m*((b-a)*pow(m, -1, n) % n), m*n


def inner(v, w):
    """The symmetric bilinear form with inner(v,v)=2*C(v)."""
    a, b = v
    c, d = w
    return 44*a*c + 9*(a*d + b*c) + 58*b*d


def minimum_norm(f, exponent):
    roots = combine_congruences(lift_root(f, 7, 0, 3, exponent),
                                lift_root(f, 353, 119, 276, exponent))
    root, modulus = combine_congruences(roots, (163, 683))
    v, w = (modulus, 0), (root, 1)
    while True:
        if inner(w, w) < inner(v, v):
            v, w = w, v
        numerator, denominator = inner(v, w), inner(v, v)
        if 2*abs(numerator) <= denominator:
            break
        multiple = (2*numerator + denominator) // (2*denominator)
        w = (w[0] - multiple*v[0], w[1] - multiple*v[1])
    require(abs(v[0]*w[1] - v[1]*w[0]) == modulus, "Wrong reduction determinant")
    require(all((a-root*b) % modulus == 0 for a, b in (v, w)), "Wrong lattice")
    require(inner(v, v) <= inner(w, w) and 2*abs(inner(v, w)) <= inner(v, v),
            "Basis is not Gauss reduced")
    return inner(v, v) // 2


def check_local_coordinates(f):
    derivative = [(P-j)*a for j, a in enumerate(f[:-1])]
    for q, expected, unit_root, expected_derivative in (
        (7, {0, 6}, 0, 3), (353, {72, 119}, 119, 276)
    ):
        require(f[0] % q != 0, f"Unexpected root at infinity modulo {q}")
        roots = {z for z in range(q) if evaluate(f, z, 1) % q == 0}
        good = {z for z in roots if (22*z*z + 9*z + 29) % q != 0}
        require(roots == expected and good == {unit_root}, f"Unexpected roots modulo {q}")
        slope = sum(c * unit_root**(P-1-j) for j, c in enumerate(derivative)) % q
        require(slope == expected_derivative, f"Incorrect derivative modulo {q}")
        print(f"q={q}: root with unit norm={unit_root}, derivative={slope}")

    q, root = 683, 332
    powers = {pow(i, P, q) for i in range(q)}
    require((root*root+D) % q == 0, "Incorrect split root modulo 683")
    r = (1+root)*pow(2,-1,q) % q
    slope = (83-r)*pow(7+3*r,-1,q) % q
    require(slope == 163, "Incorrect projective slope")
    for x, sign, expected_b in [(5, -1, {26, 657}), (67, 1, {298, 385})]:
        shift = pow(D, (x-1)//2, q)
        possible = set(range(q))
        for s_root in (root, -root):
            w = (1+s_root)*pow(2,-1,q) % q
            eta = (ETA[0]+ETA[1]*w) % q
            require(eta != 0, "Expected a local unit")
            factor = pow(eta,8,q)
            possible = {b for b in possible
                        if (b*b + sign*shift*s_root)*factor % q in powers}
        require(possible == expected_b, f"Unexpected b modulo {q} at x={x}")
        require(all((b*b + sign*shift*root) % q == 0 for b in possible),
                "Vanishing at distinguished root required")
        print(f"x={x} mod 124: scaled b mod 683 in {sorted(possible)}, u/v={slope} mod 683")

def check():
    require((83**2 - 83 + 618) % 256 == 0, "Incorrect reduction root")
    require((ETA[0] + ETA[1]*83) % 256 == 0, "Incorrect prime above 2")
    require(norm(ETA) == 2**P, "Incorrect norm")
    require(FIRST[0]*SECOND[1] - FIRST[1]*SECOND[0] == 256, "Incorrect lattice index")
    for a, b in (FIRST, SECOND):
        require((a + 83*b) % 256 == 0, "Basis vector outside the ideal")
    h, f = form_coefficients()
    require(f[0] != 0 and gcd(*f) == 1, "Expected primitive F of degree 31")
    for u, v in [(1, 0), (0, 1), (1, 1), (2, -1), (-3, 2)]:
        require(gcd(u, v) == 1, "Test pair must be primitive")
        beta = (u*FIRST[0] + v*SECOND[0], u*FIRST[1] + v*SECOND[1])
        H, F = evaluate(h, u, v), evaluate(f, u, v)
        require(multiply((H, F), power(ETA, 8)) == power(beta, P),
                f"Failed to recover beta^31 at {(u, v)}")
        C = 22*u*u + 9*u*v + 29*v*v
        require(norm(beta) == 256*C and norm((H, F)) == C**P,
                f"Failed norm identity at {(u, v)}")
        print(f"(u,v)=({u},{v}): C={C}, H={H}, F={F}")
    check_local_coordinates(f)
    for t, expected in (
        (2, 61556730755),
        (33, 30037741118939165043541773515025179607825654269254898589906307931058569334645705859214658956080886769986664957667560),
    ):
        bound = minimum_norm(f, t)
        require(bound == expected, f"Incorrect shortest-vector norm at t={t}")
        print(f"t >= {t} on its branch: c >= {bound}")
    return h, f


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--coefficients", action="store_true",
                        help="print both coefficient lists, from u^31 to v^31")
    args = parser.parse_args()
    H, F = check()
    if args.coefficients:
        print("H =", H)
        print("F =", F)
