"""Exact exploratory checks. Run with Python 3.12 and SymPy 1.14.0."""
import argparse
from fractions import Fraction
from itertools import combinations
from math import gcd, prod

import sympy as sp


X, S, T = sp.symbols('X S T')
H = X**2 + X + 3
NUM = sp.Poly((5 * X - 3) * H**5 + 729, X)
OCTIC = NUM.exquo(sp.Poly(X**3, X))


def characteristic(weights):
    return sum((Fraction(1, n) for n in weights), Fraction(-1))


def transfers():
    # For each pair mapped to the same target point, use the lightest target
    # weights consistent with that assignment. A larger weight tightens the bound.
    survivors = []
    count = 0
    for source in combinations(sp.primerange(3, 100), 3):
        for left, right in combinations(source, 2):
            third, = set(source) - {left, right}
            target = (left * right, third, 2)
            upper = characteristic(source) / characteristic(target)
            if left + right <= upper:
                survivors.append((source, target))
            count += 1
    print(f'transfer pair collisions, odd primes <100: {count} checked, {len(survivors)} survive')
    assert not survivors


def critical_remainder(double_index, single_index, linear=1):
    h = X**2 + linear * X + S
    derivative = X**(single_index - 1) * h**(double_index - 1)
    primitive = sp.integrate(derivative, X)
    return sp.factor(sp.Poly(sp.rem(primitive, h, X), X).nth(1))


def covers():
    septic = sp.integrate(105 * X**2 * (1 - X)**4, X)
    assert sp.expand(septic + (15 * (1-X)**7 - 35 * (1-X)**6 + 21 * (1-X)**5) - 1) == 0
    for double, single in [(3, 7), (5, 3)]:
        print(f'doubled {double}, single {single}: {critical_remainder(double,single)}')
        print(f'  zero linear coefficient: {critical_remainder(double,single,0)}')
    cubic = 10*S**3 - 90*S**2 + 105*S - 28
    assert all(cubic.subs(S, i) % 19 for i in range(19))
    assert critical_remainder(5, 3).subs(S, 3) == 0
    assert NUM.diff().as_expr().expand() == (55 * X**2 * H**4).expand()
    disc = sp.discriminant(NUM.as_expr() - 729*T, X)
    assert sp.factor(disc / (T**2 * (T-1)**8)) == -(3**60 * 5**10 * 11**11)
    print('cubic roots mod 19: none; degree-11 discriminant constant: -3^60*5^10*11^11')
    fake = NUM - sp.Poly(648, X)  # t = 8/9
    shifted = sp.Poly(fake.as_expr().subs(X, X+2), X)
    assert all(c % 11 == 0 for c in shifted.all_coeffs()[1:])
    assert shifted.LC() % 11 and shifted.TC() % 121 == 88
    print('control t=8/9: Eisenstein at 11 after shift by 2, constant mod 121 = 88')


def frobenius_counts(polynomial, prime, expected):
    # The roots fixed by the k-th Frobenius are exactly the roots of factors
    # whose degrees divide k. This checks factor degrees without factoring.
    x = sp.Poly(X, X, modulus=prime)
    power = x
    for k in range(1, polynomial.degree() + 1):
        base = power
        power = sp.Poly(1, X, modulus=prime)
        exponent = prime
        while exponent:
            if exponent % 2:
                power = (power * base).rem(polynomial)
            base = (base * base).rem(polynomial)
            exponent //= 2
        fixed = (power - x).gcd(polynomial).degree()
        assert fixed == sum(d for d in expected if k % d == 0)


def degrees(polynomial, prime):
    modular = sp.Poly(polynomial, X, modulus=prime)
    factors = modular.factor_list()[1]
    assert all(multiplicity == 1 for _, multiplicity in factors)
    pattern = tuple(sorted(factor.degree() for factor, _ in factors))
    if prime in (2, 37, 43):
        frobenius_counts(modular, prime, pattern)
    return pattern


def power_classes(prime, exponent):
    count = gcd(prime-1, exponent)
    generator = int(sp.primitive_root(prime))
    return [pow(generator, i, prime) for i in range(count)]


def local_types(prime):
    # Branch labels indicate which of A, B, C is divisible by prime.
    units = {degrees(NUM.as_expr() - 729*j, prime) for j in range(2, prime)}
    simple = degrees(OCTIC.as_expr(), prime)
    at_a = {tuple(sorted(simple + degrees(1485*X**3 - 729*u, prime)))
            for u in power_classes(prime, 3)}
    at_b = {tuple(sorted((1,) + degrees(99*X**10 - 11*729*u*X**5 + (729*u)**2, prime)))
            for u in power_classes(prime, 5)}
    at_c = {degrees(5*X**11 - 729*u, prime) for u in power_classes(prime, 11)}
    return {'U': units, 'A': at_a, 'B': at_b, 'C': at_c}


def affine_patterns(multiplier):
    if multiplier == 1:
        return {(1,)*11, (11,)}
    order = int(sp.n_order(multiplier, 11))
    return {(1,) + (order,)*(10//order)}


def sieve(prime_limit):
    affine = set().union(*(affine_patterns(a) for a in range(1, 11)))
    forced = {'affine': [], 'pure': []}
    for prime in sp.primerange(2, prime_limit + 1):
        if prime in (3, 5, 11):
            continue
        patterns = local_types(prime)
        if prime == 2:
            print('at 2:', {k: sorted(v) for k, v in patterns.items()})
        labels = {}
        for name, allowed in [('affine', affine), ('pure', affine_patterns(prime % 11))]:
            possible = ''.join(k for k, types in patterns.items() if types & allowed)
            assert 'C' in possible
            if possible == 'C':
                forced[name].append(prime)
            labels[name] = possible
        print(f"{prime:2}  {labels['pure']:4}  {labels['affine']}")
    for name, primes in forced.items():
        print(f'{name}: forced divisors of C = {primes}, product = {prod(primes)}')


def boundary():
    c, v = sp.symbols('c v')
    scaled = sum(coeff * 5**10 * c**(11-k) * (v/5)**k
                 for (k,), coeff in NUM.terms()) - 729 * 5**10 * (1+c)**15
    assert scaled.subs(c, 0) == v**11 - 3**6 * 5**10
    print('boundary polynomial: V^11 - 3^6*5^10')


def wronskian_image(x, y):
    if min(x, y) < 2 or gcd(x, y) != 1:
        raise ValueError('The two summands must be coprime integers greater than one.')
    z = x + y
    factors = [sp.factorint(n) for n in (x, y, z)]
    gx, gy, gz = (gcd(*(int(n * v // prime) for prime, v in factorization.items()))
                  for n, factorization in zip((x, y, z), factors))
    image = gcd(z * gx * gy, y * gx * gz, x * gy * gz) // gcd(gx, gy, gz)
    baseline = x * y * z // prod(prod(factorization) for factorization in factors)
    assert image % baseline == 0
    return image, baseline


def wronskians():
    controls = [(2, 7, 17, 3, 71, 2), (3, 5, 11, 4, 122, 2),
                (7, 3, 13, 2, 2, 9), (1414, 3, 2213459, 2, 65, 7)]
    dx, dy, dz = -7 * 64, -8 * 3 * 17**2, -52 * 2 * 71
    assert dx + dy == dz and 128 * dy - 4913 * dx == 1313216
    for a, p, b, q, c, r in controls:
        assert a**p + b**q == c**r
        image, baseline = wronskian_image(a**p, b**q)
        print(f'{a}^{p}+{b}^{q}={c}^{r}: W image / baseline = {image//baseline}')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument('--critical-pair', nargs=2, type=int, metavar=('DOUBLE', 'SINGLE'),
                       help='derive the coefficient condition for two equal critical values')
    modes.add_argument('--wronskian', nargs=2, type=int, metavar=('X', 'Y'),
                       help='compute the Wronskian image for coprime summands X and Y')
    modes.add_argument('--prime-limit', type=int, default=97,
                       help='largest good prime in the degree-eleven sieve (default 97)')
    args = parser.parse_args()
    if args.critical_pair:
        if min(args.critical_pair) < 2:
            parser.error('ramification indices must be at least two')
        for linear in (1, 0):
            print(f'linear coefficient {linear}: {critical_remainder(*args.critical_pair, linear)}')
        return
    if args.wronskian:
        try:
            image, baseline = wronskian_image(*args.wronskian)
        except ValueError as exc:
            parser.error(str(exc))
        print(f'W image = {image} Z, radical baseline = {baseline}')
        return
    if args.prime_limit < 2:
        parser.error('prime limit must be at least two')
    transfers()
    covers()
    print('q   pure  affine   (U = all bases units)')
    sieve(args.prime_limit)
    boundary()
    wronskians()


if __name__ == '__main__':
    main()
