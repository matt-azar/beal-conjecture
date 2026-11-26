"""Replay for docs/square-summand-2471.md: 2471^x + U^2 = c^31 with x odd, c odd.

  python3 scripts/check_square_2471.py filters            class-independent trace sets, one prime per line
  python3 scripts/check_square_2471.py verify DIR/PREFIX  run the class test on Hecke matrices PREFIX_l.txt
                                                          (default: docs/replays/square-2471/TV0)

Standard library only. The Hecke matrices are produced by scripts/check_modsym_hecke.cpp (mode "dump").
"""
import sys

D, P = 2471, 31
ETA_T, ETA_H = 90621, 391                      # eta = (T + H s)/2, s^2 = -d, norm 2^31
assert ETA_T**2 + D * ETA_H**2 == 4 * 2**P
SMALL = [q for q in range(5, 230)]             # candidates for class-independent filters
CLASS_PRIMES = [61, 683, 1117, 1489, 1861, 2357, 1303, 2543]
ALL_PRIMES = [3, 5, 11, 13, 17, 19] + sorted(CLASS_PRIMES)


def is_prime(n):
    return n > 1 and all(n % i for i in range(2, int(n**0.5) + 1))


_squares, _traces = {}, {}


def squares(q):
    if q not in _squares:
        table = bytearray(q)
        for i in range(1, q):
            table[i * i % q] = 1
        _squares[q] = table
    return _squares[q]


def a_q(q, a2, a4):
    """Trace of Frobenius of Y^2 = X^3 + a2 X^2 + a4 X over F_q by point counting."""
    sq, total = squares(q), 0
    for x in range(q):
        value = ((x + a2) * x + a4) * x % q
        if value:
            total += 1 if sq[value] else -1
    return -total


def frey_trace(q, u, w, signed=True):
    """Residues mod 31 allowed for a_q(f) when (U, W) = (u, w) mod q, W = U^2 + d^x, q not dividing 2*31*d."""
    u %= q
    w %= q
    if w == 0:                                  # q | c: multiplicative, tangent slopes +-sqrt(2U)
        plus, minus = (q + 1) % P, -(q + 1) % P
        if not signed:
            return {plus, minus}
        return {plus if squares(q)[2 * u % q] else minus}
    key = (q, u, w)
    if key not in _traces:
        _traces[key] = a_q(q, 2 * u % q, w) % P
    return {_traces[key]}


def generic_set(q, signed=True):
    """Union over every odd x and every U such that U^2 + d^x is a 31st power mod q."""
    powers = {pow(c, P, q) for c in range(q)}
    found = set()
    for big_d in {pow(D, x, q) for x in range(1, 2 * q, 2)}:
        for u in range(q):
            w = (u * u + big_d) % q
            if w in powers:
                found |= frey_trace(q, u, w, signed)
    return sorted(found)


def root_of_minus_d(q):
    return next((s for s in range(q) if (s * s + D) % q == 0), None)


def mul(q, x, y):                               # in F_q[s]/(s^2 + d)
    return ((x[0] * y[0] - D * x[1] * y[1]) % q, (x[0] * y[1] + x[1] * y[0]) % q)


def power(q, x, e):
    result = (1, 0)
    while e:
        if e & 1:
            result = mul(q, result, x)
        x = mul(q, x, x)
        e >>= 1
    return result


def class_set(q, t, k, signed=True, orbit=True):
    """Residues allowed for the class (t, k): x = 2t+1 (mod 62) and beta^31 = eta^k (U + a s), a = d^((x-1)/2).

    Raising x by 62 multiplies a by d^31. Solutions then scale by lam = d^31, a 31st power, and the Frey
    curve is twisted by lam, so the trace changes by the Legendre symbol (d/q). With orbit=False every
    value of a is enumerated directly instead.
    """
    r, inv2 = root_of_minus_d(q), pow(2, -1, q)
    found = set()
    exponents = [t] if orbit else list({pow(D, t + 31 * j, q): t + 31 * j for j in range(q)}.values())
    for e in exponents:
        a, big_d = pow(D, e, q), pow(D, 2 * e + 1, q)
        if r is not None:                       # split: both embeddings s -> r, -r with the same U
            powers = {pow(c, P, q) for c in range(q)}
            plus = pow((ETA_T + ETA_H * r) * inv2 % q, k, q)
            minus = pow((ETA_T - ETA_H * r) * inv2 % q, k, q)
            for u in range(q):
                if plus * (u + a * r) % q in powers and minus * (u - a * r) % q in powers:
                    found |= frey_trace(q, u, u * u + big_d, signed)
        else:                                   # inert: one condition in F_{q^2}
            assert (q * q - 1) % P == 0
            eta_k = power(q, (ETA_T * inv2 % q, ETA_H * inv2 % q), k)
            for u in range(q):
                if power(q, mul(q, eta_k, (u, a)), (q * q - 1) // P) == (1, 0):
                    found |= frey_trace(q, u, u * u + big_d, signed)
    if orbit and pow(D, (q - 1) // 2, q) != 1:
        found |= {-v % P for v in found}
    return sorted(found)


# ---- linear algebra over F_31; a matrix C acts on row vectors v -> v C ----
def load(path):
    words = open(path).read().split()
    m, values = int(words[0]), list(map(int, words[1:]))
    assert len(values) == m * m
    return [values[i * m:(i + 1) * m] for i in range(m)]


def matmul(a, b):
    columns = list(zip(*b))
    return [[sum(x * y for x, y in zip(row, col)) % P for col in columns] for row in a]


def rref(rows):
    rows, pivots, r = [row[:] for row in rows], [], 0
    for j in range(len(rows[0]) if rows else 0):
        s = next((i for i in range(r, len(rows)) if rows[i][j]), None)
        if s is None:
            continue
        rows[r], rows[s] = rows[s], rows[r]
        inverse = pow(rows[r][j], -1, P)
        rows[r] = [x * inverse % P for x in rows[r]]
        for i in range(len(rows)):
            if i != r and rows[i][j]:
                c = rows[i][j]
                rows[i] = [(x - c * y) % P for x, y in zip(rows[i], rows[r])]
        pivots.append(j)
        r += 1
    return rows[:r], pivots


def cut(basis, c, allowed):
    """Subspace of span(basis) annihilated by prod_{a in allowed} (T - a). The span must be T-stable."""
    if not basis:
        return basis
    reduced, pivots = rref(basis)
    size, m = len(c), len(reduced)
    restricted = []
    for b in reduced:
        image = [sum(b[i] * c[i][j] for i in range(size)) % P for j in range(size)]
        coords = [image[p] for p in pivots]
        assert image == [sum(x * reduced[k][j] for k, x in enumerate(coords)) % P for j in range(size)], "not stable"
        restricted.append(coords)
    product = [[int(i == j) for j in range(m)] for i in range(m)]
    for a in allowed:
        product = matmul(product, [[(restricted[i][j] - (a if i == j else 0)) % P for j in range(m)] for i in range(m)])
    augmented = [product[i] + [int(i == j) for j in range(m)] for i in range(m)]
    echelon, _ = rref(augmented)
    kernel = [row[m:] for row in echelon if not any(row[:m])]
    return [[sum(k[i] * reduced[i][j] for i in range(m)) % P for j in range(size)] for k in kernel]


def verify(prefix):
    c = {q: load(f"{prefix}_{q}.txt") for q in ALL_PRIMES}
    m = len(c[3])
    identity = [[int(i == j) for j in range(m)] for i in range(m)]
    assert all(matmul(c[a], c[b]) == matmul(c[b], c[a]) for a in ALL_PRIMES for b in ALL_PRIMES if a < b)
    print(f"dimension of the retained space: {m}; the {len(ALL_PRIMES)} operators commute")

    # Control 1: the level-32 CM form of y^2 = x^3 - x occurs 8 times (4 degeneracy maps, 2 signs),
    # and every operator acts on it by the point count computed here.
    cm = identity
    for q in [3, 5, 11, 13, 17, 19]:
        cm = cut(cm, c[q], [a_q(q, 0, q - 1) % P])
    assert len(cm) == 8, len(cm)
    for q in ALL_PRIMES:
        assert len(cut(cm, c[q], [a_q(q, 0, q - 1) % P])) == 8, q
    print("control: the CM system of y^2 = x^3 - x has multiplicity 8 and all 14 operators match point counts")

    # Control 2: the two descriptions of a class set agree.
    for q, t, k in [(61, 2, 8), (61, 20, 13), (683, 2, 8), (683, 9, 2), (1117, 22, 7)]:
        assert class_set(q, t, k) == class_set(q, t, k, orbit=False), (q, t, k)
    print("control: orbit and direct enumerations of class sets agree on 5 samples")

    for signed in (True, False):
        survivors, needed = [], {}
        for t in range(P):
            for k in range(P):
                space = identity
                for q in CLASS_PRIMES:
                    space = cut(space, c[q], class_set(q, t, k, signed))
                    if not space:
                        needed[q] = needed.get(q, 0) + 1
                        break
                if space:
                    survivors.append((2 * t + 1, k, len(space)))
        label = "signed multiplicative traces" if signed else "both multiplicative signs allowed"
        print(f"{label}: classes surviving = {survivors}; last prime needed -> classes: {dict(sorted(needed.items()))}")
        assert not survivors
    print("all 961 classes (x mod 62, k) have zero common kernel")


if __name__ == "__main__":
    mode = sys.argv[1] if len(sys.argv) > 1 else "verify"
    if mode == "filters":
        signed = "--unsigned" not in sys.argv
        print(3, *generic_set(3, signed))
        for q in SMALL:
            if is_prime(q) and (2 * D * P) % q:
                residues = generic_set(q, signed)
                if len(residues) <= 15:
                    print(q, *residues)
    elif mode == "verify":
        verify(sys.argv[2] if len(sys.argv) > 2 else "docs/replays/square-2471/TV0")
    else:
        sys.exit(__doc__)
