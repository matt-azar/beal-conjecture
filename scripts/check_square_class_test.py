"""Class test for d^x + U^2 = c^p with x odd and c odd, where p divides h(-d). Bases 263 (p=13) and 2471 (p=31).

  python3 scripts/check_square_class_test.py --base 263 filters [--unsigned]
  python3 scripts/check_square_class_test.py --base 263 verify [DIR/PREFIX] [--unsigned-space]
  python3 scripts/check_square_class_test.py --base 263 sieve

Same method as scripts/check_square_2471.py, with the base as a parameter. For 2471 it reads the matrices
of that replay and must give the same answer. Standard library only. Method: docs/square-summand-2471.md.
"""
import sys

BASES = {
    263: dict(p=13, eta=(141, 7), small=range(5, 120), max_set=9, control=[3, 5, 7, 11, 17, 19],
              class_primes=[157, 313, 521, 677, 937], cm_multiplicity=4, prefix="docs/replays/square-263/TW0"),
    2471: dict(p=31, eta=(90621, 391), small=range(5, 230), max_set=15, control=[3, 5, 11, 13, 17, 19],
               class_primes=[61, 683, 1117, 1489, 1861, 2357, 1303, 2543], cm_multiplicity=8,
               prefix="docs/replays/square-2471/TV0"),
}
D = P = ETA_T = ETA_H = None
_squares, _traces = {}, {}


def setup(base):
    global D, P, ETA_T, ETA_H
    cfg = BASES[base]
    D, P, (ETA_T, ETA_H) = base, cfg["p"], cfg["eta"]
    assert D % 16 == 7 and ETA_T**2 + D * ETA_H**2 == 4 * 2**P    # eta = (T + H s)/2 has norm 2^p
    _squares.clear()
    _traces.clear()
    return cfg


def is_prime(n):
    return n > 1 and all(n % i for i in range(2, int(n**0.5) + 1))


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
    """Residues mod p allowed for a_q(f) when (U, W) = (u, w) mod q, W = U^2 + d^x, q not dividing 2*p*d."""
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
    """Union over every odd x and every U such that U^2 + d^x is a p-th power mod q."""
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


def local_solutions(q, t, k, e=None):
    """U mod q with eta^k (U + a s) a p-th power in R/q, a = d^e (default e = t). q must be class-sensitive."""
    r, inv2 = root_of_minus_d(q), pow(2, -1, q)
    a = pow(D, t if e is None else e, q)
    if r is not None:                           # split: both embeddings s -> r, -r with the same U
        powers = {pow(c, P, q) for c in range(q)}
        plus = pow((ETA_T + ETA_H * r) * inv2 % q, k, q)
        minus = pow((ETA_T - ETA_H * r) * inv2 % q, k, q)
        return [u for u in range(q) if plus * (u + a * r) % q in powers and minus * (u - a * r) % q in powers]
    assert (q * q - 1) % P == 0                 # inert: one condition in F_{q^2}
    eta_k = power(q, (ETA_T * inv2 % q, ETA_H * inv2 % q), k)
    return [u for u in range(q) if power(q, mul(q, eta_k, (u, a)), (q * q - 1) // P) == (1, 0)]


def class_set(q, t, k, signed=True, orbit=True):
    """Residues allowed for the class (t, k): x = 2t+1 (mod 2p), beta^p = eta^k (U + a s), a = d^((x-1)/2).

    Raising x by 2p multiplies a by d^p. Solutions scale by lam = d^p, a p-th power, and the Frey curve is
    twisted by lam, so the trace changes by the Legendre symbol (d/q). orbit=False enumerates every a.
    """
    found = set()
    exponents = [t] if orbit else list({pow(D, t + P * j, q): t + P * j for j in range(q)}.values())
    for e in exponents:
        big_d = pow(D, 2 * e + 1, q)
        for u in local_solutions(q, t, k, e):
            found |= frey_trace(q, u, u * u + big_d, signed)
    if orbit and pow(D, (q - 1) // 2, q) != 1:
        found |= {-v % P for v in found}
    return sorted(found)


# ---- linear algebra over F_p; a matrix C acts on row vectors v -> v C ----
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
    echelon, _ = rref([product[i] + [int(i == j) for j in range(m)] for i in range(m)])
    kernel = [row[m:] for row in echelon if not any(row[:m])]
    return [[sum(k[i] * reduced[i][j] for i in range(m)) % P for j in range(size)] for k in kernel]


def filters(cfg, signed):
    print(3, *generic_set(3, signed))
    for q in cfg["small"]:
        if is_prime(q) and (2 * D * P) % q:
            residues = generic_set(q, signed)
            if len(residues) <= cfg["max_set"]:
                print(q, *residues)


def verify(cfg, prefix):
    primes = cfg["control"] + sorted(cfg["class_primes"])
    c = {q: load(f"{prefix}_{q}.txt") for q in primes}
    m = len(c[3])
    identity = [[int(i == j) for j in range(m)] for i in range(m)]
    assert all(matmul(c[a], c[b]) == matmul(c[b], c[a]) for a in primes for b in primes if a < b)
    print(f"base {D}, exponent {P}: retained space of dimension {m}; the {len(primes)} operators commute")
    cm = identity
    for q in cfg["control"]:
        cm = cut(cm, c[q], [a_q(q, 0, q - 1) % P])
    assert len(cm) == cfg["cm_multiplicity"], len(cm)
    for q in primes:
        assert len(cut(cm, c[q], [a_q(q, 0, q - 1) % P])) == len(cm), q
    print(f"control: the CM system of y^2 = x^3 - x has multiplicity {len(cm)} and every operator matches point counts")
    first = cfg["class_primes"][0]
    for t, k in [(0, 1), (2, 8 % P), (5, 3), (P - 1, P - 2)]:
        assert class_set(first, t, k) == class_set(first, t, k, orbit=False), (t, k)
    print("control: orbit and direct enumerations of class sets agree on 4 samples")
    for signed in (True, False):
        survivors, needed = [], {}
        for t in range(P):
            for k in range(P):
                space = identity
                for q in cfg["class_primes"]:
                    space = cut(space, c[q], class_set(q, t, k, signed))
                    if not space:
                        needed[q] = needed.get(q, 0) + 1
                        break
                if space:
                    survivors.append((2 * t + 1, k, len(space)))
        label = "signed multiplicative traces" if signed else "both multiplicative signs allowed"
        print(f"{label}: classes surviving = {survivors}; last prime needed -> classes: {dict(sorted(needed.items()))}")
        assert not survivors
    print(f"all {P * P} classes (x mod {2 * P}, k) have zero common kernel")


def sieve(limit=6000):
    """Classes with a local solution at every split prime q = 1 (mod p) below the limit. No Hecke input."""
    moduli = [q for q in range(3, limit) if is_prime(q) and q % P == 1 and (2 * D) % q and root_of_minus_d(q) is not None]
    alive = {(t, k) for t in range(P) for k in range(P)}
    for q in moduli:
        alive = {(t, k) for (t, k) in alive if local_solutions(q, t, k)}
    print(f"base {D}: {len(moduli)} split primes = 1 mod {P} below {limit}; classes with local solutions at all: {len(alive)} of {P * P}")
    print(sorted((2 * t + 1, k) for t, k in alive))


if __name__ == "__main__":
    args = sys.argv[1:]
    if len(args) < 3 or args[0] != "--base" or int(args[1]) not in BASES:
        sys.exit(__doc__)
    config = setup(int(args[1]))
    if args[2] == "filters":
        filters(config, "--unsigned" not in args)
    elif args[2] == "verify":
        rest = [a for a in args[3:] if not a.startswith("--")]
        verify(config, rest[0] if rest else config["prefix"])
    elif args[2] == "sieve":
        sieve()
    else:
        sys.exit(__doc__)
