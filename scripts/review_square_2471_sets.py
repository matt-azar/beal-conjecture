"""C7 replay: recover all allowed local trace sets by enumerating 31st powers first."""
from collections import defaultdict
from itertools import product
from math import gcd, isqrt, lcm
from pathlib import Path
import argparse

from check_square_2471 import class_set, generic_set  # used only for comparison

D, P = 2471, 31


def times(q, z, w):
    u, a = z
    v, b = w
    return ((u*v - D*a*b) % q, (u*b + v*a) % q)


def ring_power(q, z, n):
    result = (1, 0)
    while n:
        if n % 2:
            result = times(q, result, z)
        z = times(q, z, z)
        n //= 2
    return result


def image_of_power(q):
    roots = [r for r in range(q) if (r*r+D) % q == 0]
    if not roots:
        return {ring_power(q, z, P) for z in product(range(q), repeat=2)}
    # Interpolate the pair of values at +r and -r, including zero at either root.
    r = roots[0]
    half, scale = pow(2, -1, q), pow(2*r, -1, q)
    powers = {pow(x, P, q) for x in range(q)}
    return {((u+v)*half % q, (u-v)*scale % q) for u, v in product(powers, repeat=2)}


def local_sets(q):
    exponents = defaultdict(set)
    for e in range(lcm(q-1, P)):
        exponents[pow(D, e, q)].add(e % P)
    fibers = [0]*q
    for y in range(q):
        fibers[y*y % q] += 1
    point_counts = {}
    inverse_norm = pow(pow(2, P, q), -1, q)
    half = pow(2, -1, q)
    eta_inv = (90621*half*inverse_norm % q, -391*half*inverse_norm % q)
    powers = image_of_power(q)
    signed, unsigned = defaultdict(set), defaultdict(set)
    for k in range(P):
        multiplier = ring_power(q, eta_inv, k)
        for w in powers:
            u, a = times(q, w, multiplier)
            if a not in exponents:
                continue
            r = u*pow(a, -1, q) % q
            if (r*r+D) % q:
                if r not in point_counts:
                    points = 1 + sum(fibers[(x*((x+r)**2+D)) % q] for x in range(q))
                    point_counts[r] = q+1-points
                # Scaling (r,1) to (u,a) twists the normalized curve by a.
                traces = {(point_counts[r]*(fibers[a]-1)) % P}
                both = traces
            else:
                traces = {((q+1)*(fibers[2*u % q]-1)) % P}
                both = {(q+1) % P, -(q+1) % P}
            for t in exponents[a]:
                signed[t,k].update(traces)
                unsigned[t,k].update(both)
    return signed, unsigned


def generic_trace_set(q, signed):
    roots = [0]*q
    for y in range(q):
        roots[y*y % q] += 1
    powers = {pow(c, P, q) for c in range(q)}
    # For U=a*r the curve is the twist by a of the curve with U=r and d^x=d.
    traces = [q-sum(roots[x*((x+r)**2+D) % q] for x in range(q)) for r in range(q)]
    found = set()
    for a in {pow(D, t, q) for t in range(q-1)}:
        for r in range(q):
            w = a*a*(r*r+D) % q
            if w and w in powers:
                found.add((roots[a]-1)*traces[r] % P)
            elif not w:
                if signed:
                    found.add((roots[2*a*r % q]-1)*(q+1) % P)
                else:
                    found.update(((q+1) % P, -(q+1) % P))
    return found


def descent_sieve():
    # At these split moduli, U+ar and U-ar are inverse eta-powers
    # times 31st powers. Subtract the two expressions to eliminate U.
    moduli = [P**2] + [q for q in range(P+1, 11720, P)
                        if all(q % j for j in range(2, isqrt(q)+1))
                        and pow(-D, (q-1)//2, q) == 1]
    for square in (False, True):
        period = 2*P if square else P  # period in t, with x=2t+1
        pairs = set(product(range(period), range(P)))
        for q in moduli:
            r = next(r for r in range(q) if (r*r+D) % q == 0)
            eta = [(90621+sgn*391*r)*pow(2, -1, q) % q for sgn in (1,-1)]
            powers = {pow(c, P, q) for c in range(q)}
            squares = {u*u % q for u in range(q)}
            keep = set()
            for k in range(P):
                left, right = [{v*pow(z, -k, q) % q for v in powers} for z in eta]
                for t in range(period):
                    ar = pow(D, t, q)*r % q
                    if (t,k) in pairs and any(
                        (v-2*ar) % q in right and (not square or (v-ar) % q in squares)
                        for v in left
                    ):
                        keep.add((t,k))
            pairs = keep
        print(f"descent moduli={len(moduli)} square_U={square} survivors={len(pairs)}")
        if square:
            print("fourth-power (x mod 124, k):", sorted((2*t+1, k) for t,k in pairs))


def kernel_dimension(array):
    import numpy as np
    a = array.copy() % P
    rank = 0
    for j in range(a.shape[1]):
        candidates = np.flatnonzero(a[rank:, j])
        if not len(candidates):
            continue
        pivot = rank+int(candidates[0])
        a[[rank,pivot]] = a[[pivot,rank]]
        a[rank] = (a[rank]*pow(int(a[rank,j]), -1, P)) % P
        a[rank+1:] = (a[rank+1:]-a[rank+1:,j:j+1]*a[rank]) % P
        rank += 1
    return a.shape[1]-rank


def check_systems(prefix, tables):
    import numpy as np
    def read(q):
        words = [int(t) for t in Path(f"{prefix}_{q}.txt").read_text().split()]
        return np.array(words[1:], dtype=np.int64).reshape(words[0], words[0]).T

    primes = (61, 683, 1117)
    operators = [read(q) for q in primes]
    identity = np.eye(len(operators[0]), dtype=np.int64)
    if any(np.any((a@b-b@a) % P) for a,b in product(operators, repeat=2)):
        raise ValueError("Hecke operators do not commute")
    # Stack all eigenvector equations. A linear factor over F_31 suffices:
    # every allowed trace is in F_31 and the operators commute.
    systems = {(): []}
    for op in operators:
        candidates = {}
        for a in range(P):
            shifted = op-a*identity
            if kernel_dimension(shifted):
                candidates[a] = shifted
        systems = {eigenvalues+(a,): equations+[matrix]
                   for eigenvalues,equations in systems.items()
                   for a,matrix in candidates.items()
                   if kernel_dimension(np.vstack(equations+[matrix]))}
    dims = {system: kernel_dimension(np.vstack(equations)) for system,equations in systems.items()}
    if sum(dims.values()) != len(identity):
        raise ValueError("the joint eigenspaces do not span the input")
    print(f"joint eigenvalue triples (dimension): {dims}")
    for i, label in enumerate(("signed", "unsigned")):
        active = list(product(range(P), repeat=2))
        for j, q in enumerate(primes):
            active = [(t,k) for t,k in active if any(
                all(system[h] in tables[primes[h]][i][t,k] for h in range(j+1))
                for system in dims)]
            print(f"{label} after {q}: {len(active)} classes compatible with a full triple")
        if active:
            raise ValueError(active)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--matrix-prefix", default="docs/replays/square-2471/TV0")
    args = parser.parse_args()
    for signed in (True, False):
        chosen = []
        for q in range(3, 230):
            if gcd(q, 2*P*D) != 1 or any(q % n == 0 for n in range(2, isqrt(q)+1)):
                continue
            found = generic_trace_set(q, signed)
            if found != set(generic_set(q, signed)):
                raise ValueError((q, signed, found))
            if len(found) <= 15:
                chosen.append(q)
        print(f"signed={signed} generic filters={len(chosen)} first={chosen[0]} last={chosen[-1]}")
    descent_sieve()
    tables = {}
    for q in (61, 683, 1117):
        tables[q] = local_sets(q)
        for use_sign, table in zip((True, False), tables[q]):
            for t,k in product(range(P), repeat=2):
                expected = set(class_set(q, t, k, signed=use_sign))
                if table[t,k] != expected:
                    raise ValueError((q, t, k, use_sign, table[t,k], expected))
            largest = max(map(len, table.values()))
            empty = sum(not s for s in table.values())
            print(f"q={q} signed={use_sign} matched=961 maximum={largest} empty={empty}")
    check_systems(args.matrix_prefix, tables)
