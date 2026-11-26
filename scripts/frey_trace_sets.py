"""Residues mod p allowed for a_l of the Frey curve Y^2 = X^3 + 2b^2 X^2 + c^p X
attached to a primitive solution of d^x + b^4 = c^p with x = x0 (mod m).

For each prime l (not dividing 2*d*p) the output line is "l r1 r2 ...": every
residue of a_l(f) mod p that some local solution allows, where f is the newform
produced by level lowering. Good reduction gives a_l(E); l | c gives +-(l+1),
with sign + exactly when 2 is a square mod l (split multiplicative reduction).

usage: frey_traces.py d p x0 m l1 l2 ...
"""
import sys


def trace(q, a2, a4):
    squares = bytearray(q)
    for i in range(1, q):
        squares[i * i % q] = 1
    total = 0
    for x in range(q):
        value = ((x + a2) * x + a4) * x % q
        if value:
            total += 1 if squares[value] else -1
    return -total


def allowed(d, p, x0, m, q):
    powers = {pow(c, p, q) for c in range(q)}
    summands = {pow(d, x0 + m * i, q) for i in range(q)}  # all of d^x mod q, x = x0 mod m
    found, cache = set(), {}
    for big_d in summands:
        for b in range(q // 2 + 1):
            c_power = (pow(b, 4, q) + big_d) % q
            if c_power not in powers:
                continue
            if c_power == 0:
                split = pow(2, (q - 1) // 2, q) == 1
                found.add(((q + 1) if split else -(q + 1)) % p)
            else:
                key = (2 * b * b % q, c_power)
                if key not in cache:
                    cache[key] = trace(q, *key) % p
                found.add(cache[key])
    return sorted(found)


if __name__ == "__main__":
    d, p, x0, m = map(int, sys.argv[1:5])
    for q in map(int, sys.argv[5:]):
        assert q > 2 and (2 * d * p) % q and all(q % i for i in range(2, int(q**0.5) + 1))
        print(q, *allowed(d, p, x0, m, q))
