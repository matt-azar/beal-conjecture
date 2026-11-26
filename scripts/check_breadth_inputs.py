"""Regenerate the C3 cohort and local trace sets. Both commands print TSV."""

import argparse
import csv
import sys
from math import isqrt

from check_twists import reduced_forms, require
from frey_trace_sets import allowed, trace


def prime_divisors(value):
    for prime in range(2, isqrt(value) + 1):
        if value % prime == 0:
            yield prime
            while value % prime == 0:
                value //= prime
    if value > 1:
        yield value


def cohort():
    for d in range(7, 200, 16):
        if all(d % (i * i) for i in range(2, isqrt(d) + 1)):
            h = sum(1 for _ in reduced_forms(-d))
            yield d, h, list(prime_divisors(h))


def point_count_traces(d, p, r, q):
    """Count affine points on each admissible good or nodal cubic."""
    residues = set()
    powers = {pow(c, p, q) for c in range(q)}
    for b in range(q):
        u = (pow(d, r, q) + b**4) % q
        if u not in powers:
            continue
        affine = sum(
            (y*y - x*(x*x + 2*b*b*x + u)) % q == 0
            for x in range(q) for y in range(q)
        )
        # One point at infinity in both cases.
        a = q - affine
        if u:
            require(a == trace(q, 2*b*b, u), f"Good trace mismatch at {(d,p,r,q,b)}")
        else:
            require(b != 0, "Expected an ordinary node with nonzero b")
            # At (0,0), the tangent slopes satisfy m^2 = 2b^2.
            slopes = sum((m*m - 2*b*b) % q == 0 for m in range(q))
            require(a == slopes - 1, f"Nodal trace mismatch at {(d,p,r,q,b)}")
            a *= q + 1
        residues.add(a % p)
    result = sorted(residues)
    require(result == allowed(d, p, r, 12, q), f"Trace set mismatch at {(d,p,r,q)}")
    return result


def integers(values):
    return ",".join(map(str, values)) or "-"


def main(table):
    writer = csv.writer(sys.stdout, delimiter="\t", lineterminator="\n")
    if table == "cohort":
        writer.writerow(("d", "h", "prime_divisors"))
        for d, h, primes in cohort():
            writer.writerow((d, h, integers(primes)))
        return
    writer.writerow(("d", "p", "r", "q", "status", "residues"))
    for d, _, primes in cohort():
        for p in primes:
            if p < 5:
                continue
            for r in range(1, 12, 2):
                for q in (3, 5, 7):
                    if 2*d*p % q == 0:
                        writer.writerow((d, p, r, q, "skip", "-"))
                    else:
                        residues = point_count_traces(d, p, r, q)
                        writer.writerow((d, p, r, q, "apply", integers(residues)))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("table", choices=("cohort", "traces"))
    main(parser.parse_args().table)
