"""Verify the Beal filter on Bennett and Siksek's Lebesgue–Nagell table."""

import argparse
import hashlib
import json
from math import gcd
from pathlib import Path


PRIMES = (2, 3, 5, 7, 11)
# samirsiksek/lebnag, commit e8b1dab1f30487b0c38eee94b297bd88c821924f
EXPECTED_SHA256 = "20be2359ca6f16965b2e3b61fe944d0efd9efee67d26a72cb7586bf31a93a822"


def valuation_one_prime(x):
    """Return a prime of multiplicity one, or None if no such prime exists."""
    remainder = x
    p = 2
    while p * p <= remainder:
        exponent = 0
        while remainder % p == 0:
            remainder //= p
            exponent += 1
        if exponent == 1:
            return p
        p = 3 if p == 2 else p + 2
    return remainder if remainder > 1 else None


def check(path):
    data = path.read_bytes()
    if hashlib.sha256(data).hexdigest() != EXPECTED_SHA256:
        raise ValueError("SHA-256 mismatch: expected the pinned authors' table")
    # The upstream Magma file assigns one array of integer rows to `sols`.
    _, _, array = data.decode("ascii").partition("sols:=")
    rows = json.loads(array.strip().removesuffix(";"))
    if len(rows) != 1240:
        raise ValueError(f"expected 1240 rows, found {len(rows)}")

    candidates = []
    seen = set()
    for row in rows:
        n, x, c, *exponents = row
        if len(exponents) != len(PRIMES) or min(exponents) < 0:
            raise ValueError(f"invalid prime exponents in {row}")
        key = (n, x, c)
        if key in seen or n < 3 or x < 1 or c < 2 or gcd(x, c) != 1:
            raise ValueError(f"duplicate or invalid triple {key}")
        seen.add(key)

        d = c**n - x*x
        if d <= 0:
            raise ValueError(f"nonpositive difference for {key}")
        remainder = d
        for p, expected in zip(PRIMES, exponents):
            valuation = 0
            while remainder % p == 0:
                remainder //= p
                valuation += 1
            if valuation != expected:
                raise ValueError(f"incorrect valuation at {p} for {key}")
        if remainder != 1:
            raise ValueError(f"difference contains a prime above 11 for {key}")

        # D = 1 admits every exponent. Otherwise its possible exponents are
        # exactly the divisors of the gcd of its listed prime multiplicities.
        if d != 1 and gcd(*exponents) < 3:
            continue
        if x == 1:
            raise ValueError(f"surviving X = 1 permits every exponent for {key}")
        witness = valuation_one_prime(x)
        if witness is None:
            raise ValueError(f"no valuation-one exclusion witness for {key}")
        candidates.append((n, x, c, d, witness))

    distinct_x = len({row[1] for row in candidates})
    if (len(candidates), distinct_x) != (12, 11):
        raise ValueError(f"unexpected candidate counts: {len(candidates)}, {distinct_x}")
    print("n X C D prime_with_v_p(X)=1")
    for row in candidates:
        print(*row)
    print(f"Verified {len(seen)} triples, {len(candidates)} higher-power differences, "
          f"{distinct_x} distinct X, 0 survivors.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("table", type=Path, help="path to lebesgue_nagell_solutions.txt")
    try:
        check(parser.parse_args().table)
    except (OSError, ValueError) as error:
        parser.exit(1, f"{error}\n")
