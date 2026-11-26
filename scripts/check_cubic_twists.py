"""Check the two orientations above 2 in the even-c cubic descent."""


# The tuple is (d, trace of eta, coefficient of sqrt(-d) in 2*eta,
# exponent p in Norm(eta)=2**p, obstruction modulus for x=1,3,...,11).
CASES = (
    (167, 3, 7, 11, (9, 19, 9, 9, 19, 9)),
    (2471, 90621, 391, 31, (13, 13, 13, 13, 13, 13)),
)


def check(d, trace, coefficient, p, moduli, expected=None):
    if trace**2 + d * coefficient**2 != 4 * 2**p:
        raise ValueError("Incorrect principal generator above 2")
    exponent = (-pow(p, -1, 3)) % 3
    root_at_two = (-trace * pow(coefficient, -1, 4)) % 4
    for x, modulus in zip(range(1, 12, 2), moduli):
        t = (x - 1) // 2
        # delta is divisible by P exactly when its numerator is 0 mod 4 at P.
        use_eta = (1 + pow(d, t, 4) * root_at_two) % 4 == 0
        signed = coefficient if use_eta else -coefficient
        root = next(r for r in range(modulus) if (r*r + d) % modulus == 0)
        half = pow(2, -1, modulus)
        cubes = {pow(z, 3, modulus) for z in range(modulus)}
        surviving_b = set(range(modulus))
        for r in (root, -root):
            eta = (trace + signed*r) * half % modulus
            multiplier = pow(eta, exponent, modulus)
            shift = pow(d, t, modulus) * r
            surviving_b = {b for b in surviving_b
                           if multiplier * (b*b + shift) * half % modulus in cubes}
        allowed = expected.get(x, set()) if expected else set()
        if surviving_b != allowed:
            raise ValueError(f"Unexpected b at d={d}, x={x}, m={modulus}: {surviving_b}")
        orientation = "eta" if use_eta else "conjugate"
        result = f"b = {sorted(surviving_b)}" if surviving_b else "no b"
        print(f"d={d}, x={x} mod 12, {orientation}, m={modulus}, {result}")


if __name__ == "__main__":
    for case in CASES:
        check(*case)
    # At 263 the two nonempty rows feed the Mordell-curve argument.
    check(263, 141, 7, 13, (9,) * 6, {5: {4, 5}, 11: {4, 5}})
