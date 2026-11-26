"""Check the two rational newform candidates for the level-79072 Frey curve."""
import argparse
from ast import literal_eval
from hashlib import sha256
from pathlib import Path


DIGEST = "668a49dba97210ebc97c70e6ecfb58eddef76bd02b5dea9c2bf8597d7b713623"


def trace(q, a2, a4, a6):
    """Frobenius trace for a good model y^2=x^3+a2*x^2+a4*x+a6 at an odd prime."""
    squares = {i*i % q for i in range(q)}
    total = 0
    for x in range(q):
        value = (((x + a2)*x + a4)*x + a6) % q
        if value:
            total += 1 if value in squares else -1
    return -total


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("curves", type=Path, help="Cremona curves.70000-79999 file")
    data = parser.parse_args().curves.read_bytes()
    if sha256(data).hexdigest() != DIGEST:
        raise ValueError("Cremona table SHA-256 mismatch")
    possible = set()
    for b in range(5):
        c_power = (b**4 + 1) % 5
        possible.add(trace(5, 2*b*b, c_power, 0))
    if possible != {-2, 2}:
        raise ValueError(f"Unexpected Frey traces at 5: {possible}")
    print("Frey traces at 5:", sorted(possible))
    candidates = {}
    for line in data.decode("ascii").splitlines():
        conductor, label, number, coeff, *_ = line.split()
        if conductor != "79072":
            continue
        a1, a2, a3, a4, a6 = literal_eval(coeff)
        if (a1, a3) != (0, 0) or number != "1":
            raise ValueError(f"Unexpected curve model or index: {line}")
        ap = trace(5, a2, a4, a6)
        candidates[label] = (ap, trace(683, a2, a4, a6))
        if any((ap - value) % 31 == 0 for value in possible):
            raise ValueError(f"Surviving rational isogeny class {label}")
    if candidates != {"a": (-1, -4), "b": (-1, 4)}:
        raise ValueError(f"Unexpected level-79072 classes: {candidates}")
    for label, (a5, a683) in candidates.items():
        print(f"79072{label}: a_5={a5}, a_683={a683}")


if __name__ == "__main__":
    main()
