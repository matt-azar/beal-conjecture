"""Test the required traces on the full discriminant-7 Brandt module at level 79072."""

from itertools import product
from math import gcd, isqrt

import numpy as np
from flint import fmpz_mat, nmod_mat


P = 31
IDENTITY = (2, 0, 0, 0)
I = (0, 2, 0, 0)
J = (0, 0, 2, 0)
W = (1, 0, 1, 0)
IW = (0, 1, 0, 1)


def check(condition, message):
    if not condition:
        raise ValueError(message)


def norm_representatives(q):
    """Represent left unit classes of (a+b*i+c*j+d*ij)/2 of norm q."""
    representatives = []
    bound = isqrt(4*q // 7)
    for c, d in product(range(-bound, bound + 1), repeat=2):
        remaining = 4*q - 7*(c*c + d*d)
        if remaining < 0:
            continue
        a_bound = isqrt(remaining)
        for a in range(-a_bound, a_bound + 1):
            if (a-c) % 2:
                continue
            b_abs = isqrt(remaining - a*a)
            if a*a + b_abs*b_abs != remaining or (b_abs-d) % 2:
                continue
            for b in sorted({-b_abs, b_abs}):
                element = (a, b, c, d)
                orbit = (element, (-b, a, -d, c), (-a, -b, -c, -d), (b, -a, d, -c))
                if element == min(orbit):
                    representatives.append(element)
    check(len(representatives) == q+1, f"Wrong norm-{q} neighbor count")
    return representatives


def local_matrix(element, modulus):
    """Send i and w=(1+j)/2 to the matrices in the accompanying proof."""
    a, b, c, d = element
    x, y = (a-c)//2, (b-d)//2
    if modulus == 32:
        entries = (x+6*c, -y+5*d, y+6*d, x-5*c)
    elif modulus == 353:
        entries = (x+c-46*d, -y+46*c, y+46*c+d, x+46*d)
    else:
        raise ValueError("Unsupported modulus")
    return np.array(entries, dtype=np.int64).reshape(2, 2) % modulus


class ProjectiveLine:
    def __init__(self, modulus):
        self.modulus = modulus
        nonunits = list(range(0, 32, 2)) if modulus == 32 else [0]
        self.x = np.array(list(range(modulus)) + [1]*len(nonunits))
        self.y = np.array([1]*modulus + nonunits)
        self.inverses = np.array([pow(a, -1, modulus) if gcd(a, modulus) == 1 else 0
                                  for a in range(modulus)])

        one, i, w, iw = [local_matrix(g, modulus) for g in (IDENTITY, I, W, IW)]
        check(np.array_equal(one, np.eye(2, dtype=int)), "Incorrect identity")
        for relation in (i@i + one, w@w - w + 2*one, w@i - i + iw, i@w - iw):
            check(np.all(relation % modulus == 0), "Quaternion relation failed")
        rows = [m.ravel().tolist() for m in (one, i, w, iw)]
        check(gcd(int(fmpz_mat(rows).det()), modulus) == 1, "Splitting is not onto")

    def action(self, element):
        m = self.modulus
        (a, b), (c, d) = local_matrix(element, m)
        u = (a*self.x + b*self.y) % m
        v = (c*self.x + d*self.y) % m
        other_chart = 32 + ((v*self.inverses[u]) % 32)//2 if m == 32 else 353
        permutation = np.where(self.inverses[v] != 0, (u*self.inverses[v]) % m, other_chart)
        check(np.array_equal(np.sort(permutation), np.arange(len(self.x))),
              "Projective action is not bijective")
        return permutation


def sector_basis(unit, ramified, sibling, j_sign, sibling_sign):
    """Give the representative, orbit index and character on every free orbit."""
    actions = [np.arange(len(unit)), unit, ramified, unit[ramified]]
    actions += [sibling[action] for action in actions]
    signs = [1, 1, j_sign, j_sign]
    signs += [sibling_sign*s for s in signs]
    indices = np.full(len(unit), -1, dtype=np.int64)
    weights = np.zeros(len(unit), dtype=np.int64)
    representatives = []
    for x in range(len(unit)):
        if indices[x] >= 0:
            continue
        orbit = [action[x] for action in actions]
        check(len(set(orbit)) == 8 and np.all(indices[orbit] == -1),
              "Unexpected stabilizer or overlapping orbits")
        indices[orbit] = len(representatives)
        weights[orbit] = signs
        representatives.append(x)
    return np.array(representatives), indices, weights


def hecke_matrix(local_actions, basis):
    """Rows act on column vectors of values of a function at the representatives."""
    reps, indices, weights = basis
    rows = np.arange(len(reps))
    result = np.zeros((len(reps), len(reps)), dtype=np.int32)
    x, y = np.divmod(reps, 354)
    for action32, action353 in local_actions:
        images = 354*action32[x] + action353[y]
        result[rows, indices[images]] += weights[images]
    check(np.array_equal(result, result.T), "Brandt symmetry failed")
    return result


def eigenvectors(matrix, eigenvalue):
    shifted = matrix.copy()
    shifted[np.diag_indices_from(matrix)] -= eigenvalue
    reduced = nmod_mat((shifted % P).tolist(), P)
    nullspace, dimension = reduced.nullspace()
    vectors = np.array([[int(nullspace[i, j]) for j in range(dimension)]
                        for i in range(nullspace.nrows())], dtype=np.int32)
    check(np.all(shifted @ vectors % P == 0), "Incorrect nullspace vectors")
    return vectors


def main():
    line32, line353 = ProjectiveLine(32), ProjectiveLine(353)

    def product_action(g):
        return (354*line32.action(g)[:, None] + line353.action(g)).ravel()

    unit = product_action(I)
    ramified = product_action(J)
    # In the second chart the even second coordinate is stored divided by 2.
    sibling32 = np.array([i ^ 16 if i < 32 else i ^ 8 for i in range(48)])
    sibling = (354*sibling32[:, None] + np.arange(354)).ravel()
    for a, b in product((unit, ramified, sibling), repeat=2):
        check(np.array_equal(a[a], np.arange(len(a))), "Involution check failed")
        check(np.array_equal(a[b], b[a]), "Involutions do not commute")

    neighbors = {q: [(line32.action(g), line353.action(g)) for g in norm_representatives(q)]
                 for q in (5, 683)}
    expected_dimensions = {(-1, -1): (2, 5), (1, -1): (2, 5),
                           (-1, 1): (1, 7), (1, 1): (2, 14)}
    expected_dets = {(-1, -1): 11, (-1, 1): 28, (1, -1): 6, (1, 1): 26}
    full_det = 1
    print("j  swap   dim  a5  nullity(T5-a5)  a683  joint nullity")
    for (j_sign, sibling_sign), expected in expected_dimensions.items():
        basis = sector_basis(unit, ramified, sibling, j_sign, sibling_sign)
        t5, t683 = [hecke_matrix(neighbors[q], basis) for q in (5, 683)]
        check(len(t5) == 2124, "Wrong sector dimension")
        if (j_sign, sibling_sign) == (1, 1):
            check(np.all(t5.sum(axis=1) == 6) and np.all(t683.sum(axis=1) == 684),
                  "Incorrect action on the constant function")
        # Each T5 row has at most six nonzero entries. Square it exactly.
        combined = t683.copy()
        for row_index, row in enumerate(t5):
            columns = row.nonzero()[0]
            combined[row_index] += row[columns] @ t5[columns]
        combined[np.diag_indices_from(combined)] -= 2
        det = int(nmod_mat((combined % P).tolist(), P).det())
        check(det == expected_dets[j_sign, sibling_sign], "Wrong determinant")
        full_det = full_det * det % P
        print(f"det(T5^2 + T683 - 2I), j={j_sign:+d}, swap={sibling_sign:+d}: {det}")
        tests = [(-2, expected[0], {-2: 0}), (2, expected[1], {-2: 0})]
        if sibling_sign == -1:
            # Known exact-level elliptic curves with a5=-1 and a683=-4 or +4.
            tests.append((-1, 2, {-4: int(j_sign == -1), 4: int(j_sign == 1)}))
        for a5, expected_nullity, trace_tests in tests:
            vectors = eigenvectors(t5, a5)
            nullity = vectors.shape[1]
            check(nullity == expected_nullity, "Unexpected T5 nullity")
            images = t683 @ vectors % P
            check(np.all((t5 @ images - a5*images) % P == 0), "Hecke commutation failed")
            for a683, expected_joint in trace_tests.items():
                rank = nmod_mat(((images - a683*vectors) % P).tolist(), P).rank()
                joint = nullity - rank
                print(f"{j_sign:+d}  {sibling_sign:+d}   {len(t5)}  {a5:+2d}"
                      f"        {nullity:2d}        {a683:+3d}       {joint}")
                check(joint == expected_joint, "Unexpected simultaneous kernel")
    check(full_det == 29, "Full determinant failed")
    print(f"Full determinant modulo 31: {full_det}")


if __name__ == "__main__":
    main()
