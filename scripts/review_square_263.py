"""Independent finite checks for the review of PR #28. Python standard library."""
from itertools import product
from math import isqrt


def prime(n):
    return n > 1 and all(n % i for i in range(2, isqrt(n)+1))


def least_root(n):
    """Smallest integer whose thirteenth power is at least n."""
    lo, hi = 0, 1 << ((n.bit_length()+12)//13)
    while lo < hi:
        m = (lo+hi)//2
        if m**13 < n:
            lo = m+1
        else:
            hi = m
    return lo


def bounded_search():
    hits = []
    for x in range(1, 40):
        d = 263**x
        # Only iterate over c in the interval corresponding to 0 < U < 20000.
        for c in range(least_root(d+1), least_root(d+20000**2)):
            u = isqrt(c**13-d)
            if u*u == c**13-d:
                hits.append((x,u,c))
    return hits


def roots_table(q):
    roots = [0]*q
    for y in range(q):
        roots[y*y % q] += 1
    return roots


def split_test(q, classes, with_traces):
    """Enumerate the two thirteenth powers first and recover U by interpolation."""
    d, p = 263, 13
    r = next(i for i in range(1,q) if (i*i+d) % q == 0)
    powers = {pow(v,p,q) for v in range(q)}
    half = pow(2,-1,q)
    eta = [(141+sgn*7*r)*half % q for sgn in (1,-1)]
    roots = roots_table(q)
    retained = {}
    for t,k in classes:
        ar = r*pow(d,t,q) % q
        left = {v*pow(eta[0],-k,q) % q for v in powers}
        right = {v*pow(eta[1],-k,q) % q for v in powers}
        us = [(v-ar) % q for v in left if (v-2*ar) % q in right]
        if not us:
            continue
        if not with_traces:
            retained[t,k] = None
            continue
        traces = set()
        big_d = pow(d,2*t+1,q)
        for u in us:
            w = (u*u+big_d) % q
            if w:
                a = q-sum(roots[x*(x*x+2*u*x+w) % q] for x in range(q))
            else:
                a = (q+1)*(roots[2*u % q]-1)
            traces.add(a % p)
        if roots[d % q] == 0:
            traces |= {-a % p for a in traces}
        retained[t,k] = traces
    return retained


def main():
    reduced = [(a,b) for a in range(1,isqrt(263//3)+1) for b in range(-a,a+1)
               if (b*b+263) % (4*a) == 0 and (c := (b*b+263)//(4*a)) >= a
               and not (b<0 and (abs(b)==a or a==c))]
    print("class number", len(reduced), "norm eta", (141**2+263*7**2)//4)
    print("bounded solutions", bounded_search())
    all_classes = set(product(range(13),repeat=2))
    live = all_classes.copy()
    for q in (157,313,521):
        sets = split_test(q,all_classes,True)
        roots = roots_table(q)
        trace = q-sum(roots[(x**3-x) % q] for x in range(q))
        live = {c for c in live if trace % 13 in sets.get(c,set())}
        print(q, "CM trace", trace, "mod 13", trace % 13,
              "max signed set size", max(map(len,sets.values())), "survivors",len(live))
    qs = [q for q in range(14,6000,13) if prime(q) and pow(-263,(q-1)//2,q)==1]
    live = all_classes.copy()
    for q in qs:
        live = set(split_test(q,live,False))
    print("split primes", len(qs), "descent survivors", len(live))


if __name__ == "__main__":
    main()
