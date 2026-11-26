# Independent checks for docs/audit.md, written without reference to the other scripts.
# Run: python3 scripts/audit_skeleton.py  (standard library only, about a minute)
from math import gcd, isqrt
def h(D):  # class number of discriminant -D (D>0, -D fundamental), reduced forms
    n=0
    for a in range(1, isqrt(D//3)+2):
        for b in range(-a+1, a+1):
            if (b*b+D)%(4*a): continue
            c=(b*b+D)//(4*a)
            if c<a: continue
            if a==c and b<0: continue
            if gcd(gcd(a,abs(b)),c)!=1: continue
            n+=1
    return n
for d, expected_h, expected_factors in (
    (167, 11, [167]), (263, 13, [263]), (2471, 62, [7, 353]),
):
    class_number = h(d)
    factors = [p for p in range(2,d+1) if d%p==0 and all(p%q for q in range(2,isqrt(p)+1))]
    print(d, "mod16", d%16, "h", class_number, "factor", factors)
    if (d % 16, class_number, factors) != (7, expected_h, expected_factors):
        raise AssertionError(f"unexpected discriminant data for {d}")
# 16-adic and 8-adic parity claims, exhaustively over residues
ok1=all((pow(7,x,16)+pow(b,4,16))%16==8 for x in (1,3,5,7) for b in range(1,16,2))
ok2=all((7+pow(b,4,8))%8==7 for b in range(0,8,2))
sq8={(c*c)%8 for c in range(1,8,2)}
print("odd b gives 8 mod 16:",ok1,"| even b gives 7 mod 8:",ok2,"| odd squares mod 8:",sq8)
if not (ok1 and ok2 and sq8 == {1}):
    raise AssertionError("parity check failed")

# brute-force: d^x + b^4 = perfect power with exponent >=3, gcd(b,d)=1
def integer_nth_root(n, z):
    """Return the integer r with r**z <= n < (r+1)**z for n >= 0 and z >= 1."""
    upper = 1 << ((n.bit_length() + z - 1) // z)
    lower = upper // 2
    # The bit length gives lower**z <= n < upper**z. Bisection preserves it.
    while upper - lower > 1:
        middle = (lower + upper) // 2
        if middle**z <= n:
            lower = middle
        else:
            upper = middle
    return lower


def is_pow(n):
    # For c >= 2, c**z = n implies z < n.bit_length().
    for z in range(3, n.bit_length()):
        c = integer_nth_root(n, z)
        if c**z == n:
            return (c, z)
    return None


# The largest cube within the search height is (2471**4)**3.
control_root = 2471**4
control = control_root**3
if is_pow(control) != (control_root, 3):
    raise AssertionError("missed the control cube")
if is_pow(control - 1) is not None or is_pow(control + 1) is not None:
    raise AssertionError("a neighbor of the control cube was reported as a power")

hits=[]
tested = 0
for d in (167,263,2471):
    for x in range(1,13):
        for b in range(1,3000):
            if gcd(b,d)!=1: continue
            tested += 1
            r=is_pow(d**x+b**4)
            if r: hits.append((d,x,b,r))
print("small solutions (x>=1, b<3000, x<=12):",hits)
# The three bases admit 2982, 2988 and 2564 choices of b for each of the 12 exponents.
if tested != 102408 or hits:
    raise AssertionError(f"expected 102408 coprime triples and no hits, got {tested} and {len(hits)}")
