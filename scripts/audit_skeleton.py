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
for d in (167,263,2471):
    print(d, "mod16", d%16, "h", h(d), "factor", [p for p in range(2,d+1) if d%p==0 and all(p%q for q in range(2,isqrt(p)+1))])
# 16-adic and 8-adic parity claims, exhaustively over residues
ok1=all((pow(7,x,16)+pow(b,4,16))%16==8 for x in (1,3,5,7) for b in range(1,16,2))
ok2=all((7+pow(b,4,8))%8==7 for b in range(0,8,2))
sq8={(c*c)%8 for c in range(1,8,2)}
print("odd b gives 8 mod 16:",ok1,"| even b gives 7 mod 8:",ok2,"| odd squares mod 8:",sq8)
# brute-force: d^x + b^4 = perfect power with exponent >=3, gcd(b,d)=1
def is_pow(n):
    for z in range(3, n.bit_length()+1):
        r=round(n**(1.0/z))
        for c in (r-1,r,r+1):
            if c>1 and c**z==n: return (c,z)
    return None
hits=[]
for d in (167,263,2471):
    for x in range(1,13):
        for b in range(1,3000):
            if gcd(b,d)!=1: continue
            r=is_pow(d**x+b**4)
            if r: hits.append((d,x,b,r))
print("small solutions (x>=1, b<3000, x<=12):",hits)
