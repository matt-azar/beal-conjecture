# The fourth-power summand for base 263

**Result.** The equation $263^x+B^y=C^z$ has no primitive positive solution for $x,y,z\geq3$ and $4\mid y$. This note supplies the two inputs specific to 263. [Proof across all exponents](fixed-bases.md)

**Exponent 13.** For every positive odd $x$, there are no positive pairwise coprime bases satisfying $263^x+b^4=c^{13}$. The class number of $\mathbb Q(\sqrt{-263})$ is 13, so the principal-ideal argument for an exponent coprime to the class number would leave this case open. Trace at 3 alone eliminates level 8416. Trace at 5 eliminates level 32.

Write $D=263^x$ and take $E:Y^2=X(X^2+2b^2X+c^{13})$. Since $D\equiv7\pmod{16}$, the parity argument gives $b$ even and $c$ odd. The conductor calculation used for 167 gives multiplicative reduction at the odd primes dividing $Dc$, and conductor exponent 5 at 2. The minimal discriminant is $-64D c^{26}$. The rational point of order two and a hypothetical Galois-stable line in $E[13]$ would give a forbidden rational cyclic 26-isogeny. Thus level lowering supplies a weight-two newform of exact level $32\cdot263=8416$ for $13\nmid x$ and level 32 for $13\mid x$. [Local and level-lowering argument](frey-167.md#conductor-and-irreducibility) · [Cyclic isogeny classification, Theorem 2.1.48](https://grantmolnar.com/pdfs/Counting_elliptic_curves_with_a_cyclic_m_isogeny_over_Q.pdf)

The following traces are taken at a single prime $\lambda$ over 13. At 3 we have $D\equiv2$, giving good trace 0 if $3\mid b$ and lowered multiplicative trace $-4$ otherwise. At 5, $D\equiv2$ or 3. The good traces are $0,4$ in the former case and $-4,2$ in the latter. In particular the unique level-32 newform with $a_5=-2$ is impossible. [Point counts at 3 and 5](frey-167.md#traces-and-simultaneous-exclusion)

At level 8416, the characteristic-zero plus cuspidal newspace has dimension 262. The matrix of $T_3$ in PARI's rational newspace basis has denominator 4. Modulo 13, $T_3(T_3+4)$ has rank 262. A common characteristic-zero eigenvector can be made integral at $\lambda$ with at least one unit coordinate. Its reduction would give a nonzero vector in this kernel, a contradiction. This proves the proposition. Run `gp -q -f scripts/check_transfer_263.gp` from the repository root. [PARI verifier](../scripts/check_transfer_263.gp)

## Check on a larger space

The full relative plus modular-symbol space has dimension 1,060. Here the 3 and 5 conditions leave a five-dimensional joint kernel, so one more prime is useful. At 7, $263\equiv4$ is a square and $-1$ is a nonsquare, so $D+b^4\ne0$ for every $b$. There is good reduction. Counting points in the good fibers gives the following ordinary traces.

| $D\bmod7$ | $b=0$ | $b=\pm1$ | $b=\pm2$ | $b=\pm3$ |
|---:|---:|---:|---:|---:|
| 1 | 0 | 4 | −2 | 2 |
| 2 | 0 | 2 | 4 | −2 |
| 4 | 0 | −2 | 2 | 4 |

Consequently a residual eigensymbol must lie in the common kernel of the three operators
$$
T_3(T_3+4),\qquad (T_5+4)T_5(T_5-2)(T_5-4),\qquad
(T_7+2)T_7(T_7-2)(T_7-4).
$$
On the full relative plus space the third condition gives zero joint kernel. The 262-dimensional newspace calculation above explains why the extra prime can be omitted when one works at exact level.

## The remaining cubic equation

Now take $z=3$. For odd $x$ and odd $c$, the [odd-norm cubic argument](right-exponent-three.md#odd-x-and-odd-c) applies unchanged because $263\equiv7\pmod{16}$, $3\nmid263$ and $3\nmid h(-263)$. For even $x$, use the [Gaussian argument for 167](right-exponent-three.md#even-x). It only needs a prime $d\equiv2\pmod3$ with $d\equiv7\pmod{16}$.

Suppose $x$ is odd and $c$ even. Set $s^2=-263$, $t=(x-1)/2$ and $\delta=(b^2+263^ts)/2$. The element $\eta=(141+7s)/2$ has odd trace and norm $2^{13}$, so $(\eta)=P^{13}$ for a prime $P$ above 2. The [oriented cubic proof](right-exponent-three.md#odd-x-and-even-c) yields $\beta^3=\eta_Q^2\delta$, with $\eta_Q=\eta$ or $\bar\eta$. At $P$ one has $s\equiv1\pmod4$. Taking both roots $\pm4$ modulo 9, the admissible residues of $b$ are empty at $x\equiv1,3,7,9\pmod{12}$ and equal to $\{4,5\}$ at $x\equiv5,11\pmod{12}$ for the representative exponents. [Local verifier](../scripts/check_cubic_twists.py)

Both remaining classes have $x=5+6j$, $j\geq0$. Set $X=c/263^{2j}$, $Y=b^2/263^{3j}$. These are affine coordinates on
$$
E:\quad Y^2=X^3-263^5.
$$
They are integral at every prime other than 263. The following obstruction excludes every such point.

## A denominator obstruction on the remaining Mordell curve

Every rational point on $E:Y^2=X^3-263^5$ reduces to the identity at the good prime $q=26723$. In particular every affine rational point has $v_q(X)<0$. This rules out $X=c/263^{2j}$ for any integers $c$ and $j\geq0$.

PARI/GP 2.17.2 gives lower and upper Mordell–Weil rank bounds both equal to one and trivial rational torsion. The verifier certifies the number-field data in the very `ellrankinit` structure passed to `ellrank`. Its single cubic field has discriminant $-1867563$ and `bnfcertify` returns 1. The rank upper bound comes from descent. The following explicit point also gives the rank lower bound because the torsion is trivial. [PARI `ellrank`](https://pari.math.u-bordeaux.fr/dochtml/html/Elliptic_curves.html#ellrank) · [PARI `bnfcertify`](https://pari.math.u-bordeaux.fr/dochtml/html/General_number_fields.html#bnfcertify)

The search used `ellheegner` to find $P$. Its coordinates are checked directly in the replay.

Write $P=(a/t^2,b/t^3)$ in lowest terms. Its coordinates are reproduced here as exact integers.

```text
a = 133402841906728032413158874135959681634586
b = 11065419309148454640078300299083598074536290899383440509590667
t = 3484335007852755533
```

Write $P=nG$ for a generator $G$ of $E(\mathbb Q)$. We have $v_q(X(P))=-2$, so $P$ reduces to the identity. Also $\#E(\mathbb F_q)=26724=2^2\cdot3\cdot17\cdot131$. To prove that $n$ is coprime to this order, take each prime divisor $\ell$ and reduce $P$ at the auxiliary good prime $r$ in its row. Put $m_r=\#E(\mathbb F_r)$. If $\ell\mid n$, then $[m_r/\ell]P$ reduces to the identity, since it is $[m_r]((n/\ell)G)$. The computed values exclude this in each row.

| $\ell$ | $r$ | $m_r$ | $[m_r/\ell]P\bmod r$ |
|---:|---:|---:|---|
| 2 | 5 | 6 | $(2,0)$ |
| 3 | 5 | 6 | $(3,3)$ |
| 17 | 101 | 102 | $(73,99)$ |
| 131 | 1571 | 1572 | $(1439,851)$ |

Multiplication by $n$ on $E(\mathbb F_q)$ is therefore bijective. Since $nG$ reduces to the identity, so does $G$, and hence every multiple of $G$. This argument requires no bound on the unrestricted index $[E(\mathbb Q):\langle P\rangle]$. To reproduce the field certification, rank bounds, torsion, reduction and all four point multiples, run `gp -fq scripts/check_mordell_263.gp`. [Mordell verifier](../scripts/check_mordell_263.gp)
