# A modular proof for the base 167

**Theorem.** For every positive odd $x$, the equation $167^x+b^4=c^{11}$ has no positive primitive solution. Two small-prime trace calculations at 3 and 5 suffice. The argument includes $x=1$ and works independently of the quadratic descent.

Bennett and Siksek’s Theorem 4 already treats even exponents of 167 for every square summand and every right exponent at least three. For odd exponents their Theorem 1 assumes the prime is below 100, and their Theorem 12 requires the exponent of the right side to be coprime to the class number. Here that class number is 11. A survey lists 167 in connection with Zhu and Le, whose theorem specifies 163. The identity $7^2+167=6^3$ also rules out the unrestricted assertion about 167 printed in the survey. [Bennett–Siksek, Theorems 1, 4 and 12](https://wrap.warwick.ac.uk/id/eprint/171531/1/WRAP-Differences-between-perfect-powers-prime-power-gaps-22.pdf) · [Zhu–Le](https://doi.org/10.1016/j.jnt.2010.09.009) · [Survey, §3.2, item (vi)](https://www.kurims.kyoto-u.ac.jp/EMIS/journals/SMA/v15/p15_20.pdf)

## Conductor and irreducibility

Write $D=167^x$, so $D\equiv7\pmod{16}$. If $b$ were odd, the sum would be $8\pmod{16}$, impossible for an eleventh power. Hence $b$ is even, $c$ odd and $c^{11}\equiv7\pmod{16}$. Set
$$E:\quad Y^2=X(X^2+2b^2X+c^{11}).$$
Its discriminant is $-64D c^{22}$ and $c_4=16(b^4-3D)$. Primitivity implies that each odd $q\mid Dc$ is a multiplicative prime at which the given model is minimal. At 2 the valuation of the discriminant is 6. Translating $X$ by 1 gives $a'_4\equiv2\pmod4$, $a'_6\equiv0\pmod8$, $b'_8\equiv4\pmod8$. Tate's algorithm gives type III and conductor exponent 5. [Local invariant calculations](frey-curve.md#conductor-and-level)

The smooth curve has the rational point $(0,0)$ of order two. A Galois-stable line in $E[11]$ would combine with this point to give a Galois-stable cyclic subgroup of order 22. The classification of rational cyclic isogenies excludes degree 22, so $E[11]$ is irreducible. Weight-two level lowering removes the primes dividing $c$. At 167 the valuation of the minimal discriminant is $x$. The lowered newform has exact level 5344 if $11\nmid x$, or 32 if $11\mid x$. [Cyclic isogeny classification, Theorem 2.1.48](https://grantmolnar.com/pdfs/Counting_elliptic_curves_with_a_cyclic_m_isogeny_over_Q.pdf) · [Level lowering, §5.2, Theorem 3](https://samirsiksek.github.io/siksek.github.io/papers/ihpnotes7.pdf)

## Traces and simultaneous exclusion

At 3 we have $D\equiv2$. If $3\mid b$ the reduction is $Y^2=X^3-X$ with trace zero. Otherwise $3\mid c$, and the node at zero has tangent slopes $\pm b\sqrt2$. Nonsplit multiplicative reduction gives lowered trace $-(3+1)=-4\bmod\lambda$ for $\lambda\mid11$. At 5 we have $D\equiv2$ or 3, so $c^{11}\equiv D+b^4\ne0$ and the Frey curve is good. Counting points gives the ordinary traces below. [Multiplicative trace formula](auxiliary-traces.md#from-a-twist-to-a-trace)

| $D\bmod5$ | $5\mid b$ | $5\nmid b$ |
|---|---:|---:|
| 2 | 4 | 0 |
| 3 | −4 | 2 |

The unique level-32 newform has $a_5=-2$, incompatible with the four allowed residues. At level 5344 the plus part of the new cuspidal modular symbols has dimension 166 and contains each weight-two newform eigensystem. Use the rational basis returned by PARI's `msnew`. The matrices of $T_3,T_5$ have denominator 8, hence preserve the lattice spanned by this basis over $\mathbb Z_{(11)}$. On reduction modulo 11, $K=\ker(T_3(T_3+4))$ has dimension 3. The image of $K$ under $(T_5+4)T_5(T_5-2)(T_5-4)$ has dimension 3, so the joint kernel is zero. These ranks persist over any extension of $\mathbb F_{11}$. A candidate simultaneous eigenvector in characteristic zero can be scaled over its coefficient field localized at $\lambda$ to have integral coordinates with at least one unit. Its reduction would be a nonzero vector in this joint kernel. This contradiction proves the theorem. [PARI modular symbols](https://pari.math.u-bordeaux.fr/pub/pari/manuals/2.17.1/users.pdf) · [GP verifier](../scripts/check_new_5344.gp)

Run `gp -q -f scripts/check_new_5344.gp` from the repository root. The verifier computes the two newspaces and their Hecke matrices from scratch. It also checks the alternate trace at 89 below. It uses PARI/GP 2.17.2 and allows a stack of up to 1.2 GB.

## Varying the first summand

Let $D=167^n u^{11}$, with $n,u$ positive and
$$
 D\equiv7\pmod{16},\qquad D\equiv2\pmod3,\qquad D\equiv2\text{ or }3\pmod5.
$$
Then $D+b^4=c^{11}$ has no positive solution with $D,b,c$ pairwise coprime. The Frey model, conductor exponent at 2 and traces at 3 and 5 depend only on the displayed residues. At odd $q\mid u$ other than 167 the valuation of the minimal discriminant is $11v_q(u)$ and the prime disappears under level lowering. At 167 that valuation is $n+11v_{167}(u)$, so the same two levels cover all cases. In particular one may take any odd $n\ge1$ and $u=m^4$ with $\gcd(m,30)=1$.

## Cross-check using the quadratic descent

For odd $x\ge3$ the [descent](descent.md) gives $(x\bmod44,k)=(1,4)$ or $(23,7)$. Use $s^2=-167$, $\eta=(3+7s)/2$ and the prescribed $k$. At each $q\nmid 2\cdot167\cdot11$, test all $b$ and retain those for which $\eta^k(b^2+167^{(x_0-1)/2}s)$ is an eleventh power in the residue algebra. Here $x_0=1$ or 23 represents the branch. Replacing $x_0$ by $x_0+44j$ rescales $b$ by the local unit $167^{11j}$ and identifies the Frey models after rescaling $X,Y$ by $167^{22j},167^{33j}$. Good fibers give the point-count trace. The lowered multiplicative trace for a zero value of $b^4+167^{x_0}$ is $(2/q)(q+1)$. [Proof of the trace transfer](auxiliary-traces.md#from-a-twist-to-a-trace)

| $q$ | $a_q(f)\bmod\lambda$, $x\equiv1$ | $a_q(f)\bmod\lambda$, $x\equiv23$ |
|---:|---|---|
| 3 | −4, 0 | −4, 0 |
| 5 | 0, 4 | −4, 2 |
| 7 | −4, −3, 0 | −4, −3, 0 |
| 13 | −4, −2, 2, 4 | −5, −4, 0, 4 |
| 23 | 0, 2 | 0, 2 |
| 43 | −4, 2 | 3, 5 |
| 89 | −3 | −3 |
| 199 | 5 | 5 |
| 353 | 3 | 3 |
| 397 | −5 | −5 |

For example, at 89 the first branch permits only $b=\pm37$, the second only $b=\pm12$. Both fibers have good reduction and yield the same trace residue. Run `python3 scripts/check_aux_traces.py --base 167` to reproduce the table or append `--show-b 89` to check this example. At level 5344 the kernel of $T_{89}+3$ modulo 11 has dimension 2, and its intersection with $\ker(T_3(T_3+4))$ has dimension zero. The GP verifier checks this second exclusion in the same rational basis. [Local verifier](../scripts/check_aux_traces.py)

## An arbitrary square summand at exponent 11

**Theorem.** There is no solution of $167^x+U^2=c^{11}$ in positive integers with $x\geq1$ and $167\nmid U$. Thus at this right exponent the exclusion extends to every even $y$ in the Beal equation. If $x$ is even, apply Bennett–Siksek's Theorem 4 to the prime-power gap. If $11\mid x$, write $c^{11}+(-167^{x/11})^{11}=U^2$ and use Darmon–Merel. [Prime power gaps, Theorem 4](https://personal.math.ubc.ca/~bennett/BeSi-ANT-2023.pdf) · [Darmon–Merel, Main Theorem](https://www.math.mcgill.ca/darmon/pub/Articles/Research/18.Merel/paper.pdf)

Suppose $x$ is odd, $11\nmid x$, and write $t=(x-1)/2$. If $c$ is even then $U$ is odd. In $K=\mathbb Q(s)$, $s^2=-167$, the element $\delta=(U+167^t s)/2$ is integral with odd trace and norm $c^{11}/4$. The two primes above 2 cannot both divide $\delta$ since its trace is odd. At the one that does, say $Q$, the valuation is $11v_2(c)-2$. At odd primes the two conjugate ideals are coprime, so every other valuation is a multiple of 11. Hence $(\delta)=Q^9 I^{11}$. The class group has order 11 and $Q$ has order 11, by the norm-two obstruction. The class relation $9[Q]+11[I]=0$ is impossible. [Class-number and prime-ideal proof](descent.md#from-an-integer-solution-to-a-twist)

For odd $c$, $U$ is even. Put $D=167^x$ and use $E:Y^2=X(X^2+2UX+c^{11})$. The discriminant is $-64D c^{22}$. At 2, translating $X$ by 1 gives $a'_4=3+4U+c^{11}\equiv2\pmod4$ and $a'_6=(1+U)^2+D\equiv0\pmod8$. As above this gives $v_2(b'_8)=2$, type III and conductor exponent 5. The odd-prime calculation and the rational 2-torsion point are unchanged by this substitution, so the lowered level is exactly 5344.

An arbitrary $U$ expands the allowed traces. At 3 the good case gives 0 and the multiplicative case has tangent sign $(2U/3)$, giving $-4$ or $4$. At 5 all fibers are good. The ordinary traces for $D=2\pmod5$ lie in $\{-2,0,4\}$, and for $D=3\pmod5$ in $\{-4,0,2\}$. In the exact-level newspace modulo 11, $\ker(T_3(T_3-4)(T_3+4))$ has dimension 4. Applying the product of the three $T_5-a$ operators for either trace set to that kernel has rank 4. The intersections are zero. The same GP verifier replays the point counts and both ranks. [Exact calculation](../scripts/check_new_5344.gp)
