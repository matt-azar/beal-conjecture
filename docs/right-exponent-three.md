# A cubic right side for the two fixed bases

**Theorem.** For $d=167$ or $2471$, the equation
$$
d^x+b^4=c^3
$$
has no positive primitive solution for any integer $x\ge 1$. Here $d,b,c$ are pairwise coprime. Consequently these bases are excluded in the Beal equation whenever $4\mid y$ and $3\mid z$, by replacing $b$ and $c$ by the corresponding powers of the original bases.

## Odd $x$ and even $c$

Write $t=(x-1)/2$, $a=d^t$, $s=\sqrt{-d}$, and $R=\mathbb Z[(1+s)/2]$. Then $b$ is odd and $d^x+b^4\equiv8\pmod {16}$, so $v_2(c)=1$. Define
$$
\delta=(b^2+as)/2\in R,\qquad N(\delta)=c^3/4.
$$
No odd prime ideal divides both $\delta$ and its conjugate. Such an ideal would divide $as$ and hence lie above a prime dividing both $d$ and $c$. Thus all odd prime ideal valuations of $(\delta)$ are divisible by three. The prime 2 splits, and $v_2(N(\delta))=1$, so exactly one prime $Q$ above 2 divides $\delta$, with valuation one. In particular $(\delta)=Q I^3$ for an integral ideal $I$.

The generators $\eta=(T+Hs)/2$ satisfy $(\eta)=P^p$ for one prime $P$ above 2. [Class numbers and generators](descent.md#from-an-integer-solution-to-a-twist)

| $d$ | $T$ | $H$ | $p$ | class number | $k$ |
|---:|---:|---:|---:|---:|---:|
| 167 | 3 | 7 | 11 | 11 | 1 |
| 2471 | 90621 | 391 | 31 | 62 | 2 |

Let $\eta_Q=\eta$ if $Q=P$ and $\bar\eta$ otherwise. Since $1+pk\equiv0\pmod3$, the ideal of $\eta_Q^k\delta$ is a cube. Both class numbers are coprime to 3 and both unit groups are $\{\pm1\}$. Hence an integral $\beta$ satisfies
$$
\beta^3=\eta_Q^k\delta.
$$

The orientation is determined by $x\bmod4$. In $R_P$ the image of $s\bmod4$ is $-T/H\bmod4$ since $T+Hs=2\eta$ is divisible by 4 there. This image is 3 for $d=167$ and 1 for $d=2471$. As $b^2\equiv1\pmod4$, one has $Q=P$ exactly when $1+a s\equiv0\pmod4$ in $R_P$.

Each table entry gives an odd modulus $m$ at which the cubic identity is impossible. Denote conjugation by a bar.

| $x\bmod12$ | 1 | 3 | 5 | 7 | 9 | 11 |
|---|---:|---:|---:|---:|---:|---:|
| $\eta_Q$ for 167 | $\eta$ | $\bar\eta$ | $\eta$ | $\bar\eta$ | $\eta$ | $\bar\eta$ |
| $m$ for 167 | 9 | 19 | 9 | 9 | 19 | 9 |
| $\eta_Q$ for 2471 | $\bar\eta$ | $\eta$ | $\bar\eta$ | $\eta$ | $\bar\eta$ | $\eta$ |
| $m$ for 2471 | 13 | 13 | 13 | 13 | 13 | 13 |

Evaluate $s$ at both $r,-r$ modulo $m$, using $r=2$ at 9 and 19, and $r=5$ at 13. For each $b\bmod m$, at least one image of $\eta_Q^k(b^2+as)/2$ falls outside the full set of cubes $\{j^3\bmod m:0\le j<m\}$. Increasing $x$ by 12 multiplies $a$ by $d^6$. Replacing $b$ by $d^3 b$ and $\beta$ by $d^2\beta$ gives an invertible change modulo each $m$, preserving the orientation. The enumeration therefore covers arbitrary odd $x$. Run `python3 scripts/check_cubic_twists.py` from the repository root. [Finite verifier](../scripts/check_cubic_twists.py)

Lean checks all twelve rows in `Beal.CubicTwists.no_local_cubes`. For either base, every representative $t=0,\ldots,5$ and every residue $b$ at its assigned modulus, the two reduced targets cannot both have cube roots. Each root is quantified separately. The ideal factorization, orientation rule and periodicity argument above connect this finite theorem to arbitrary integer solutions. [Lean certificate](../lean/CubicTwists.lean)

## Odd $x$ and odd $c$

Here $b$ is even. In the same ring the coprime conjugate factors $b^2\pm as$ have product $c^3$. Coprimality follows from $\gcd(c,2d)=1$. As above, the class and unit arguments give $b^2+as=(u+vs)^3$. The cube root has norm $c$ and its coordinates $u,v$ are integers. In the half-integral case its norm would be $(j^2+d k^2)/4$ with $j,k$ odd, which is even because $d\equiv7\pmod8$.

Taking imaginary parts gives $v(3u^2-dv^2)=d^t$. Thus $v$ is odd and $u$ is even by the norm. At every prime $q\mid d$, coprimality of $c=u^2+dv^2$ with $d$ gives $q\nmid u$. Since $3\nmid d$, the second factor is a unit at each such $q$. It follows that $v=\pm d^t$ and $3u^2-d^x=\pm1$. Modulo 16 the latter difference is 9 or 5, a contradiction.

## Even $x$

Set $a=d^{x/2}$. An odd $b$ gives $a^2+b^4\equiv2\pmod4$, impossible for a cube. Hence $b$ is even and $c$ odd. The Gaussian factors $b^2\pm ia$ are coprime since a common prime would divide $2a,2b^2$ and their odd norm. Unique factorization in $\mathbb Z[i]$, where every unit is a cube, yields
$$
b^2+ia=(u+iv)^3,\qquad v(3u^2-v^2)=a.
$$
The norm is $u^2+v^2=c$, so $v$ is odd and $u$ is even. Also $u\ne0$ by the real part. The coprimality of the conjugate factors implies $\gcd(u,v)=1$. The two factors of $a$ in this display are coprime, since their gcd divides 3 and $3\nmid a$.

For $d=2471$, the quadratic character of 3 at both 7 and 353 is $-1$. Thus neither prime can divide $3u^2-v^2$, since this would imply $3\equiv(v/u)^2$ in its residue field. The factor consequently equals $-1$ by reduction modulo 4. As $353\mid v$, we get $3u^2\equiv-1\pmod{353}$, impossible because $-3$ is a quadratic nonresidue at primes congruent to 2 modulo 3.

For $d=167$, coprimality puts the whole prime power $a$ into one factor. If $|v|=a$, the same reduction modulo 4 gives $3u^2-v^2=-1$, and $-3$ is again a quadratic nonresidue at 167. Otherwise $|v|=1$. Since $u$ is nonzero and even, $3u^2-1>0$, forcing $v=1$ and $3u^2-1=a$. Modulo 16 the left side is 15 or 11, while every power of 167 is 1 or 7.
