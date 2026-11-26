# The two Hecke conditions at level 79072

**Proposition.** No normalized weight-two newform of trivial character and exact level $N=79072=7\cdot32\cdot353$ admits a prime $\lambda\mid31$ of its coefficient field for which
$$
a_5(f)\equiv 2\text{ or }-2\pmod\lambda,\qquad a_{683}(f)\equiv-2\pmod\lambda.
$$
The computation below covers the entire space of forms new at 7, including oldforms at 2 and 353. Together with the descent and Frey-curve deductions, this excludes a primitive solution of $2471^x+b^4=c^{31}$ for odd $x\ge3$. [Descent](descent.md) · [Frey curve and required traces](frey-curve.md)

## Quaternionic realization

Use $B=(-1,-7)_{\mathbb Q}$, with generators $i^2=-1$, $j^2=-7$, $ji=-ij$. Put $w=(1+j)/2$ and take the order
$$
O=\mathbb Z+\mathbb Zi+\mathbb Zw+\mathbb Ziw.
$$
The relations $w^2=w-2$ and $wi=i-iw$ verify closure. The Gram matrix of $(x,y)\mapsto\operatorname{trd}(x\bar y)$ in this basis has diagonal $2,2,4,4$, with off-diagonal entries $1$ at the pairs $(1,3)$ and $(2,4)$, and determinant $49$. Thus the reduced discriminant of $O$ is 7. At 7, $\mathbb Q_7(i)$ is unramified quadratic, so $-7$ cannot be a norm because its valuation is odd. The algebra ramifies at 7. Since the algebra discriminant divides the reduced order discriminant with quotient the index in a maximal order, $B$ has finite discriminant 7 and $O$ is maximal. It is definite at infinity.

Write an element as $(a+bi+cj+dij)/2$. It belongs to $O$ precisely when $a\equiv c$ and $b\equiv d\pmod2$. Its norm is $(a^2+b^2+7c^2+7d^2)/4$. The units are $\{1,-1,i,-i\}$. The Eichler mass is $(7-1)/12=1/2$, already contributed by the principal class, whose projective unit group has order 2. This proves that $O$ has a single right ideal class. [Voight, *Quaternion Algebras*, Theorem 25.1.1](https://jvoight.github.io/quat-book.pdf)

Put $M=32\cdot353$. The class-number-one form of the definite Brandt model identifies the full weight-two quaternionic module at Eichler level $M$ with the functions on
$$
\Gamma\backslash X,\qquad \Gamma=O^\times/\{\pm1\},\quad
X=\mathbb P^1(\mathbb Z/32)\times\mathbb P^1(\mathbb F_{353}).
$$
The projective lines consist of primitive column vectors modulo unit scaling. The group $\Gamma$ acts on the left. For a prime $q\nmid7M$, choose one element $\alpha$ of norm $q$ in each orbit under left multiplication by $O^\times$. There are $q+1$ representatives. On function values the operator is
$$
(T_q F)(x)=\sum_{\alpha}F(\alpha x).
$$
The class-number-one projective-line construction and the corresponding formula on the free vector space on the orbits are in Dembélé–Voight, §4, immediately before Example 4.6. The function convention gives its transpose. Here all $\Gamma$-orbits have the same size, since $i$ has no projective fixed point modulo 32 (a fixed line would yield a square root of $-1$ modulo 4). Conjugating each norm-$q$ element reverses its projective action since $\bar\alpha\alpha=q$. Counting the directed edges between two equal-sized orbits over all norm-$q$ elements and dividing out the common multiplicities gives a symmetric matrix. The program also checks symmetry in each of the four bases below. By the weight-two Eichler–Shimizu–Jacquet–Langlands correspondence the cuspidal part includes every newform of exact level $7M$. [Dembélé–Voight, Theorem 3.9 and §4](https://jvoight.github.io/articles/hmf-crm-bcn-053024.pdf)

## Building the matrices

Both local maps send $i$ to $\left(\begin{smallmatrix}0&-1\\1&0\end{smallmatrix}\right)$. The images of $w$ are
$$
w_{32}=\begin{pmatrix}6&0\\0&-5\end{pmatrix},\qquad
w_{353}=\begin{pmatrix}1&46\\46&0\end{pmatrix}.
$$
The program checks the defining relations and that the images of $1,i,w,iw$ form a basis over each ring. It enumerates the solutions to $a^2+b^2+7c^2+7d^2=4q$ with the two parity conditions, retaining the lexicographically first of the four unit multiples. Each local matrix acts on columns using the chart $(t,1)$ when the second coordinate is a unit, and $(1,t)$ with $t$ a nonunit otherwise. These charts give 48 and 354 lines respectively.

Two commuting involutions divide the linear algebra into smaller blocks.

* Left multiplication by $j$ induces an involution $J$ on $X$ since $j^2=-7$ is a unit scalar at both factors. Conjugation by $j$ preserves $O$, its units and norms. Consequently $J$ preserves $\Gamma$-invariant functions and commutes with every $T_q$ used here.
* Let $S$ interchange the two lifts of each element of $\mathbb P^1(\mathbb Z/16)$ to $\mathbb P^1(\mathbb Z/32)$, holding the coordinate at 353 fixed. Every invertible matrix modulo 32 respects reduction, so it commutes with $S$. In either chart $S$ replaces $t$ with $t+16$.

The program verifies that multiplication by $i$, $J$, and $S$ give commuting involutions and that every orbit of the three has eight points. A function in the $(\epsilon_J,\epsilon_S)$ block is invariant under $i$ and changes by the indicated sign under $J$ and $S$. Its values at one representative of each orbit form free coordinates. Each block has $48\cdot354/8=2124$ coordinates. All four sign choices are used. Since 2 is invertible modulo 31, their direct sum contains every $\Gamma$-invariant function, including after scalar extension. This avoids any need to identify Atkin–Lehner signs or construct the 2-new subspace.

## A determinant certificate

Set $H=T_5^2+T_{683}-2I$. At a common eigenvector with either required pair of traces modulo 31, $H$ acts by $4-2-2=0$. The four determinants in the indicated bases give the following certificate.

| $(J,S)$ | $(-1,-1)$ | $(-1,+1)$ | $(+1,-1)$ | $(+1,+1)$ |
|---|---:|---:|---:|---:|
| $\det(H)\bmod31$ | 11 | 28 | 6 | 26 |

Their product is **29 modulo 31**. Hence $H$ is invertible on the full Brandt module modulo 31, including over any extension of that field. The verifier builds $H$ from the two integer matrices before computing each determinant. Equivalently, any putative newform would give $H$ the algebraic-integer eigenvalue $a_5(f)^2+a_{683}(f)-2$ divisible by $\lambda$. Reducing its monic characteristic-polynomial identity at $\lambda$ would force $\det H=0\pmod{31}$.

## Exact ranks modulo 31

The table gives $\dim\ker(T_5-a)$, followed by the rank of $T_{683}+2$ restricted to that kernel. Equal numbers give a zero simultaneous kernel.

| $J$ | $S$ | $a=-2$ dimension | $a=-2$ rank | $a=2$ dimension | $a=2$ rank |
|---:|---:|---:|---:|---:|---:|
| $-1$ | $-1$ | 2 | 2 | 5 | 5 |
| $+1$ | $-1$ | 2 | 2 | 5 | 5 |
| $-1$ | $+1$ | 1 | 1 | 7 | 7 |
| $+1$ | $+1$ | 2 | 2 | 14 | 14 |

For each $a$, the columns of $V$ form the right nullspace of $T_5-a$ computed with FLINT over $\mathbb F_{31}$. The verifier checks $(T_5-a)V=0$ and that $T_{683}V$ belongs to the same eigenspace. It computes the rank of $(T_{683}+2)V$ over the same field. As positive controls, the two known exact-level elliptic curves have trace pairs $(-1,-4)$ and $(-1,4)$. The program recovers a one-dimensional common eigenspace for the former in the $(-1,-1)$ block and for the latter in the $(+1,-1)$ block. It also checks that the constant function has eigenvalue $q+1$ for each operator. [Elliptic curves and point counts](frey-curve.md)

To see why this excludes coefficient fields of every degree, suppose a newform met both conditions. The Brandt realization gives a common eigenvector for the two integer matrices over a number field containing the two eigenvalues. Equivalently the stacked system for $T_5-a_5(f)$ and $T_{683}-a_{683}(f)$ already has a nonzero solution over the coefficient field, since its rank is invariant under field extension. Scale this vector over the discrete valuation ring at $\lambda$ until all coordinates are integral and some coordinate is a unit. Its reduction is a nonzero common eigenvector over the residue field at $\lambda$. Ranks over $\mathbb F_{31}$ stay unchanged after extension to that field. The determinant certificate already excludes this vector. The independent kernel and rank calculations give the same conclusion for each trace pair individually.

## Reproduction

From the repository root, run the commands below in a Python environment. The verifier was run with Python 3.12.14, NumPy 2.3.5, and python-flint 0.9.0. It builds both matrices directly from the norm equations and uses deterministic exact finite-field linear algebra. [Verifier](../scripts/check_brandt.py)

```sh
python3 -m pip install numpy==2.3.5 python-flint==0.9.0
python3 scripts/check_brandt.py
```

Classical modular symbols independently verify both joint exclusions on the full 11336-dimensional plus space. The published correspondence and the exact matrix calculations are mathematical inputs outside the current Lean developments. [Independent eclib replay](../scripts/check_eclib_hecke.cpp) · [Dependency-free replay without the trace at 683](modular-symbols-replay.md)
