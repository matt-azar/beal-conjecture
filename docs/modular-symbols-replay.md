# A dependency-free modular-symbol replay of the two Hecke exclusions

This is a third realization of the Hecke calculations at levels 79072 and 5344. It computes classical Manin symbols over $\mathbb F_p$ directly with C++ and OpenMP. At 79072 it reaches the exclusion **without the trace at 683**. The decisive prime is 311. The only input from the descent is $x\equiv5\pmod{62}$. [Brandt calculation](brandt-sieve.md) · [Frey curve](frey-curve.md) · [Level 5344](frey-167.md)

| Level, residual prime | Space | Trace conditions used | Common kernel |
|---|---|---|---:|
| 79072, 31 | Full relative symbols, both signs, dimension 22657 | $T_3,T_5,T_{11},T_{13},T_{19},T_{311}$ | 0 |
| 5344, 11 | Full relative symbols, both signs, dimension 1345 | $T_3,T_5$ | 0 |

The spaces contain every oldform and the Eisenstein part. No newform decomposition, Atkin–Lehner sign or new subspace enters.

## The space

Let $S=\left(\begin{smallmatrix}0&-1\\1&0\end{smallmatrix}\right)$ and $R=\left(\begin{smallmatrix}0&-1\\1&-1\end{smallmatrix}\right)$ act on the right of $\mathbb P^1(\mathbb Z/N)$. The program works in the dual of Manin's presentation,
$$
M^*=\{\varphi:\mathbb P^1(\mathbb Z/N)\to\mathbb F_p\ :\ \varphi(xS)=-\varphi(x),\ \varphi(x)+\varphi(xR)+\varphi(xR^2)=0\}.
$$
Both levels have no elliptic points, so $S$ and $R$ act freely. The program checks this. The $R$-orbits are then the vertices and the $S$-orbits the edges of a connected trivalent graph, and $M^*$ is its space of circulations. A breadth-first spanning tree gives free coordinates, one for each non-tree edge. The dimension $E-V+1$ equals $2g+c-1$, which is 22657 at level 79072 ($g=11313$, $c=32$). For a prime $\ell\nmid N$ the operator is the transpose of the Heilbronn–Cremona formula,
$$
(T_\ell\varphi)(x)=\sum_h\varphi(xh).
$$
Every eigensystem modulo $\lambda\mid p$ of a weight-two cusp form of level $N$ occurs in $M^*$. Integrating a normalized eigenform along relative modular symbols gives a nonzero Hecke eigenfunctional in characteristic zero. The Manin relations and simultaneous Hecke eigenvalue equations have coefficients in its number field, so their common kernel contains a nonzero vector over that field. Scale the coordinates at the chosen prime until they are integral with at least one unit, then reduce. This gives the required eigenfunctional over the residue field. Cremona gives the integration pairing and the Heilbronn matrices. [Chapter II, §§2.1 and 2.4](https://johncremona.github.io/book/fulltext/chapter2.pdf)

## The test

For a good prime $\ell$ let $S_\ell\subset\mathbb F_p$ be the set of residues of $a_\ell(f)$ allowed by some local solution. Good reduction contributes the trace of $Y^2=X^3+2b^2X^2+(b^4+d^x)X$. A zero of $b^4+d^x$ contributes $(2/\ell)(\ell+1)$. Only residues with $b^4+d^x$ a $p$th power modulo $\ell$ are kept, which is restrictive exactly when $\ell\equiv1\pmod p$. A newform arising from a solution gives a nonzero vector in
$$
\bigcap_\ell\ker\prod_{a\in S_\ell}(T_\ell-a).
$$
The program computes the first kernel by Gauss–Jordan elimination on the full matrix and cuts it down with each further operator.

| $\ell$ at 79072 | $S_\ell\subset\mathbb F_{31}$ | Kernel dimension after this prime |
|---:|---|---:|
| 3 | 0, 27 | 180 |
| 5 | 2, 29 | 80 |
| 11 | 0, 4, 19, 27 | 42 |
| 13 | 2, 25, 29 | 34 |
| 19 | 0, 2, 4, 6, 23, 27 | 22 |
| 311 | 7, 12, 22, 28, 29, 30 | 0 |

The 22-dimensional space survives the sets at every further prime below 200 that has at most 20 allowed residues. On it the operators at small primes have small even integer eigenvalues, as oldforms from elliptic curves with a rational point of order 2 would. The systems were not identified further. The Frey curve has such a point, so at a large prime with $\ell\not\equiv1\pmod{31}$ nearly every even trace is allowed. The prime $311=10\cdot31+1$ admits only six residues and none occurs.

At 5344 the sets are $S_3=\{0,7\}$ and $S_5=\{0,2,4,7\}$ in $\mathbb F_{11}$, for $x\equiv1\pmod{22}$. The kernel at 3 has dimension 50, and $T_5$ has eigenvalues $1,3,6,8,9,10$ on it.

## Checks

- At levels 11, 14 and 15 the program returns the known eigenvalues, including $U_q$ at primes dividing the level.
- At level 79072 the trace list of the curve $Y^2=X^3+37X+114$ at $3,5,11,13,17,19,23,311$ leaves a common kernel of dimension exactly 2, one for each sign.
- When building the initial matrix, the program checks input and output circulations at every 4,099th basis column, starting with column zero. For each subsequent Hecke action on a retained subspace it checks the circulation condition on the first three basis images (or all if fewer) and tests the free coordinates of every basis image for membership in that subspace.
- The set $S_{311}$ was recomputed by direct point counting over all residues.

## Reproduction

The implementation uses AVX2 intrinsics. The commands below require an AVX2-capable x86 machine and a C++17 compiler with OpenMP support. The run takes about ten minutes on two cores and about 1 GB of memory. [Program](../scripts/check_modsym_hecke.cpp) · [Trace sets](../scripts/frey_trace_sets.py)

```sh
export OMP_NUM_THREADS=2
g++ -O3 -march=native -fopenmp -std=c++17 scripts/check_modsym_hecke.cpp -o /tmp/ms31
g++ -O3 -march=native -fopenmp -std=c++17 -DPMOD=11 scripts/check_modsym_hecke.cpp -o /tmp/ms11
/tmp/ms31 11 eig 2 3 5 7 13
python3 scripts/frey_trace_sets.py 167 11 1 22 3 5 > /tmp/f167.txt
/tmp/ms11 5344 big /tmp/f167.txt /tmp/V167.bin && /tmp/ms11 5344 run /tmp/V167.bin /tmp/f167.txt
python3 scripts/frey_trace_sets.py 2471 31 5 62 3 5 11 13 19 311 > /tmp/f2471.txt
/tmp/ms31 79072 big /tmp/f2471.txt /tmp/V2471.bin && /tmp/ms31 79072 run /tmp/V2471.bin /tmp/f2471.txt
printf "3 0\n5 30\n11 1\n13 1\n17 26\n19 0\n23 29\n311 24\n" > /tmp/fEa.txt
/tmp/ms31 79072 run /tmp/V2471.bin /tmp/fEa.txt
```

Both `run` commands for the Frey sets end with `FINAL dim 0`. The last command ends with `FINAL dim 2`.

The program has not been compared entry by entry with eclib or the Brandt matrices. Agreement is at the level of the conclusions and the positive controls.
