# C3 survey protocol, first cohort

This is the predeclared computation for primitive $d^x+b^4=c^p$ with positive bases, odd $x\geq3$, and prime $p\geq5$ dividing $h(-d)$. Here $h(-d)$ means the ideal class number of $\mathbb Q(\sqrt{-d})$. The cutoff is a first cohort small enough for exact modular-symbol calculations. The unit of observation is a pair $(d,p)$. Record bases with no eligible $p$ as a separate category. The previously studied $d=167$ is a replication and must be labeled in any summary of success rates.

## Fixed inputs

Take **every** squarefree $d\equiv7\pmod{16}$ with $0<d\leq199$. In this cohort $-d$ is fundamental. The list in increasing discriminant magnitude is

```text
7, 23, 39, 55, 71, 87, 103, 119, 151, 167, 183, 199
```

Regenerate the list by testing every integer in the prescribed progression for divisibility by a square greater than one. Compute each class number by enumerating primitive reduced positive binary quadratic forms and cross-check with PARI/GP 2.17.2. List every prime divisor of the class number. Only primes $p\geq5$ enter the Hecke experiment. The $p\nmid h(-d)$ Lucas argument has its own defective-pair exceptions and lies outside this experiment. For $p\mid x$ record the independent signed $(p,p,2)$ deduction. For $p\nmid x$ test the exact level $N=32d$ predicted for an irreducible residual representation by the same conductor calculation as at 167. Document the irreducibility input for each residual prime separately. Report any missing input as a condition on the arithmetic interpretation. [Frey-curve derivation](frey-167.md) · [Darmon–Merel](https://www.math.mcgill.ca/darmon/pub/Articles/Research/18.Merel/paper.pdf)

The initial auxiliary primes, in order, are **3, 5, 7**. Skip a prime $q\mid 2dp$ and record the skip without substitution. Run the following rules for $r\in\{1,3,5,7,9,11\}$ modulo 12. These six classes preserve $d^x$ at each applied prime. All have positive lifts $x\geq3$ with $p\nmid x$. At $q$ enumerate $b\bmod q$, put $u=d^r+b^4$, and retain $u$ when it is a $p$th power, including zero. A nonzero $u$ gives the point-count trace for $Y^2=X(X^2+2b^2X+u)$. For $u=0$, primitivity ensures $b\ne0\pmod q$. Use the lowered multiplicative trace $(2/q)(q+1)$. Let $S_q$ be the resulting set of distinct residues modulo $p$. Keep the same $r$ throughout. Group rows only when all filters and outputs coincide.

## Outputs and controls

Use weight two, trivial character, the plus part of the cuspidal **new** modular-symbol space over $\mathbb Q$, and a full lattice stable at $p$. Work over $\mathbb F_p$. Verify that the chosen matrices are integral at $p$, using a saturated integral lattice when necessary. Start with the full space, then intersect successively with $\ker\prod_{a\in S_q}(T_q-aI)$. An empty set of allowed traces gives the zero space. Print the level, starting dimension and dimension after each prime, including early zeros and skipped primes. Save the raw results in the second PR. Run the level-11 positive control $a_3=-1,a_5=1$ over each residue field. Include a direct check of good and bad local traces against point counts and tangent signs.

A nonzero result is a surviving necessary condition. Report all surviving joint characters up to residue-field conjugacy, with their trace tuples and simultaneous eigenspace dimensions. A stable line identifies a character. If a tuple leaves several dimensions, apply further Hecke operators in ascending prime order, retaining **all** eigenvalues over the algebraic closure. These operators identify systems and never filter out a candidate. If multiplicities persist, use the weight-two Sturm bound and the Hecke recurrences, or explicitly report which systems still need identification. Any proposed additional arithmetic filter belongs to a separately recorded follow-up. Report exclusions, survivors, and failures for the entire cohort.
