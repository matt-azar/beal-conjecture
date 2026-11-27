# An arbitrary square summand at base 2471 and right exponent 31

**Claim.** There are no positive integers $x,U,c$ with $\gcd(U,2471)=1$ and
$$
2471^x+U^2=c^{31}.
$$
Consequently $2471^x+B^y=C^z$ has no positive primitive solution whenever $y$ is even and $31\mid z$. This includes the sixth-power target $2471^x+B^6=C^{31}$ and removes the condition $4\mid y$ at this right exponent. It is the analogue at 2471 of the [arbitrary-square result at 167](frey-167.md#an-arbitrary-square-summand-at-exponent-11).

**Status.** Derived and computed by the lead on 2026-11-26. Astra reviewed the proof and the computation the same day, found no gap, and corrected four numerical statements in this note. [Review](square-summand-2471-review.md) A separate eclib program rebuilds the space and all fourteen Hecke matrices and reaches the same result. [eclib replay](replays/square-2471-eclib.md) The lead has not run the eclib program, having no eclib installation, and checked only that its dimensions and class counts match. No specialist has reviewed the claim, and it remains a claim.

Write $d=2471=7\cdot353$, $s^2=-d$, $K=\mathbb Q(s)$, $R=\mathbb Z[(1+s)/2]$. The class group of $K$ has order 62, so it is cyclic, and a prime $P$ above 2 has class of order 31 with $P^{31}=(\eta)$, $\eta=(90621+391s)/2$. [Class group and $\eta$](descent.md#from-an-integer-solution-to-a-twist)

## The four cases

**1. $x$ even.** Put $V=d^{x/2}$, so $U^2+V^2=c^{31}$ with $\gcd(U,V)=1$ and $V$ odd. If $U$ were odd the sum would be $2\pmod4$. So $U$ is even and $c$ is odd. In $\mathbb Z[i]$ the factors $U\pm iV$ are coprime, and every unit is a 31st power, so $U+iV=\alpha^{31}$ with $\alpha=u+iv$. Then $(\alpha,\bar\alpha)$ is a Lucas pair: $\alpha\bar\alpha=c$ is odd and prime to $2u$, and $\alpha/\bar\alpha$ is not a root of unity because $uv\neq0$ and $c\neq2$. Comparing imaginary parts gives $V=v\,L_{31}$ with $L_{31}=(\alpha^{31}-\bar\alpha^{31})/(\alpha-\bar\alpha)$. By Bilu–Hanrot–Voutier $L_{31}$ has a primitive prime divisor $q$. It divides $V$, so $q\in\{7,353\}$. A primitive divisor of $L_n$ satisfies $q\equiv\pm1\pmod n$. Neither $7$ nor $353\equiv12$ is $\pm1\pmod{31}$. [Bilu–Hanrot–Voutier](https://doi.org/10.1515/crll.2001.080)

**2. $x$ odd, $c$ even.** Then $U$ is odd and $\delta=(U+d^{(x-1)/2}s)/2\in R$ has odd trace and norm $c^{31}/4$. Exactly one prime $Q$ above 2 divides $\delta$, to the power $31v_2(c)-2$. At odd primes the ideals $(\delta)$ and $(\bar\delta)$ are coprime, since a common prime would divide $U$ and $d$. Hence $(\delta)=Q^{31v_2(c)-2}J^{31}$ and $2[Q]=31[J]$ in the class group. The left side has order 31 and the right side has order at most 2. This forces $[Q]=0$, but $Q$ is not principal. This is the class relation recorded in the [research plan](research-plan.md#the-next-arithmetic-target).

**3. $x$ odd, $c$ odd, $31\mid x$.** Then $c^{31}+(-d^{x/31})^{31}=U^2$ is a non-trivial primitive solution of signature $(31,31,2)$, excluded by Darmon–Merel. [Darmon–Merel, Main Theorem](https://www.math.mcgill.ca/darmon/pub/Articles/Research/18.Merel/paper.pdf)

**4. $x$ odd, $c$ odd, $31\nmid x$.** This is the main case. $U$ is even. Put $t=(x-1)/2$, $a=d^t$.

*Descent.* The ideals $(U\pm as)$ are coprime and have product $(c)^{31}$, so $(U+as)=I^{31}$. There is a unique $k\in\{0,\dots,30\}$ with $IP^k=(\beta)$, and then
$$
\beta^{31}=\eta^k(U+as).
$$
If $k=0$ then $(\beta,\bar\beta)$ is a Lucas pair with $w\,L_{31}=2d^t$, where $\beta-\bar\beta=ws$. Odd primes of $L_{31}$ divide $d$, hence the discriminant $-dw^2$, and 2 divides $L_2$ or $L_3$. So $L_{31}$ has no primitive divisor, contradicting Bilu–Hanrot–Voutier. This is the argument of the [fixed-base proof](fixed-bases.md), which does not use that the square is a fourth power. The Hecke test below does not need this step, since it also eliminates $k=0$.

*Frey curve.* Let $E: Y^2=X^3+2UX^2+c^{31}X$, with $\Delta=-64\,d^xc^{62}$ and $c_4=16(U^2-3d^x)$. As $U$ is even, $c^{31}=U^2+d^x\equiv7$ or $11\pmod{16}$. Translating $X$ by 1 gives $a_4'=3+4U+c^{31}\equiv2\pmod4$ and $a_6'=(1+U)^2+d^x\equiv0\pmod8$, so $v_2(b_8')=2$, Tate type III and conductor exponent 5, exactly as for [the fourth-power curve](frey-curve.md#conductor-and-level). At odd $q\mid dc$ the reduction is multiplicative because $c_4$ is a unit. Since $31\nmid x$, level lowering gives a newform $f$ of exact level $2^5\cdot7\cdot353=79072$ and a prime $\lambda\mid31$ with, for every prime $\ell\nmid2\cdot31\cdot d$,
$$
a_\ell(f)\equiv a_\ell(E)\ \ (\ell\nmid c),\qquad a_\ell(f)\equiv\pm(\ell+1)\ \ (\ell\mid c),
$$
with sign $+$ exactly when $2U$ is a square modulo $\ell$. Irreducibility is Mazur's theorem at 31. Unlike the fourth-power case, the reduction type at 7 and 353 depends on $U$. The test below uses the full space at level 79072 and no Atkin–Lehner or $U_q$ information, so this does not matter.

*Classes.* The pair $(t\bmod31,\ k)$ is a global invariant of the solution, and $x\equiv2t+1\pmod{62}$. Raising $x$ by 62 multiplies $a$ by $d^{31}$. Local solutions then scale by $\lambda=d^{31}$, which is a 31st power, and $E$ is replaced by its quadratic twist by $\lambda$. So for each prime $\ell$ the set $S_\ell(t,k)\subset\mathbb F_{31}$ of residues that $a_\ell(f)$ can take is well defined:

- reduce the twist identity modulo $\ell$, at both roots of $s^2=-d$ with the same $U$ if $\ell$ splits, or in $\mathbb F_{\ell^2}$ if $\ell$ is inert;
- keep the $U\bmod\ell$ for which $\eta^k(U+as)$ is a 31st power (zero allowed);
- record the trace of each such $U$, and its negative as well when $d$ is a non-residue modulo $\ell$.

The condition is restrictive when $\ell$ splits with $\ell\equiv1\pmod{31}$ (about $\ell/961$ of the residues survive) or $\ell$ is inert with $\ell\equiv-1\pmod{31}$ (about $\ell/31$).

*Hecke test.* A solution in class $(t,k)$ gives a nonzero vector in the dual Manin-symbol space of level 79072 over $\overline{\mathbb F}_{31}$ killed by $\prod_{a\in S_\ell}(T_\ell-a)$ for every $\ell$, as in the [modular-symbol replay](modular-symbols-replay.md). The computation has two stages.

| Stage | Primes | Trace sets | Result |
|---|---|---|---|
| Class-independent | 3, then 25 primes from 5 to 227 | Union over all odd $x$ and all $U$. $S_3=\{0,\pm4\}$, $S_5=\{\pm2,6\}$, $S_{11}=\{0,\pm4,\pm12\}$, $S_{17}=\{0,\pm2,\pm4,\pm6,\pm8\}$ | Kernel of dimension 209 after 3, then 111, 73, 73, 42, and 42 after every later prime |
| Class-dependent | 61 (inert), 683 and 1117 (split) | $S_\ell(t,k)$, signed maxima 4, 6 and 7, respectively | Zero for all 961 pairs $(t,k)$ |

In the second stage 403 classes die at 61, a further 512 at 683 and the last 46 at 1117. The descent sieve alone, with modulus 961 and all 22 split primes congruent to 1 modulo 31 through 11719, leaves 81 of the 961 classes. The Hecke test was run on all 961 classes and does not depend on the sieve. The independent review lists the five simultaneous eigenvalue triples of the 42-dimensional space at these three primes. It is the analogue of the 22-dimensional space in the fourth-power replay.

## Checks

- **Operators.** The retained space contains the CM system of $y^2=x^3-x$ (level 32) with multiplicity 8, which is four degeneracy maps times two signs. On it each of the 14 dumped operators, including $T_{2543}$, acts by the trace obtained from an independent point count.
- **Signs.** Repeating both stages with both signs $\pm(\ell+1)$ allowed at every multiplicative prime gives the same dimensions and again zero for all 961 classes.
- **Trace code.** Restricting $U$ to squares reproduces the documented fourth-power sets $S_{19}$ and $S_{311}$ for $x\equiv5\pmod{62}$, and the descent sieve restricted to squares reproduces all four survivors $(5,23),(31,0),(67,8),(93,0)$ for $(x\bmod124,k)$. The lift to modulus 124 preserves the condition that $U$ is a square.
- **Class sets.** Enumerating every value of $a$ directly agrees with the orbit description on five sampled $(\ell,t,k)$.
- **Program.** At level 11 the modified program still returns the known eigenvalues. Each dumped operator passes the invariance test on all 22657 coordinates for every basis vector and the flow test on the first basis vector.

## Scope and verification

- The level-79072 operators now have two implementations for this claim: the Manin-symbol program with its `dump` mode, and the [eclib replay](replays/square-2471-eclib.md). The exclusion also relies on the published modularity and level-lowering results.
- The independent review gives the order argument for primitive divisors at index 31 and checks the published hypotheses in cases 1, 3 and 4.
- The reduction $a_\ell(f)\equiv a_\ell(E)(\ell+1)$ at $\ell\mid c$ is used with its sign in the main run. The sign-free run does not need it.
- Other right exponents are not treated. For $y$ even and $31\nmid z$ nothing is claimed.

## Reproduction

About ten minutes on two cores and 1 GB of memory, with an AVX2 machine and a C++17 compiler with OpenMP. The last command alone takes under a minute and uses the matrices stored in [`docs/replays/square-2471`](replays/square-2471).

```sh
export OMP_NUM_THREADS=2
g++ -O3 -march=native -fopenmp -std=c++17 scripts/check_modsym_hecke.cpp -o /tmp/ms31
python3 scripts/check_square_2471.py filters > /tmp/fsq.txt
/tmp/ms31 79072 big /tmp/fsq.txt /tmp/Vsq3.bin
MS_SAVE=/tmp/Vsq.bin /tmp/ms31 79072 run /tmp/Vsq3.bin /tmp/fsq.txt
/tmp/ms31 79072 dump /tmp/Vsq.bin /tmp/TV0 3 5 11 13 17 19 61 683 1117 1303 1489 1861 2357 2543
python3 scripts/check_square_2471.py verify /tmp/TV0
python3 scripts/check_square_2471.py verify
```

Expected: `kernel of filter at 3: dim 209`, `FINAL dim 42`, fourteen lines ending `invariance and flow checks passed`, and the verifier's last line `all 961 classes (x mod 62, k) have zero common kernel`. For the sign-free variant add `--unsigned` to the `filters` command.

The program change is one new mode, `dump`, which writes the matrix of $T_\ell$ on a saved Hecke-stable space without storing the Heilbronn tables, and an optional `MS_SAVE` to keep the space left by `run`. [Program](../scripts/check_modsym_hecke.cpp) · [Verifier](../scripts/check_square_2471.py)
