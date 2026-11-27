# An arbitrary square summand at base 263 and right exponent 13

**Claim.** There are no positive integers $x,U,c$ with $263\nmid U$ and
$$
263^x+U^2=c^{13}.
$$
Consequently $263^x+B^y=C^z$ has no positive primitive solution whenever $y$ is even and $13\mid z$. With the results at [167 and exponent 11](frey-167.md#an-arbitrary-square-summand-at-exponent-11) and at [2471 and exponent 31](square-summand-2471.md), each of the three bases now has this statement at the prime dividing its class number.

**Status.** Derived and computed by the lead on 2026-11-26. Not yet reviewed by another agent, and the Hecke computation has one implementation. No specialist has seen it. Treat it as a claim.

The method is that of the [2471 note](square-summand-2471.md), which has the full argument. This note records what changes. Write $d=263$, $s^2=-d$, $K=\mathbb Q(s)$, $R=\mathbb Z[(1+s)/2]$. The class group of $K$ has order 13. No element of $R$ has norm 2, because $u^2+263v^2=8$ has no solution. So each prime $P$ above 2 has class of order 13, and $P^{13}=(\eta)$ for one of them with $\eta=(141+7s)/2$, of norm $2^{13}$ and odd trace.

## The four cases

**1. $x$ even.** Put $V=263^{x/2}$. As at 2471, $U$ is even, $c$ is odd, and $U+iV=\alpha^{13}$ in $\mathbb Z[i]$ with $(\alpha,\bar\alpha)$ a Lucas pair and $V=v\,L_{13}$. The only defective Lucas pair at index 13 lies in $\mathbb Q(\sqrt{-7})$, so $L_{13}$ has a primitive prime divisor $q$. It divides $V$, so $q=263$. Modulo a prime above $q$ the ratio $\alpha/\bar\alpha$ has order 13. Since $263\equiv3\pmod4$ is inert in $\mathbb Z[i]$, that order divides $q+1=264$, which 13 does not divide. This case is also contained in Bennett–Siksek's classification of $x^2+q^{2k}=y^n$ for primes $q<1000$. [Bilu–Hanrot–Voutier](https://doi.org/10.1515/crll.2001.080) · [Bennett–Siksek, Theorem 4](https://arxiv.org/abs/2110.05553)

**2. $x$ odd, $c$ even.** Then $U$ is odd and $\delta=(U+d^{(x-1)/2}s)/2$ has odd trace and norm $c^{13}/4$. Exactly one prime $Q$ above 2 divides it, to the power $13v_2(c)-2$, and all odd valuations of $(\delta)$ are multiples of 13. So $(\delta)=Q^{13v_2(c)-2}J^{13}$. In a class group of order 13 this gives $2[Q]=0$, hence $[Q]=0$, but $Q$ is not principal.

**3. $x$ odd, $c$ odd, $13\mid x$.** Then $c^{13}+(-263^{x/13})^{13}=U^2$ is a non-trivial primitive solution of signature $(13,13,2)$, excluded by Darmon–Merel. [Darmon–Merel, Main Theorem](https://www.math.mcgill.ca/darmon/pub/Articles/Research/18.Merel/paper.pdf)

**4. $x$ odd, $c$ odd, $13\nmid x$.** $U$ is even. With $t=(x-1)/2$ and $a=d^t$, the descent gives a unique $k\in\{0,\dots,12\}$ and $\beta\in R$ with
$$
\beta^{13}=\eta^k(U+as).
$$
The pair $(t\bmod13,\ k)$ is a global invariant, $x\equiv2t+1\pmod{26}$, and there are 169 classes.

The Frey curve $E:Y^2=X^3+2UX^2+c^{13}X$ has the same local analysis as before: conductor exponent 5 at 2, multiplicative reduction at $q\mid dc$. Mazur's theorem does not exclude a rational 13-isogeny. As in the [fourth-power proof at this base](transfer-263.md), the rational point of order 2 would turn one into a rational cyclic 26-isogeny, which does not exist. Since $13\nmid x$, level lowering gives a newform of exact level $2^5\cdot263=8416$ and a prime above 13 with the trace congruences of the 2471 note, for every prime $\ell\nmid2\cdot13\cdot263$.

*Hecke test.* The full dual Manin-symbol space at level 8416 over $\mathbb F_{13}$ has dimension 2113.

| Stage | Primes | Trace sets | Result |
|---|---|---|---|
| Class-independent | 3, 5, 7, 11, 17, 19, 23, 31, 37, 43, 61 | Union over all odd $x$ and all $U$. $S_3=\{0,\pm4\}$, $S_5=S_7=\{0,\pm2,\pm4\}$, $S_{11}=\{0,\pm1,\pm4\}$ | Kernel of dimension 39 after 3, then 14 after 5, then 4 after 7, and 4 after every later prime |
| Class-dependent | 157, 313, 521 (all split, all $1\bmod13$) | $S_\ell(t,k)$, with maxima 3, 2 and 7 residues over the 169 classes | Zero for all 169 pairs $(t,k)$ |

The 4-dimensional space is identified: it is the eigensystem of the level-32 CM curve $y^2=x^3-x$, with multiplicity 4 from two degeneracy maps and two signs. So after the first stage the only eigensystem left is that CM form modulo 13. Its traces at 157, 313 and 521 are $9$, $0$ and $4$ modulo 13, and a class is eliminated as soon as its set at one of these primes misses that value. This happens for 159 classes at 157, a further 8 at 313 and the last 2 at 521.

Local conditions alone do not suffice. At the 25 split primes below 6000 that are $1\bmod13$, 83 of the 169 classes have local solutions everywhere.

## Checks

- **Operators.** On the retained space each of the 11 dumped operators, including $T_{937}$, acts by the trace of $y^2=x^3-x$ obtained from an independent point count.
- **Signs.** Repeating both stages with both signs $\pm(\ell+1)$ allowed at every multiplicative prime gives the same dimensions 39, 14, 4 and again zero for all 169 classes, eliminated in the same numbers at the same primes.
- **Script.** The base-parametrized script reproduces the reviewed 2471 computation on the stored matrices: the same filter file, dimension 42, and 403, 512 and 46 classes eliminated at 61, 683 and 1117.
- **Class sets.** Enumerating every value of $a$ directly agrees with the orbit description on four sampled classes.
- **Program.** Compiled for the prime 13, the program returns the known eigenvalues of level 11.
- **Search.** There is no solution with $x<40$ and $U<20000$. This is a consistency check only.

## What has not been checked

- No second implementation of the level-8416 operators was run. The fourth-power proof at this base used PARI on the newspace, which is a different computation.
- The proof text has had no review. Case 1 at index 13 relies on the list of defective Lucas pairs, where index 13 is the one prime index at or above 11 with an exception.
- Nothing is claimed for right exponents not divisible by 13.

## Reproduction

Under a minute on two cores, with an AVX2 machine and a C++17 compiler with OpenMP. The last command alone needs only Python and uses the matrices stored in [`docs/replays/square-263`](replays/square-263).

```sh
export OMP_NUM_THREADS=2
g++ -O3 -march=native -fopenmp -std=c++17 -DPMOD=13 scripts/check_modsym_hecke.cpp -o /tmp/ms13
python3 scripts/check_square_class_test.py --base 263 filters > /tmp/f263.txt
/tmp/ms13 8416 big /tmp/f263.txt /tmp/W3.bin
MS_SAVE=/tmp/W0.bin /tmp/ms13 8416 run /tmp/W3.bin /tmp/f263.txt
/tmp/ms13 8416 dump /tmp/W0.bin /tmp/TW0 3 5 7 11 17 19 157 313 521 677 937
python3 scripts/check_square_class_test.py --base 263 verify /tmp/TW0
python3 scripts/check_square_class_test.py --base 263 verify
python3 scripts/check_square_class_test.py --base 263 sieve
```

Expected: `kernel of filter at 3: dim 39`, `FINAL dim 4`, eleven lines ending `invariance and flow checks passed`, the verifier's last line `all 169 classes (x mod 26, k) have zero common kernel`, and from the sieve `classes with local solutions at all: 83 of 169`. For the sign-free first stage add `--unsigned` to the `filters` command. [Script](../scripts/check_square_class_test.py) · [Program](../scripts/check_modsym_hecke.cpp)
