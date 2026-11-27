# Independent review of the arbitrary square at 263

PR #28 claims that $263^x+U^2=c^{13}$ has no positive integer solution with $263\nmid U$. I checked the proof at commit `129fd45` and found no mathematical gap. Each of the three auxiliary-prime eliminations reproduced independently. A single Hecke operator on the exact level already used in the project suffices for the hard branch.

## A single-prime test for the main case

Assume $x,c$ are odd and $13\nmid x$. The Frey curve is $E:Y^2=X^3+2UX^2+c^{13}X$. Level lowering gives a weight-two newform of **exact level** 8416. Since $263^x\equiv-1\pmod3$, the trace at 3 has only three possibilities.

- If $3\mid U$, then $c^{13}\equiv-1\pmod3$ and the good fiber is $Y^2=X^3-X$. All three affine values of $X$ give $Y=0$, so $a_3(E)=0$.
- Otherwise $3\mid c$. The reduction is multiplicative, and the lowered trace is $\pm(3+1)=\pm4\pmod{13}$. Both signs are allowed. [Siksek, Proposition 5.1](https://samirsiksek.github.io/siksek.github.io/papers/ihpnotes7.pdf)

On the 262-dimensional plus newspace of exact level 8416, PARI gives $T_3$ in a rational basis with denominator 4. Each of $T_3$, $T_3-4I$ and $T_3+4I$ has rank **262 modulo 13**. An independent calculation in the modular forms basis (its denominator is 8 modulo 13) gives determinants $3,10,10$ respectively. Their product is $1\pmod{13}$. A newform would give an eigenvector in its coefficient field. Scale the vector to be integral at the chosen prime above 13 with at least one unit coordinate. It would reduce to a nonzero vector in one of the three kernels, a contradiction. This removes the odd-$c$ twist descent and all auxiliary primes beyond 3. The even-$c$ argument still uses the class group. The CM curve in Claude’s larger computation has level 32, and its four copies there are consistent with this empty exact-level kernel.

The repository already had a certificate for $T_3(T_3+4I)$. Even that narrower certificate suffices: use $v=U$ or $-U$ as the coefficient in $2vX^2$, and choose $v\equiv1\pmod3$ in the multiplicative case. Then the tangent cone $Y^2=2vX^2$ is nonsplit and the lowered trace is $-4$. Both choices have the same conductor and minimal discriminant. [Earlier fourth-power certificate](../scripts/check_transfer_263.gp) · [Signed trace](frey-curve.md#the-second-trace-and-the-contradiction)

## Remaining proof checks

| Step | Independent check |
|---|---|
| Even $x$ | Bennett–Siksek, Theorem 4, classifies $U^2+q^{2k}=c^n$ for $q<1000$ prime, $q\nmid U$ and $n\ge3$. Its complete list omits 263. This also checks the result of the Gaussian Lucas argument: the defective pair at 13 lies in $\mathbb Q(\sqrt{-7})$, whereas a primitive divisor in the Gaussian argument would have to be 263, inert with $13\nmid264$. [Theorem 4](https://arxiv.org/pdf/2110.05553) |
| Odd $x$, even $c$ | There are 13 reduced forms of discriminant $-263$. The generator $(141+7\sqrt{-263})/2$ has odd trace and norm $2^{13}$. No element has norm 2. Each prime above 2 therefore has class of order 13. The odd trace of $\delta$ and its even norm force exactly one of the primes above 2 to divide it. Coprimality of the conjugate factors at odd primes follows from $263\nmid U$. The resulting relation $2[Q]=0$ contradicts the order of $[Q]$. |
| $13\mid x$ | The signed bases $c,-263^{x/13}$ give a nontrivial primitive solution to the signature $(13,13,2)$, contrary to Darmon–Merel. [Main Theorem, part 2](https://www.math.mcgill.ca/darmon/pub/Articles/Research/18.Merel/paper.pdf) |
| Frey conductor and irreducibility | For odd $x,c$, $U$ is even. The discriminant is $-64\cdot263^x c^{26}$. At 2 its valuation is 6. Translating $X$ by 1 gives $8\mid a'_6=(1+U)^2+263^x$ and $a'_4\equiv2\pmod4$. Thus $v_2(b'_8)=2$, type III and conductor exponent 5. At 263 and at primes of $c$, $c_4=16(U^2-3\cdot263^x)$ is a unit (at a prime of $c$ this is $64U^2$). The discriminant valuation is $x$ at 263 and $26v_q(c)$ at $q\mid c$. The level-lowering rule therefore retains 263 and removes the primes of $c$, including 13 if necessary. A rational 13-isogeny together with $(0,0)$ would give a Galois-stable cyclic subgroup of order 26, excluded over $\mathbb Q$. [Siksek, §5.2, Theorem 3](https://samirsiksek.github.io/siksek.github.io/papers/ihpnotes7.pdf) · [Cyclic degrees, Theorem 2.1.48](https://grantmolnar.com/pdfs/Counting_elliptic_curves_with_a_cyclic_m_isogeny_over_Q.pdf) |

## Check of the original proof

The odd-$c$ descent yields a single $k$ across all three primes. Increasing $x$ by 26 rescales $U$ and $263^{(x-1)/2}$ by the thirteenth power $263^{13}$ and twists the Frey curve by that factor. The admissible trace sets include both signs when its quadratic character is negative. Independently enumerating the two thirteenth powers in the split algebra and counting points gives the following results. The class counts include $13\mid x$ and $k=0$, as in the submitted computation.

| Prime | CM trace over the integers | Residue modulo 13 | Largest signed set | Remaining classes |
|---:|---:|---:|---:|---:|
| 157 | 22 | 9 | 3 | 10 |
| 313 | 26 | 0 | 2 | 2 |
| 521 | −22 | 4 | 7 | 0 |

All 507 signed sets agree class by class with PR #28. The independent eclib run starts from both sign spaces of dimensions 1060 and 1053. The generic filters reduce their direct sum to dimensions 39, 14 and 4 at 3, 5 and 7. All eleven computed operators agree with the saved matrices. The unsigned first-stage run reproduced the same space and final scalars. [C1 replay](https://github.com/matt-azar/beal-conjecture/pull/32)

Two qualifications to the write-up and CLI are worth retaining. The 83 local survivors pass reductions at the 25 tested split primes below 6000. Solubility at every completion, including lifts at those primes, requires further justification. Also, the advertised `verify --unsigned-space` flag is ignored. To check the unsigned first stage, generate the unsigned filters and pass the independently generated matrix prefix to the verifier. The C1 run did this. Neither point affects the exclusion.

The bounded search independently returned zero solutions for $1\le x<40$ and $1\le U<20000$. I also reran the parametrized 2471 verifier on the committed matrices and compared its signed filter file with its predecessor. All 961 classes were excluded and the files matched byte for byte. The 263 theorem still awaits external specialist review and end-to-end Lean formalization.

```sh
python scripts/review_square_263.py
gp -fq -s 192M scripts/check_square_263_newspace.gp
```
