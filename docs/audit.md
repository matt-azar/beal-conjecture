# Audit of the fixed-base theorem

This is the lead's independent audit of [the fourth-power theorem for three fixed bases](fixed-bases.md). It records what has been checked, how, and what has not. It is a first pass and covers only the elementary skeleton, whose source caveats are now closed. The three modular exclusions, the cubic cases and the Mordell-curve argument at 263 are **not yet audited**, and they carry most of the weight of the theorem.

Status values: **checked** (re-derived or recomputed independently), **caveat** (argument re-derived, but it rests on a source or a step not yet confirmed), **open** (not yet examined).

## Skeleton

| Step in the proof | Status | How |
|---|---|---|
| Case split on $z$: every $z\ge3$ is divisible by 3, by 4, or by a prime $p\ge5$. | checked | If $z$ has an odd prime factor it is 3 or at least 5. Otherwise $z=2^k$ with $k\ge2$. The proof treats $3\mid z$ first, then even $z\ge4$, then $p\mid z$, so the branches cover all $z$. |
| $d\equiv7\pmod{16}$ for $d=167,263,2471$. | checked | Direct. $2471=7\cdot353$, and 167, 263 are prime. |
| $x$ odd, $z\ge4$: $b$ is even and $C$ is odd. | checked | $d^x\equiv7$ and odd $b^4\equiv1\pmod{16}$ give $C^z\equiv8\pmod{16}$, impossible for $z\ge4$. Exhaustive over residues in `scripts/audit_skeleton.py`. |
| $x$ odd, $z$ even: no solution. | checked | $b$ even gives $C^z\equiv7\pmod8$, and odd squares are $1\pmod8$. |
| $x$ even, $z\ge4$: excluded by Bennett–Ellenberg–Ng, Theorem 1. | checked | The equation is $b^4+(d^{x/2})^2=C^z$ with coprime nonzero terms and exponent at least 4. The source check in PR #9 confirmed the statement, including its coprimality hypothesis, against Bennett's copy of the paper. |
| Class numbers 11, 13, 62. | checked | Independent count of reduced forms in `scripts/audit_skeleton.py`. Agrees with `check_twists.py` and with `IdealDescent.lean` for 167 and 2471. |
| $p\ge5$, $p\nmid h$: $b^2+d^{(x-1)/2}\sqrt{-d}=\alpha^p$. | checked | The two conjugate ideals are coprime because $C$ is odd and prime to $bd$. Their product is $(c)^p$, so each is a $p$th power of an ideal, principal since $p\nmid h$. The units are $\pm1$ and $p$ is odd. Note that $\alpha$ may have half-integral coordinates, since the ring of integers is $\mathbb Z[(1+\sqrt{-d})/2]$. The Lucas argument allows this. |
| $(\alpha,\bar\alpha)$ is a Lucas pair with no primitive divisor at index $p$. | checked | $\alpha\bar\alpha=c$ and $(\alpha+\bar\alpha)^2$ are coprime: a common prime divides $\alpha^p+\bar\alpha^p=2b^2$ and $c$, which are coprime. $\alpha/\bar\alpha$ is not a root of unity because the units are $\pm1$ and both coordinates of $\alpha^p$ are nonzero. Odd primes of $L_p$ divide $d$, hence the discriminant. The prime 2 divides $L_2$ or $L_3$. |
| No $p$-defective Lucas pair in these fields. | checked | The source check in PR #9 compared the list of fields for indices 5, 7 and 13 with Bilu–Hanrot–Voutier (Theorem C, Table 1) and with Bérczes–Luca–Pink–Ziegler (Proposition 2.2). The radicands $-167,-263,-2471$ are absent. The pair at index 13 is $(a,b)=(1,-7)$, whose thirteenth Lucas term is $-1$. An external summary read during the literature survey said no defective Lucas pair exists at 13. That summary is wrong and the proof's list is right. |
| Remaining pairs are exactly $(167,11)$, $(263,13)$, $(2471,31)$. | checked | The primes $p\ge5$ dividing 11, 13, 62. |
| No small solutions. | checked | Search over $x\le12$, $b<3000$, all exponents $z\ge3$ finds none. This is a consistency check only. |

## Replays run by the lead

| Command | Result |
|---|---|
| `python3 scripts/audit_skeleton.py` | Class numbers 11, 13, 62. Parity claims hold. No small solutions. |
| `python3 scripts/check_twists.py --exponents` | Matches the conventions table in the [collaborator guide](collaborating.md): surviving nonprincipal pairs $(1,4),(23,7)$ at 167 and $(5,23),(67,8)$ at 2471, with principal pairs at $x\equiv31,93\pmod{124}$. |
| `python3 scripts/check_cubic_twists.py` | Empty sets for 167 and 2471. At 263 the two surviving rows contain $b\in\{4,5\}$ modulo 9, as documented. |

The PARI/GP, eclib, Brandt and Lean replays were not run by the lead. Astra reproduced them from clean checkouts with pinned versions. [Clean replay](clean-replay.md)

## Not yet audited

| Item | What to check |
|---|---|
| Frey curve and conductor at each of the three pairs | The model $Y^2=X^3+2b^2X^2+(b^4+d^x)X$, its minimal discriminant, and the conductor exponent at 2 that gives level $32d$ after level lowering. For 2471 both primes 7 and 353 must be checked. |
| Irreducibility of the residual representation | For $p=11$ and $p=13$ a rational $p$-isogeny is not excluded by Mazur's theorem alone, since 11 and 13 are isogeny degrees. The proof uses the rational 2-torsion point to pass to degrees 22 and 26. Confirm that these, and 62, are absent from the Mazur–Kenku list, and that the 2-torsion point is rational for every solution. |
| Level lowering hypotheses | Ribet's theorem needs irreducibility and the correct Serre conductor. Check the primes of multiplicative reduction and that $p$ divides the relevant discriminant valuations. |
| Trace sets | That the admissible residues of $a_\ell$ cover every local solution, including multiplicative reduction with both signs. |
| The principal pairs at 2471 | The separate argument excluding $x\equiv31,93\pmod{124}$ with $k=0$. |
| The forced divisor $683\mid c$ | The step from the twist to the divisor, beyond what `Forced683.lean` assumes. |
| Cubic cases | The orientation at 2 and the period-12 reduction in [the cubic proof](right-exponent-three.md), and the even-$x$ Gaussian case. |
| Base 263 | The rank, torsion and index computation on $Y^2=X^3-263^5$ and the denominator argument in [the transfer note](transfer-263.md). |
| Identification of Hecke operators | That each of the three realizations (Brandt, eclib, Manin symbols) computes the operator the proof needs, at the same residual prime. |

## What is new

One row per claimed result. "Found in the literature" reports searches and source checks by the project, recorded in the [literature survey](literature-survey.md). A negative search is not proof of absence.

| Result | Closest published theorem | What it already gives | What appears to be new |
|---|---|---|---|
| $d^x+B^y=C^z$, $4\mid y$, $d\in\{167,263\}$ | Bennett–Siksek, [Theorems 1, 4 and 12](https://arxiv.org/abs/2110.05553) | Theorem 4 excludes every case with $x$ even, for any square. Theorem 12 treats odd right base with right exponent prime to the class number. | $x$ odd with right exponent 11 at 167 and 13 at 263, and the cubic cases. Theorem 1 stops at primes below 100. |
| The same at $d=2471$ | Bennett–Ellenberg–Ng, [Theorem 1](https://personal.math.ubc.ca/~bennett/BeElNgdraftFINAL.pdf) | $x$ even with $z\ge4$. The Bennett–Siksek theorems are for prime $q$ and do not apply to a composite base. | $x$ odd, and $3\mid z$. |
| $167^x+U^2=c^{11}$ | Bennett–Siksek Theorem 4. Freitas–Naskręcki–Stoll on $X^2+Y^3=Z^{11}$ | $x$ even. Under GRH, the case $x=3$. | $x$ odd in general. |
| $2471^x+U^2=c^{31}$ | None found | Nothing found. | The whole statement, pending review. [Note](square-summand-2471.md) |
| One summand a square forces a prime at least 13 in the other | Bennett–Siksek, [Theorem 2](https://doi.org/10.1090/tran/8734) | The complete list of 1,240 solutions. | Nothing. It is a corollary obtained by filtering their table. |
| Class-number obstruction for squarefree $A$ | Classical primitive-divisor arguments for $x^2+D=y^n$ | The method, for $y$ odd and exponent prime to the class number. | The packaging only. |

The method throughout is established: descent in an imaginary quadratic field, primitive divisors, and Frey curves with level lowering. The project makes no claim to a new technique.

## Later results

The [arbitrary-square result at 2471](square-summand-2471.md) is not covered by this audit. It was merged before review. Its own note lists the checks that were run and those that were not.
