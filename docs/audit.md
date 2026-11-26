# Audit of the fixed-base theorem

This is the lead's independent audit of [the fourth-power theorem for three fixed bases](fixed-bases.md). It records what has been checked, how, and what has not. It is a first pass and covers only the elementary skeleton. The three modular exclusions, the cubic cases and the Mordell-curve argument at 263 are **not yet audited**, and they carry most of the weight of the theorem.

Status values: **checked** (re-derived or recomputed independently), **caveat** (argument re-derived, but it rests on a source or a step not yet confirmed), **open** (not yet examined).

## Skeleton

| Step in the proof | Status | How |
|---|---|---|
| Case split on $z$: every $z\ge3$ is divisible by 3, by 4, or by a prime $p\ge5$. | checked | If $z$ has an odd prime factor it is 3 or at least 5. Otherwise $z=2^k$ with $k\ge2$. The proof treats $3\mid z$ first, then even $z\ge4$, then $p\mid z$, so the branches cover all $z$. |
| $d\equiv7\pmod{16}$ for $d=167,263,2471$. | checked | Direct. $2471=7\cdot353$, and 167, 263 are prime. |
| $x$ odd, $z\ge4$: $b$ is even and $C$ is odd. | checked | $d^x\equiv7$ and odd $b^4\equiv1\pmod{16}$ give $C^z\equiv8\pmod{16}$, impossible for $z\ge4$. Exhaustive over residues in `scripts/audit_skeleton.py`. |
| $x$ odd, $z$ even: no solution. | checked | $b$ even gives $C^z\equiv7\pmod8$, and odd squares are $1\pmod8$. |
| $x$ even, $z\ge4$: excluded by Bennett–Ellenberg–Ng, Theorem 1. | caveat | The equation is $b^4+(d^{x/2})^2=C^z$ with coprime nonzero terms, which is the shape that theorem treats for exponent at least 4. The statement was recalled, not read from the source. Confirm under C4. |
| Class numbers 11, 13, 62. | checked | Independent count of reduced forms in `scripts/audit_skeleton.py`. Agrees with `check_twists.py` and with `IdealDescent.lean` for 167 and 2471. |
| $p\ge5$, $p\nmid h$: $b^2+d^{(x-1)/2}\sqrt{-d}=\alpha^p$. | checked | The two conjugate ideals are coprime because $C$ is odd and prime to $bd$. Their product is $(c)^p$, so each is a $p$th power of an ideal, principal since $p\nmid h$. The units are $\pm1$ and $p$ is odd. Note that $\alpha$ may have half-integral coordinates, since the ring of integers is $\mathbb Z[(1+\sqrt{-d})/2]$. The Lucas argument allows this. |
| $(\alpha,\bar\alpha)$ is a Lucas pair with no primitive divisor at index $p$. | checked | $\alpha\bar\alpha=c$ and $(\alpha+\bar\alpha)^2$ are coprime: a common prime divides $\alpha^p+\bar\alpha^p=2b^2$ and $c$, which are coprime. $\alpha/\bar\alpha$ is not a root of unity because the units are $\pm1$ and both coordinates of $\alpha^p$ are nonzero. Odd primes of $L_p$ divide $d$, hence the discriminant. The prime 2 divides $L_2$ or $L_3$. |
| No $p$-defective Lucas pair in these fields. | caveat | The list of fields for indices 5, 7, 13 in the proof matches the Bilu–Hanrot–Voutier table as recalled, and $-167,-263,-2471$ are absent from it. Confirm against the table under C4. |
| Remaining pairs are exactly $(167,11)$, $(263,13)$, $(2471,31)$. | checked | The primes $p\ge5$ dividing 11, 13, 62. |
| No small solutions. | checked | Search over $x\le12$, $b<3000$, all exponents $z\ge3$ finds none. This is a consistency check only. |

## Replays run by the lead

| Command | Result |
|---|---|
| `python3 scripts/audit_skeleton.py` | Class numbers 11, 13, 62. Parity claims hold. No small solutions. |
| `python3 scripts/check_twists.py --exponents` | Matches the conventions table in the [collaborator guide](collaborating.md): surviving nonprincipal pairs $(1,4),(23,7)$ at 167 and $(5,23),(67,8)$ at 2471, with principal pairs at $x\equiv31,93\pmod{124}$. |
| `python3 scripts/check_cubic_twists.py` | Empty sets for 167 and 2471. At 263 the two surviving rows contain $b\in\{4,5\}$ modulo 9, as documented. |

The PARI/GP, eclib, Brandt and Lean replays were not run by the lead. They are task C2.

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
