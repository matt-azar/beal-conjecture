# Research plan

The outstanding arithmetic target is the [degree-31 Thue–Mahler equation](thue-mahler.md) shared by both surviving exponent classes for $2471^x+b^4=c^{31}$. The global-to-local evaluation of the integral twist is now formalized for the two cubic exclusions. The unformalized part starts with the ideal class group. [Expert contributor guide](collaborating.md)

## Starting point

Write $d^x+b^4=c^p$ with positive pairwise coprime bases, odd $x\geq 3$ and prime $p$. This form also covers summand exponents divisible by four and right-hand exponents divisible by $p$, by absorbing their quotients into $b$ and $c$. The quadratic descent attaches one ideal-class index $k$ to a hypothetical solution. The same $k$ must pass every local test. With the choice of generator in the [descent notes](descent.md), the [exponent sieve](../scripts/check_twists.py) leaves the following pairs.

| $d$ | $p$ | $(x\bmod 4p,\ k)$ still possible |
|---:|---:|---|
| 167 | 11 | $(1,4),\ (23,7)$ |
| 2471 | 31 | $(5,23),\ (67,8)$ |

The row $x\equiv1\pmod{44}$ begins at $x=45$ under our hypotheses. A survivor passes the selected tests. Its existence as an integer solution is open in this argument. For $x=3$, Lean checks the contradiction given the principalized identity. The deduction of that identity from the ideal-class data remains a paper proof. [Lean bridge](../lean/QuadraticBridge.lean)

## What the AI-assisted proofs actually did

- **Erdős #728.** Kevin Barreto passed an informal argument from GPT-5.2 Pro to Harmonic's Aristotle. After readers clarified the intended statement, he asked for a stronger argument and ran Aristotle again. The resulting Lean proof reduces factorial divisibility to a binomial divisibility problem. Kummer's theorem turns each prime valuation into a count of carries when doubling an integer. A counting argument finds a single integer satisfying the requirements at all relevant primes simultaneously. Nat Sothanaphan subsequently explained the formal proof. Here the analogous question is whether local witnesses come from one global twist and one choice of denominators. [Proof and discovery account, including the appendix](https://arxiv.org/html/2601.07421v5)
- **AlphaProof Nexus, Erdős #125.** Near coincidences between powers of 3 and 4 supplied the mathematical idea for proving a digit-restricted sumset has lower density zero. During proof search the prover closed all but one goal, split that goal into three lemmas and retried. The authors also corrected an ambiguity about which density the statement meant and proved the corrected version. Their system resolved nine of 353 Erdős problems attempted. For Beal, keep the quantifiers visible when splitting a goal, especially the order of “there exists $k$” and “for every place.” [Methods, Figure 1 and §3](https://arxiv.org/html/2605.22763v1)
- **Alpöge and Claude, November 2026.** In his announcement concerning RH and GRH for Dirichlet $L$-functions, Alpöge describes choosing two ideas in a simpler setting and directing the transfer to the integer problem. A function-field argument gained multiplicity. Claude suggested a chain of theta lifts of length about $\sqrt X$ to reproduce that gain. This is the author's account of discovery. Rubinstein separately records kernel replays of the released statements. For Beal, express precisely what a generator of a principal ideal supplied, then test a replacement in a field with nontrivial $p$-torsion. [Alpöge's account](https://alpo.ge/remark.pdf) · [Independent verification](https://www.math.uwaterloo.ca/~mrubinst/alpoge_claude_grh/)

OpenAI reports that for its August collection a model found mathematical arguments, people and the model prepared manuscripts, and the model subsequently produced Lean certificates. A passing certificate indicates what was verified. Identifying who found the argument and how requires the discovery record. [OpenAI's account](https://openai.com/index/ten-advances-in-mathematics/)

## 1. Connect the arithmetic to the Lean certificates

1. Prove from primitivity that $c$ is odd for the two listed $d$. In $K=\mathbb Q(\sqrt{-d})$, show that the conjugate factors of $c^p$ are coprime and that the class of the root ideal lies in the subgroup killed by $p$. Certify that the prime ideal over 2 used in the calculation generates that subgroup. Include the class-number input and the orientation of the chosen generator.
2. Extract a **single** $k$ and an algebraic integer whose $p$th power is $\eta^k(b^2+d^{(x-1)/2}\sqrt{-d})$. Connect its signed coefficients to the existing bridge. The ring evaluation, preservation of powers and application of the two cubic certificates already build in Lean.

3. Prove why the tests at moduli coprime to $d$ repeat after $x\mapsto x+4p$. The imaginary coefficient scales by $d^{2p}$, the square coordinate by $(d^p)^2$, and the twist index stays fixed. This gives an invertible change of **local** variables. The scaled integer bases would lose primitivity. Then formalize the finite odd-residue sweep and the separate exclusion of $k=0$, with its primitive-divisor theorem dependency visible. Report exactly which global assumptions remain when inspecting the final Lean theorem.
4. Formalize the varying-base corollary in the [descent notes](descent.md#varying-the-base). For $x=3+4pj$, expand $(d u^{4p})^x=d^3 W^{4p}$ with $W=d^ju^x$. The condition $\gcd(u,M)=1$ makes $W$ invertible at every cubic-certificate modulus dividing $M$. Dividing the local identity by $W^{2p}$ must yield the existing cubic witness with the same $k$. This permits reuse of the certificates for arbitrarily large bases.

## 2. Attack the two surviving classes for 2471

Put $d=2471=7\cdot353$. Each residue class gives a fixed curve over $\mathbb Z[1/d]$. The integer problem also prescribes the denominators in lowest terms.

| $x$ and $k$ | Curve | $U$ | $V$ |
|---|---|---|---|
| $x=5+124j$, $k=23$ | $U^4+d^5=V^{31}$ | $b/d^{31j}$ | $c/d^{4j}$ |
| $x=67+124j$, $k=8$ | $U^4+d^7=d^2V^{31}$ | $b/d^{31j+15}$ | $c/d^{4j+2}$ |

Here $j\geq0$. Since $7$ and $353$ divide neither numerator, the powers shown are exact at both primes, and one $j$ sets all four valuations. Conversely a positive rational point with these exact denominators and numerators coprime to each other and to $d$ recovers an integer solution by clearing denominators. Keep $k$ attached when imposing the twisted local conditions.

The [all-places calculation](local-points.md) proves that each of these two twists admits primitive points over every completion. It also supplies $683\mid c$. A further search for an obstructing prime on the same twist cannot close either case. A stronger covering curve or a condition tying different places together could still succeed.

**Primary arithmetic task.** Use the [explicit binary form](thue-mahler.md) and its [degree-31 root field](trace-field.md) to enumerate or exclude its primitive solutions. Preserve the equality of valuations at 7 and 353, the single allowed slope at 683, and the positive-square condition. Begin with the possible prime ideals above 2, 7 and 353. Translate the known slopes into ideal conditions using the change of generator. Identify what class-group and unit certificates a complete calculation would need. A computed unit subgroup or a bounded enumeration requires an index or height bound before it can settle the residual equation.

**Independent check.** Use the [Frey curve at level 79072](frey-curve.md) and its trace restrictions as a second route. Any elimination needs to consider residual primes in the coefficient fields of the newforms left by level lowering. Rational-coefficient tests alone cover only part of that space.

Solving the two branches would settle this fixed-base exponent-31 family. An extension to general Beal would also need to cover other class groups, squarefree parts, and signatures in which neither summand is a square.
