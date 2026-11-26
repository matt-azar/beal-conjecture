# Working on the Beal descent

The residual equation is now explicit. Both exponent-31 branches give a single irreducible degree-31 Thue–Mahler form supported on 2, 7 and 353. Computing its primitive solutions subject to the prescribed exponents and the square condition is the outstanding arithmetic task. [Binary forms, signs and reconstruction](thue-mahler.md)

The original question is whether a **primitive** solution of $2471^x+b^4=c^{31}$ can occur in either of the two surviving exponent classes. Here $b,c>0$, $x$ is odd and $x\geq3$, and $2471,b,c$ are pairwise coprime. The target includes arbitrarily large exponents and bases. For $4\mid y$ and $31\mid z$, substituting $b=B^{y/4}$ and $c=C^{z/31}$ recovers the corresponding portion of the original Beal equation. [Research plan and residual curves](research-plan.md)

## Which inputs support which conclusions?

| Question | Starting point |
|---|---|
| Is a square summand compatible with an 11-smooth complementary summand? | Bennett–Siksek's Theorem 2 supplies the complete list of 1,240 triples. The Python check authenticates its input and supplies a valuation-one witness in each of the 12 rows where the difference is a higher power. [Derivation and pinned authors' data](results.md#a-square-summand-and-an-11-smooth-summand) |
| Why remove the principal ideal class? | The Bilu–Hanrot–Voutier primitive-divisor theorem applies after checking the Lucas-pair hypotheses. The exceptional pair at index 13 has norm 2, whereas the descent here gives odd norm. This published input enters the sweep over all odd exponents. [Proof and references](results.md#the-quadratic-class-number-obstruction) |
| How do the two fixed-base cubic exclusions work? | The written descent uses ideal factorization and a reduced-form count. The cubic congruence certificates themselves cover **all** twist indices, including zero, so these two exclusions are independent of the Lucas theorem. [Arithmetic proof](descent.md#from-an-integer-solution-to-a-twist) · [Lean for 167](../lean/Twist167.lean) · [Lean for 2471](../lean/Twist2471.lean) |
| What generality does a literature comparison establish? | At $x=3$, substitution into $X^2+Y^3=Z^p$ places the $p=11$ example within a 2026 preprint's classification. Its stated range omits $p=31$. A result for the specific base 2471 gives no classification of all $(3,4,31)$ solutions. [Prior work and hypotheses](descent.md#relation-to-existing-work) |

## Conventions for exchanging calculations

Use $s^2=-d$ and $R=\mathbb Z[(1+s)/2]$. In the integral basis $1,\omega$ with $\omega=(1+s)/2$, one has $\omega^2=\omega-(d+1)/4$. Fix the prime ideal $P$ above 2 by $P^p=(\eta)$. The sign convention is $IP^k=(\beta)$, hence

$$
\beta^p=\eta^k(b^2+d^{(x-1)/2}s),\qquad 0\leq k<p.
$$

| $d,p$ | Discriminant, class number | $\eta$ | Surviving $(x\bmod 4p,k)$ |
|---|---|---|---|
| $167,11$ | $-167,11$ | $(3+7s)/2$ | $(1,4),(23,7)$ |
| $2471,31$ | $-2471,62$ | $(90621+391s)/2$ | $(5,23),(67,8)$ |

For the second row, $[P]$ generates the order-31 subgroup killed by 31. Changing the chosen generator to its inverse negates the twist labels. When comparing another computation, translate its ideal convention before comparing $k$. The exponent shifts by $4p$ through an invertible rescaling at moduli coprime to $d$. Only the local residues undergo this rescaling. [Definitions and proof of periodicity](descent.md#all-odd-exponents-for-the-two-fixed-bases)

A valid witness uses one **global** $k$. At a given modulus, the two substitutions $s\mapsto\pm r$ use the **same** residue of $b$ and allow separate $p$th roots. Different moduli may use different residues of $b$. Include zero and nonunits when testing powers at $p^2$. In particular, passing one modulus per twist is insufficient to exclude an integer solution. An empty intersection of the admissible twist sets is sufficient.

## Reproduce and extend

From the repository root, run `python3 scripts/check_twists.py --exponents` with Python 3.9 or later. For the cubic case at 31, the successive twist counts are 13, 2, 1, and 0. For the odd-exponent sweep, the two surviving pairs are shown above. With the pinned Lean 4.19.0, each cubic certificate ends in a theorem named `no_local_witnesses`; its printed axiom dependencies are `propext` and `Quot.sound`. The smooth-summand verifier takes the raw upstream table as its argument. The README gives the pinned revision and replay commands. [Reproduction instructions](../README.md#reproduce-the-calculations)

**Arithmetic contribution.** Generate the integer coefficients using `python3 scripts/check_residual_form.py --coefficients`. The arrays run from $u^{31}$ to $v^{31}$. For each primitive candidate $(u,v)$, check its sign and the linked valuations of $F$, test whether $H+F/2$ is a positive square, and recover $c=22u^2+9uv+29v^2$. Since $c$ is odd, $u$ is even and $v$ odd. This gives a quick cross-check on candidate coordinates. The parametrization uses $P^8$ in both branches, conjugating the $k=23$ branch. [Construction and converse](thue-mahler.md#explicit-integral-coordinates)

The two twists admit primitive points at every place. Their residues at 683 still force $683\mid c$ and a single slope in the common binary-form coordinates. Use this information in a global calculation. [All-places proof and its verifier](local-points.md) · [Smaller defining polynomial and prime decompositions](trace-field.md)

For a curve-based approach start with $x=5+124j$ and $k=23$. The curve $U^4+2471^5=V^{31}$ has $U=b/2471^{31j}$ and $V=c/2471^{4j}$. The *same* integer $j\geq0$ prescribes the denominators at both 7 and 353, with coprimality preventing cancellation. A single rational point on the unrestricted curve is relevant only after checking these valuations and the positive primitive numerators. A proposed local exclusion on a stronger cover should specify its map to the current twist and identify the exponent classes it covers. At 7 and 353 every local unit is already a 31st power. An argument using these primes needs relations beyond a power test on units. [Both residual equations](research-plan.md#2-attack-the-two-surviving-classes-for-2471)

**Formal contribution.** The main arithmetic interface takes an integer solution to an element $\beta$ and one $k$ satisfying the displayed equation. The substantive inputs are coprimality of conjugate ideals, the class group's $p$-torsion, and the extraction of the unit. The two declarations `Beal.QuadraticBridge.no_integral_twist167` and `Beal.QuadraticBridge.no_integral_twist2471` prove the ensuing contradiction for an explicit twist identity at $x=3$. Their input uses signed integer coordinates in the basis $1,\omega$. The declarations `forced683_at5` and `forced683_at67` take the corresponding integral twist and the original equation to $683\mid c$ for all exponent lifts. The front-door file [`TwistIdentity.lean`](../lean/TwistIdentity.lean) formalizes the algebraic-integer fragment (general-odd-$x$ norm of $\gamma$, $\eta$ encodings, odd-$p$ unit absorption) and packages the remaining Dedekind / class-group facts as `IdealFrontDoor`; `no_integral_twist167_of_signed` / `2471_of_signed` reuse the cubic certificates once a signed identity is supplied. Build them all with `lake build`. State which implication a new declaration proves and give its exact assumptions. This lets the next contributor reuse a checked lemma without introducing the desired global conclusion as a premise. [Formal targets](research-plan.md#1-connect-the-arithmetic-to-the-lean-certificates)

## Where an independent calculation would change the result

| Contribution | Inputs | What would settle it |
|---|---|---|
| Thue–Mahler computation | The explicit primitive form, its trace field and the coupled conditions at 7, 353 and 683 | A certified exhaustive enumeration with reconstruction of all positive primitive candidates, or a proof of incompatibility. [Field and prime data](trace-field.md) · [Lattice constraints](thue-mahler.md) |
| Modular forms | The weight-two newspace at level 79072, of dimension 2112. Rational newforms have been eliminated. | A simultaneous mod-31 Hecke test using a full integral lattice. The same prime over 31 must satisfy every trace condition. [Frey curve and trace filters](frey-curve.md) |
| Formal ideal theory | The two quadratic rings and the specified prime ideal above 2 | A theorem producing the integral twist from the primitive equation without supplying the desired identity as an input. Partial progress: [TwistIdentity](../lean/TwistIdentity.lean). Remaining gap: Dedekind factorization and class-group generation. [Checked ring evaluation](../lean/QuadraticBridge.lean) · [Checked divisor at 683](../lean/Forced683.lean) |

The Python, C++, and PARI/GP runs certify different finite computations. The pinned sources and replay commands are linked above and in the [README](../README.md#reproduce-the-calculations). For a proposed exclusion, record the exact theorem or input data, any external assumptions, and the range of exponents it covers. A failed search at bounded height leaves the two surviving classes intact. Even the lowest possible right base is already at least 61,556,730,755 on the first branch and exceeds $3\cdot10^{115}$ on the second, by the verified lattice minima.
