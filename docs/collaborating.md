# Expert collaborator guide

For $A\in\{167,263,2471\}$ the project has a computer-assisted proof excluding positive primitive $A^x+B^y=C^z$ for all $x,y,z\geq3$ with $4\mid y$. The most useful independent review is the passage from the arithmetic equation to the exact finite computations. The [proof by cases](fixed-bases.md) gives the full implication. The [research plan](research-plan.md) ranks possible extensions. A newer claim, that $2471^x+U^2=c^{31}$ has no primitive solution for an arbitrary square, has had one internal review and no specialist review, and would benefit most from a second pair of eyes. [Internal review](square-summand-2471-review.md) [Arbitrary square at 2471](square-summand-2471.md)

## Proof map

| Case | Proof input | What to scrutinize |
|---|---|---|
| $3\mid z$ | Oriented ideal factorization in a quadratic field for odd $x$, Gaussian cubes for even $x$. | For an even right base, dividing by 2 gives an ideal with valuation one at exactly one prime above 2. The orientation depends on $x\bmod4$. At 263 the last two classes are excluded by the prime 26723 in denominators of rational points. [Denominator proof](transfer-263.md#a-denominator-obstruction-on-the-remaining-mordell-curve) The relevant obstruction repeats modulo 12. [Cubic proof](right-exponent-three.md) |
| $x$ even and $z\geq4$ | Bennett–Ellenberg–Ng, Theorem 1, applied to a square plus a fourth power. | The two summands have coprime positive bases. [Assembly](fixed-bases.md) |
| $x$ odd and $z\geq4$ even | Odd squares are 1 modulo 8. | The parity step forces $b$ even and $C^z\equiv7\pmod8$. [Assembly](fixed-bases.md) |
| $x$ odd, $p\mid z$, $p\geq5$, $p\nmid h(-d)$ | Principalization and the classification of defective Lucas pairs. | Check the nonzero trace, coprimality with the norm, discriminant and the list of quadratic fields at indices 5, 7 and 13. [Lucas argument](fixed-bases.md) |
| $(d,p)=(167,11)$ | A rational point of order 2 rules out a rational 11-isogeny via the degree-22 classification. Level lowering leads to 32 or 5344. | At 3 the bad fibers require the signed lowered trace. The good fibers at 5 give four possibilities across the two classes of $d^x$. [Frey proof and PARI replay](frey-167.md) |
| $(d,p)=(263,13)$ | A rational 26-isogeny is impossible. Level lowering gives 32 or 8416. | On the 262-dimensional newspace at 8416, $T_3(T_3+4)$ is invertible modulo 13. The larger relative plus space contains extra systems. [Transfer calculation](transfer-263.md) |
| $(d,p)=(2471,31)$ | Both locally admissible twists force $683\mid c$. That divisor fixes the nonsplit lowered trace. | Verify the signs and that the Hecke operators act at the same residual prime. Rank after extension of scalars covers coefficient fields of every degree. [Descent](descent.md) · [Frey proof](frey-curve.md) · [Brandt matrices](brandt-sieve.md) |

Here $h(-d)$ denotes the ideal class number of $\mathbb Q(\sqrt{-d})$. A form matching the trace at each prime under different reductions would fail the necessary simultaneous condition.

## Conventions

Write $s^2=-d$, $\omega=(1+s)/2$, and $R=\mathbb Z[\omega]$. Choose $P\mid 2$ by $P^p=(\eta)$. For odd right base the convention $IP^k=(\beta)$ gives $\beta^p=\eta^k(b^2+d^{(x-1)/2}s)$. At both signed embeddings of a split modulus use the same $b$. Allow separate roots, including nonunits. The local residues of $b$ may vary across primes. These exponent classes describe the output of the descent before its modular exclusion.

| $d,p$ | $h(-d)$ | $\eta$ | Surviving nonprincipal $(x\bmod 4p,k)$ |
|---|---:|---|---|
| 167, 11 | 11 | $(3+7s)/2$ | $(1,4),(23,7)$ |
| 2471, 31 | 62 | $(90621+391s)/2$ | $(5,23),(67,8)$ |

In the even-right-base cubic proof the identity is $\beta^3=\eta_Q^k(b^2+d^{(x-1)/2}s)/2$, where $Q$ is the particular prime above 2 selected by the numerator. This $k$ has a different definition. [Orientations at 2](right-exponent-three.md#odd-x-and-even-c)

## Verification

The [README](../README.md#reproduce-the-calculations) lists the primary replays. Use ordinary Python execution. For the modular results, verify at least the following.

| Replay | Expected result |
|---|---|
| `python3 scripts/check_cubic_twists.py` | Twelve empty sets for 167 and 2471. At 263 the two surviving rows modulo 9 each contain 4 and 5. |
| `python3 scripts/check_twists.py --exponents` | At 2471, the complete output includes $(31,0)$ and $(93,0)$ as well as the two nonprincipal pairs. A separate argument excludes the principal pairs. |
| `gp -q -f scripts/check_new_5344.gp` | Level 32 has $a_5=-2$. At 5344 the first kernel at 3 has dimension 3, the joint kernel with 5 has dimension 0. |
| `python3 scripts/check_brandt.py` | Four 2124-dimensional blocks give total determinant 29 modulo 31. The two known elliptic-curve trace pairs give positive controls. |
| `gp -fq scripts/check_transfer_263.gp` and `gp -fq scripts/check_mordell_263.gp` | The exact-level rank is 262/262. On the Mordell curve the rank is one, the torsion is trivial, and four finite-field witnesses exclude all the required index primes. |
| Classical eclib replay | Full column ranks 676 and 11336 for each of the two trace pairs at the respective levels. A level-11 control has nullity one. |
| `scripts/check_modsym_hecke.cpp`, following the [replay note](modular-symbols-replay.md) | `FINAL dim 0` at 5344 modulo 11 and at 79072 modulo 31 on the full relative spaces of dimension 1345 and 22657. The 79072 run uses 311 in place of 683. The control curve gives `FINAL dim 2`. |

| `python3 scripts/check_square_2471.py verify` | The retained space has dimension 42, the CM system of $y^2=x^3-x$ has multiplicity 8, and all 961 classes have zero common kernel under both sign conventions. Regeneration of the matrices is described in the [note](square-summand-2471.md#reproduction). |

The [audit](audit.md) records which steps of the proof have been independently checked. Its standalone replay `python3 scripts/audit_skeleton.py` (standard library only) recomputes the class numbers 11, 13 and 62 and the parity claims, and finds no small solutions.

The classical eclib replay (`scripts/check_eclib_hecke.cpp`) uses eclib 20250122, FFLAS-FFPACK 2.5, Givaro 4.2, NTL, GMP and OpenBLAS. Install their development headers and run the commands below from the repository root. The clean replay records the pinned commands, both modular-symbol control kernels and the exact Lean build output. [Clean replay](clean-replay.md)

```sh
c++ -O3 -std=c++17 scripts/check_eclib_hecke.cpp -o /tmp/beal-hecke -lec -lntl -lgivaro -lgmpxx -lgmp -lopenblas
/tmp/beal-hecke
```

Build the Lean development with the pinned toolchain and Mathlib `v4.19.0`: first `lake exe cache get`, then `lake build`. The declarations `Beal.QuadraticBridge.no_integral_twist167` and `no_integral_twist2471` start from an integral twist for the **left** exponent $x=3$ at right exponent 11 or 31. The declarations `Beal.Forced683.forced683_at5` and `forced683_at67` prove $683\mid c$ for both lifted classes under the displayed twist and equation. The theorem `Beal.CubicTwists.no_local_cubes` checks the twelve oriented cases with **right** exponent 3. Its scope is the finite test at the two embeddings. [Cubic Lean certificate](../lean/CubicTwists.lean)

The `Beal.TwistIdentity` development proves the general odd-exponent norm identity, the encodings of the two generators $\eta$, and absorption of an odd-power unit sign. Its `IdealFrontDoor.signed_twist` field specifies the outstanding ideal-theoretic input. The signed declarations `no_integral_twist167_of_signed` and `no_integral_twist2471_of_signed` feed the previous cubic certificates. [Algebraic interface](../lean/TwistIdentity.lean)

For $d=167,2471$, Lean proves the unit group is $\{\pm1\}$, rules out elements of norm two and counts reduced forms. The instances `idealAPI167` and `idealAPI2471` use Mathlib ideals of $\mathbb Z[\omega]$ with $\omega=(1+\sqrt{-d})/2$. The standard identification with the full ring of integers of $\mathbb Q(\sqrt{-d})$ still lacks a Lean equivalence with `NumberField.RingOfIntegers`. The two `no_integral_twist*_of_mathlib_gap` theorems for $x=3$ still assume `DedekindGap`, which supplies $(\gamma)=I^p$, $P^p=(\eta)$ and a principal ideal $IP^k$. [Finite descent data](../lean/IdealDescent.lean) · [Concrete ideals and theorem statements](../lean/OmegaRing.lean)

The level-lowering theorem and the modular-form calculations remain external to these Lean statements. Class-number counts for the two bases are now checked in `IdealDescent`. [Quadratic bridge](../lean/QuadraticBridge.lean) · [Divisor at 683](../lean/Forced683.lean)

## Contributions that would change the scope

- **Try the rank-one denominator test on another residual cubic.** Given a nontorsion point $P$, take a good prime $q$ outside the allowed denominators at which $P$ reduces to the identity. For each prime $l\mid\#E(\mathbb F_q)$, find an auxiliary reduction certifying that $P$ is indivisible by $l$. At rank one with trivial torsion, this proves that every affine rational point has $q$ in its denominator. [Worked example](transfer-263.md#a-denominator-obstruction-on-the-remaining-mordell-curve)
- **Test a new base.** State the class number, the exceptional residual prime and the precise Frey level for each exponent class. Report the dimensions before and after each trace filter. A surviving eigensymbol in a space containing oldforms needs identification before it motivates a new descent.
- **Review or extend the arbitrary-square results.** The test succeeds at 167 with right exponent 11 and at 2471 with right exponent 31. An internal review recomputed the Hecke operators on the 42-dimensional space at level 79072 with eclib. [eclib replay](replays/square-2471-eclib.md) A recomputation by someone outside the project would still be valuable. The same test at 263 with right exponent 13 succeeds, and its review found a one-operator proof on the newspace of level 8416. [263](square-summand-263.md) A full statement about even $y$ at one base needs more than was first thought: the right exponents 3 and 4, and, for every other prime exponent, the branch with an even right base, which the fourth power used to exclude. [167](frey-167.md#an-arbitrary-square-summand-at-exponent-11) · [2471](square-summand-2471.md) · [Next targets](research-plan.md#the-next-arithmetic-target)
- **Formalize an arithmetic bridge.** Produce the oriented integral twist from a primitive solution using the concrete Mathlib ideals and the outstanding [`DedekindGap` fields](../lean/IdealDescent.lean), or certify a Hecke determinant together with the identification of its operator. A formal statement that takes either conclusion as a premise verifies only the following implication.
- **Develop an independent global route.** For the degree-31 form the inexpensive test is $[P_2]=x[P_{17}P_{23}]$. The two local twists have points everywhere. A full class-group or unit computation is optional for the completed 2471 example. [Ideal-class relation](trace-ideal-classes.md) · [Global form](thue-mahler.md) · [Local points](local-points.md)
