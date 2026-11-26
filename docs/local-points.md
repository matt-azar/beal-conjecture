# Local points on the two surviving exponent-31 twists

Let $d=2471=7\cdot353$. The [descent](descent.md) leaves two possibilities for a primitive positive solution of $d^x+b^4=c^{31}$ with odd $x\geq3$.

| $x$ | Global class $k$ | Necessary value of $b\bmod683$ |
|---|---:|---|
| $5+124j$ | 23 | $\pm26d^{31j}$ |
| $67+124j$ | 8 | $\pm298d^{31j}$ |

**Every such solution has $683\mid c$. Both surviving twists admit primitive local solutions over every $\mathbb Q_q$ and over $\mathbb R$.** Here local primitivity means that no rational prime at the specified place divides two of $d,b,c$. The local solutions may be chosen with $bc\ne0$. Thus prime-power solvability of either twist on its own cannot eliminate it. The integer solution would have to satisfy all these conditions with one set of global variables.

## What the prime 683 forces

Put $s^2=-d$, $\eta=(90621+391s)/2$ and $a=d^{(x-1)/2}$. The identity to be tested is $\beta^{31}=\eta^k(b^2+as)$ in the quadratic algebra. Its norm recovers $c=N(\beta)/2^k$. Outside the primes dividing $d$, increasing $x$ by $124j$ multiplies $a$ by $d^{62j}$ and rescales $b,\beta,c$ by $d^{31j},d^{2j},d^{4j}$ respectively. These are units at such places. Work first with $x=5,67$.

At 683, take $s=332,-332$. The images of the right side must both be 31st powers in $\mathbb F_{683}$. Testing all $b$ gives the full list.

| $(x,k)$ | $b$ | Images | One pair of 31st roots |
|---|---|---|---|
| $(5,23)$ | $\pm26$ | $(681,0)$ | $(29,0)$ |
| $(67,8)$ | $\pm298$ | $(0,32)$ | $(0,8)$ |

The zero component forces $683\mid c$. The [Lean proof](../lean/Forced683.lean) verifies the divisor for every exponent lift, assuming the corresponding shared integral twist and original equation. The nonzero component forces $683\nmid b$. More precisely, **any prescribed valuation $v_{683}(c)=h\geq1$ is possible locally**. Lift the chosen root of $s^2=-d$ by Hensel's lemma. In the zero component prescribe the value of $\beta$ to be $683^h$. Solve for $b$ in this component by Hensel lifting, since $2b$ and the image of $\eta$ are units. The other component still reduces to a nonzero 31st power, so also has a 31st root over $\mathbb Z_{683}$. Taking norms gives the stated valuation. This explains why higher precision at 683 alone cannot dispatch the survivors.

## The finitely many small primes

At a good prime $q\nmid 2\cdot7\cdot31\cdot353$, reduction of $\mathbb Z[(1+s)/2]$ gives either $\mathbb F_q\times\mathbb F_q$ or $\mathbb F_{q^2}$. If 31 does not divide the relevant unit-group exponent ($q-1$ or $q^2-1$ respectively), every unit has a 31st root. Take $b\equiv0\pmod q$ so both $\eta$ and $b^2+as$ are units. In all other cases the verifier searches for a $b$ whose image gives a nonzero 31st power. It uses $z^{(Q-1)/31}=1$ in a residue field of size $Q$. In the split case both components use the same $b$. Any unit root so obtained lifts by Hensel's lemma since $q\ne31$, and $b$ can be lifted to a nonzero integer.

Among the 505,656 good primes below $2731^2=7,458,361$, the search addresses 8,420 split and 16,819 inert primes explicitly. At every prime except 683 both twists admit unit values of $c$. At 683 the exhaustive test above applies.

- At $q=2$, the quadratic algebra is split. The valuations of $\eta$ in its two factors are 31 and 0 since $N\eta=2^{31}$ and its trace is odd. With $b=2$, $b^2+as$ is a unit in both components. Every 2-adic unit has a 31st root, and the two valuations of the twisted right side are divisible by 31. Taking norms gives $c$ odd.
- At $q=7,353$, take $b=1$. The right side is a unit of the ramified quadratic completion and its residue field has order $q$. Since $31\nmid q(q-1)$ every local unit is a 31st power. This argument applies directly to every $j$, preserving local primitivity at the primes dividing $d$.
- At $q=31$, the quadratic algebra is split. Choose $s\equiv90\pmod{961}$ and its negative. For $(x,k)=(5,23)$, take $(b,y_+,y_-)=(425,10,27)$. For $(67,8)$ take $(461,25,13)$. The two $y$ values in each row are unit 31st roots modulo $31^2$. A 31-adic unit with a unit 31st root modulo $31^2$ has one over $\mathbb Z_{31}$. Indeed, the binomial expansion of $(y+31t)^{31}$ lets one choose $t$ to lift the congruence to modulus $31^3$; then the usual valuation form of Hensel's lemma applies.
- Over $\mathbb R$ the quadratic algebra is $\mathbb C$. Any positive $b$ gives a nonzero complex value with a 31st root, and its norm gives positive $c$.

## All larger primes

For a good $q$ consider the curve over $\mathbb F_q$ obtained by equating the two coefficients of $\beta^{31}=\eta^k(b^2+as)$ in the quadratic algebra. Over an algebraic closure its function field is given by adjoining to $\overline{\mathbb F}_q(b)$ two 31st roots of constant multiples of $b^2+ar$ and $b^2-ar$, where $r^2=-d$. These quadratics have four distinct simple zeros. The valuations at a zero of the first and a zero of the second show that the two radicands are independent modulo 31st powers. Kummer theory therefore gives a geometrically integral cover of degree $31^2$.

The cover is tame. At each of the four finite zeros the inertia order is 31. At infinity both radicands have a pole of order two, and their ratio is a unit with a 31st root in the geometric local field, so the inertia order there is also 31. There are no further branch values. Riemann–Hurwitz gives the genus of the smooth projective model as $g=1365$ from $2g-2=-2\cdot31^2+5\cdot31\cdot30$. At most $5\cdot31=155$ geometric points lie above the five branch values.

The Hasse–Weil bound gives at least $q+1-2730\sqrt q$ rational points on this model. For $q\geq2731^2$ this exceeds 155. Hence at least one point is affine and unramified, where both 31st roots are units. Such a point is on the original affine curve because the cover is finite étale over that open set. It lifts to the $q$-adic quadratic algebra by the same unit-root argument. [Hasse–Weil bound](https://mathe2.uni-bayreuth.de/stoll/teaching/ArithHypKurven-SS2019/Skript-ArithHypCurves-pub-screen.pdf)

## Reproduce the finite checks

From the repository root, run the [C++17 verifier](../scripts/check_local_points.cpp).

```sh
c++ -O2 -std=c++17 scripts/check_local_points.cpp -o /tmp/beal-local-points
/tmp/beal-local-points
```

The verifier checks the exact admissible residues at 683, both unit witnesses at 31, and weak local solubility through the Hasse–Weil cutoff. The geometric cutoff, local lifting arguments and implication from the integer equation are written proofs.
