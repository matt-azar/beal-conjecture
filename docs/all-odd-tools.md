# Three experiments on all-odd Beal signatures

**Status, 27 November 2026.** Exploratory mathematics with an exact replay, pending independent review. The experiments produced a restriction on a degree-eleven field attached to a hypothetical solution, a field that survives every local comparison, and two obstructions to proposed proof strategies. No new Beal signature was excluded. Historical priority for the deductions here has not been established.

## A number-field fingerprint for a solution

Suppose $A^3+B^5=C^{11}$ with positive pairwise coprime integer bases. Set $t=A^3/C^{11}$, so $1-t=B^5/C^{11}$. The aim was to construct a number field from $t$ whose possible factorizations could contradict one another. First use $(3,5,7)$ as a control. Integrating $105T^2(1-T)^4$ from zero gives exactly $1-\phi(1-T)$ for the septic polynomial $\phi$ of Dahmen and Siksek. Their work went much further, including a classification of the possible local algebras. Chocian’s September 2026 preprint claims the exclusion of the remaining seven fields. We did not audit that proof. The septic construction is prior work. [Dahmen–Siksek, §§2–4](https://few.vu.nl/~sdn249/GFE357.pdf) · [Chocian, Theorem 1.1](https://arxiv.org/abs/2609.26996)

For $(3,5,11)$ the tool found the rational polynomial

$$F(T)=1+(5T-3)(T^2+T+3)^5/729.$$

Write $H=T^2+T+3$, $N=729F$, and $G=N/T^3$. Then $N'=55T^2H^4$ and $G(0)=1485$. The critical points at $0$, the two roots of $H$, and infinity have indices $3,5,5,11$, respectively. Set $E_t=\mathbb Q[T]/(N(T)-729t)$. Its defining polynomial has discriminant $-3^{60}5^{10}11^{11}t^2(t-1)^8$. It is separable for our $t$, and strict monotonicity on the real line gives one real root. $E_t$ may be a product of fields.

### What the sieve actually forces

If $E_t$ is a field of the form $\mathbb Q(\sqrt[11]{d})$, $d\in\mathbb Q^\times$, then **$3182=2\cdot37\cdot43$ divides $C$**. Also every prime $l\mid A$ outside $3,5,11$ satisfies **$l\equiv 1$ or $-1\pmod{33}$**. Both statements require the pure-field hypothesis.

For a good prime $l\notin\{3,5,11\}$, the following separable reductions give necessary residue degrees. Here $u$ ranges over residue units. Each row follows by expanding around a simple root or rescaling around a multiple root until the reduced polynomial is separable. Hensel lifting then gives unramified factors with the indicated degrees. Different entries in the same row form a disjoint union of root sets, so equal degrees are counted with multiplicity.

| Divisibility | Polynomials to factor over $\mathbb F_l$ |
|---|---|
| $l\nmid ABC$ | $N(T)-729j$, for $j\ne0,1$ |
| $l\mid A$ | $G(T)$ and $1485T^3-729u$ |
| $l\mid B$ | One linear factor and $99T^{10}-11(729u)T^5+(729u)^2$ |
| $l\mid C$ | $5T^{11}-729u$ |

In the $A$ row, put $k=v_l(A)$ and substitute $T=l^kY$ at the triple root. In the $B$ row, the roots $h$ of $H$ are distinct and $5h-3$ is a unit, since their discriminant is $-11$ and the norm of $5h-3$ is $99$. Work over the unramified extension containing $h$. With $k=v_l(B)$ use the coordinate $Y=H(T)/l^k$ near $h$, which is invertible there after scaling because $H'(h)$ is a unit. Its reduction satisfies $(5h-3)Y^5+729u=0$. Taking the product over both $h$ gives the displayed decic. For $u\ne0$, each root $Y$ recovers $h$ uniquely, including in characteristic two. In the $C$ row use $Y=CT$. These reductions also prove that $E_t$ is unramified outside $3,5,11$ under the primitive-solution hypothesis.

At $2$ the factor degrees are exactly $(1,2,3,5)$ when $A$ is even, $(1,2,4,4)$ when $B$ is even, and $(1,10)$ when $C$ is even. If $E_t$ is a field and $A$ is even, its Galois closure has group **$S_{11}$**. The fifteenth power of the first Frobenius permutation is a transposition. A transitive group of prime degree containing a transposition is the full symmetric group. Indeed, the graph of its conjugate transpositions has equally sized components, hence is connected, and the edge transpositions of a connected graph generate the symmetric group.

For a pure field, identify the eleven roots as $\alpha\zeta^i$, $i\in\mathbb F_{11}$. Frobenius at an unramified good prime acts by $i\mapsto li+b$. For $l\not\equiv1\pmod{11}$ it has one fixed point and all other cycles have length $\operatorname{ord}_{11}(l)$. For $l\equiv1\pmod{11}$ it is the identity or an eleven-cycle. The check uses both options. For the more general case of an irreducible field with solvable Galois closure, allow any nonzero multiplier. Indeed, a nontrivial minimal normal subgroup of a solvable group is elementary abelian. Primitivity makes it transitive, and an abelian transitive subgroup acting faithfully is regular. Its order here is eleven. Its normalizer acts affinely.

The full table through $97$ is in the replay. Only the $C$ row survives at $2,37,43$ for a pure field. For the general affine group only $2$ forces $C$ in this range. These are necessary tests, allowing all units in each row. To see the restriction on primes of $A$ at arbitrary size, its three-root cluster must be a union of Frobenius cycles. For an affine map with multiplier $l\ne1\pmod{11}$ that requires order two, hence $l\equiv-1\pmod{11}$ and cluster type $(1,2)$. A separable binomial $T^3-a$ can have that type only if $l\equiv-1\pmod3$. For multiplier one the three-root cluster forces the identity, so it splits completely and $l\equiv1\pmod3$. This proves the two congruence classes.

### Why the sieve stops, even with all primes

Let $K=\mathbb Q(\sqrt[11]{3^6 5^{10}})$. This is a degree-eleven field because the valuation of a root at $5$ is $10/11$, forcing ramification index divisible by eleven. **At every prime $l$ there is an exact, nonzero, locally primitive solution in $\mathbb Z_l$ whose associated algebra is $K\otimes\mathbb Q_l$.** Its real algebra also occurs for a positive real solution.

Take $C$ nonzero and sufficiently close to zero in $\mathbb Z_l$. Set $A=(1+C)^5$ and solve $B^5=C^{11}-A^3$ near $B=-1$. The limiting root is simple over $\mathbb Q_l$, so Hensel lifting works, including at $l=5$ upon taking $C$ sufficiently small. Both $A$ and $B$ are units. In the coordinate $V=5CT$ the monic defining polynomial is

$$5^{10}C^{11}N(V/(5C))-729\cdot5^{10}A^3.$$

Its coefficients extend to $C=0$, where it is $V^{11}-3^65^{10}$. The limit is separable. To see that the **whole local algebra** persists, split $K\otimes\mathbb Q_l$ as a product of local fields. In each factor lift the component of the limiting generator to a nearby root of the perturbed polynomial. For the resulting tuple $v$, the determinant of $1,v,\ldots,v^{10}$ in a fixed basis stays nonzero by continuity. Thus the perturbed root generates the same product algebra. Over $\mathbb R$, take $A=2$, $B=3$, $C=251^{1/11}$. Both polynomials have one real root and five conjugate pairs.

Here the local triples can vary with the prime. This proves that tests asking only whether this fixed field occurs at each completion can never eliminate it. A condition tying the primes together, such as an obstruction on rational points of a twist, could still eliminate it. The result does not determine whether $K$ arises from a global primitive solution. The analogous survival of pure candidates for the septic map is already visible in Dahmen–Siksek, Proposition 3.3 and §4.3. [Paper](https://few.vu.nl/~sdn249/GFE357.pdf)

There is also a concrete control for the nonsolvable branch. At $t=8/9$, $N(T)-648$ becomes Eisenstein at $11$ after $T\mapsto T+2$. Its constant term is $88\pmod{121}$. At $2$, $v_2(t)=3$ gives the same $(1,2,3,5)$ calculation, hence this field has Galois closure $S_{11}$. Its discriminant support is contained in $\{3,5,11\}$ by the displayed discriminant and the unramified calculation at $2$. Yet $8/9$ cannot equal $A^3/C^{11}$ for coprime positive integers, since its reduced denominator is $9$. Thus even these strong, readily checked features admit an explicit spurious parameter.

### How the tool found the polynomial and where it failed

Seek a polynomial with a single critical point of index $s$ at zero and two of equal index $p$ at the roots of $h=T^2+aT+b$. Integrate $T^{s-1}h^{p-1}$. The values at the two roots coincide precisely when the linear coefficient of the integral modulo $h$ vanishes, provided the roots are distinct. Normalize $a=1$ by rational scaling when $a\ne0$, and test $a=0$ separately.

* For doubled index 5 and single index 3, the nondegenerate rational root is $b=3$ with $a=1$. Normalizing the branch values to zero and one gives $F$ above.
* For doubled index 3 and single index 7, the residual cubic is $10b^3-90b^2+105b-28$. It has no root modulo $19$, where its leading coefficient is a unit. The discarded value $4b=1$ merges the two critical points. The case $a=0$ forces $b=0$, another collision. This rules out **every degree-eleven genus-zero three-point cover over $\mathbb Q$ with exact branch orders $(3,7,11)$ and rationally labelled branch values**. An eleven-cycle forces a unique rational pole, hence a polynomial coordinate. The degree bound allows one seven-cycle. Riemann–Hurwitz then forces exactly two three-cycles. These exhaust the possibilities. Higher degrees and coefficient extensions remain outside this argument.
* Further exploratory pairs $(p,s)=(3,13),(3,19),(5,11),(7,5)$ gave residual degrees $6,9,5,2$ after removing the collision factor in the $a=1$ chart. None had rational roots there. The `--critical-pair` mode reproduces their polynomials.

## A substitution into an easier signature

The hoped-for shortcut was a rational function of $t$ transferring the power divisibility at $0,1,\infty$ into a solved hyperbolic triangle signature. Assign weights $p,q,r$ to these points and weight one elsewhere. Require $n(f(x))\mid m(x)e_x$ at every geometric point, where $m,n$ are source and target weights and $e_x$ is local degree. This guarantees the divisibility structurally. A substitution depending separately on the bases, or only on a special arithmetic subset, need not satisfy it.

**For three distinct odd prime source weights, every such nonconstant map to a hyperbolic triangle has degree one and permutes equal weights.** Write $D=1-\sum 1/m$. The orbifold Riemann–Hurwitz inequality gives $dD_{\rm target}\le D_{\rm source}$. Each source mark must matter. If its weight could be dropped to one, the resulting source would have negative $D$, contradicting the inequality. Consequently its prime divides its target weight. [Pakovich, Proposition 3.2](https://pakovich.github.io/semicon.pdf)

If the three images are distinct, the target weights dominate the corresponding source primes and $D_{\rm target}\ge D_{\rm source}$. Equality forces degree one and identical weights. If just $p,q$ collide, their common target weight is a multiple of $pq$. The fiber thus has degree at least $p+q$. The target weights are at least $pq,r,2$. For $r=3$, $pq\ge35$, giving $D_{\rm target}\ge29/210$. For $r\ge5$, $pq\ge15$ gives the stronger $D_{\rm target}\ge7/30$. Hence $d<210/29<8\le p+q$, impossible. If all three collide, their fiber has degree at least $pq+pr+qr\ge71$. Every hyperbolic triangle has $D\ge1/42$ (sort the weights, with minimum at $(2,3,7)$), so $d<42$. This exhausts the cases. The finite prime sweep in the script checks the pair-collision calculation only. The proof covers unbounded primes.

## Differentiating the integer equation

For pairwise coprime $x,y,z>1$ with $x+y=z$, assign integer weights $d_l$ to primes and set $D(n)=\sum_{l\mid n}(n/l)v_l(n)d_l$. Impose $D(x)+D(y)=D(z)$. The Wronskian $W=xD(y)-yD(x)$ is always a multiple of $L=xyz/\operatorname{rad}(xyz)$. The idea was that prescribed perfect powers might force a larger divisor. This uses Pasten’s framework for arithmetic derivatives. [Pasten, Theorem 3.3 and Lemma 3.4](https://arxiv.org/abs/2106.16165)

Put $g_n=\gcd_{l\mid n}((n/l)v_l(n))$. Disjoint prime supports let $D(x),D(y),D(z)$ range independently over $g_x\mathbb Z,g_y\mathbb Z,g_z\mathbb Z$ before imposing additivity. The exact positive generator of the Wronskian image is

$$M=\gcd(zg_xg_y,yg_xg_z,xg_yg_z)/\gcd(g_x,g_y,g_z).$$

Indeed, use the integer matrix with rows $(g_x,g_y,-g_z)$ and $(-yg_x,xg_y,0)$. Its image has index equal to the gcd of its maximal minors by Smith normal form. Projection to the first coordinate has image $\gcd(g_x,g_y,g_z)\mathbb Z$. Dividing the index by that generator gives the generator on the vertical axis, where additivity holds.

If the bases in a hypothetical $(3,5,11)$ solution are squarefree and coprime to $165$, then $M=L$. For $x=A^3,y=B^5,z=C^{11}$ one has $g_x=3A^2,g_y=5B^4,g_z=11C^{10}$. Their gcd is one and the three maximal minors divided by $L$ have gcd $\gcd(15C,33B,55A)=1$. Thus the anticipated extra factor disappears under these hypotheses. In the genuine control $2^7+17^3=71^2$, weights $(d_2,d_{17},d_{71})=(-1,-8,-52)$ attain $W=L=1{,}313{,}216$. Other controls below attain multipliers two and three in the image formula. The computation measures divisibility. A bound for the size of the weights in an arbitrary Beal triple is a further global question.

## Replay

Tested with CPython 3.12.14 and SymPy 1.14.0. Run `python3 scripts/probe_beal_tools.py` from the repository root. Optional commands include `--critical-pair 3 7`, `--wronskian 128 4913`, and `--prime-limit N`. An initial pass inspected only regular residues through 47. It left multiplier one untreated at 23. The full replay includes both possible cycles there, the three ramified fibers of the map at every good prime, and all good primes through 97. At $2,37,43$ it verifies each factor-degree list again by counting fixed roots of Frobenius powers via polynomial gcds. The all-completions assertion is a proof above, independent of the finite sweep.

```
transfer pair collisions, odd primes <100: 6072 checked, 0 survive
doubled 3, single 7: -(4*S - 1)**2*(10*S**3 - 90*S**2 + 105*S - 28)/13860
  zero linear coefficient: -8*S**5/693
doubled 5, single 3: -(S - 3)*(4*S - 1)**4/6930
  zero linear coefficient: -128*S**5/3465
cubic roots mod 19: none; degree-11 discriminant constant: -3^60*5^10*11^11
control t=8/9: Eisenstein at 11 after shift by 2, constant mod 121 = 88
q   pure  affine   (U = all bases units)
at 2: {'U': [], 'A': [(1, 2, 3, 5)], 'B': [(1, 2, 4, 4)], 'C': [(1, 10)]}
 2  C     C
 7  UC    UC
13  UC    UC
17  UC    UC
19  UBC   UBC
23  UC    UC
29  UBC   UBC
31  BC    UBC
37  C     UC
41  UBC   UBC
43  C     UC
47  UC    UC
53  UC    UC
59  UC    UC
61  UBC   UBC
67  UC    UC
71  UBC   UBC
73  UC    UC
79  UBC   UBC
83  UC    UC
89  UC    UC
97  UC    UC
affine: forced divisors of C = [2], product = 2
pure: forced divisors of C = [2, 37, 43], product = 3182
boundary polynomial: V^11 - 3^6*5^10
2^7+17^3=71^2: W image / baseline = 1
3^5+11^4=122^2: W image / baseline = 2
7^3+13^2=2^9: W image / baseline = 3
1414^3+2213459^2=65^7: W image / baseline = 1
```
