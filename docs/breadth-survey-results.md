# A three-prime survey of the class-number branches

The fixed filters exclude primitive positive solutions of $151^x+b^4=c^7$ and reproduce the exclusion of $167^x+b^4=c^{11}$ for every odd $x\ge3$. At 151 the first trace already suffices. The filters leave two residual Hecke characters at $d=71$, three at $d=103$, and five at $d=119$. These are necessary conditions on a solution. This is a computer-assisted result pending mathematical review. [Protocol frozen in PR #7](breadth-survey-protocol.md)

## What the filters covered

The denominator is all five pairs $(d,p)$ with $p\ge5$ prime dividing $h(-d)$ among the twelve squarefree $d\equiv7\pmod{16}$ up to 199. For the seven other bases the raw log below gives each class number and all its prime divisors. Their class numbers have no prime divisor in the prescribed range. The experiment covers neither the branches $p\nmid h(-d)$ nor exponent 3.

| $d$ | $h(-d)$ | $p$ | $N=32d$ | Initial dimension | After $3$ | After $5$ | After $7$ | Surviving characters |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 71 | 7 | 7 | 2272 | 70 | 5 | 2 | skip (2) | 2 |
| 103 | 5 | 5 | 3296 | 102 | 4 | skip (4) | 3 | 3 |
| 119 | 10 | 5 | 3808 | 96 | 5 | skip (5) | skip (5) | 5 |
| 151 | 7 | 7 | 4832 | 150 | 0 | 0 | skip (0) | 0 |
| 167 | 11 | 11 | 5344 | 166 | 3 | 0 | 0 | 0 |

For each pair the displayed dimensions hold for every odd residue $x\bmod12$. The two trace sets at 5 for $d=167$ are printed separately below. For $d=119$ only $q=3$ is available because $5=p$ and $7\mid d$.

The filters give two exclusions in five pairs, or **one in four** when the previously studied 167 is held out. The 71 row is a separate check on the limits of the method. Bennett–Siksek's Theorem 1 already classifies the larger square-summand problem there. Its only entry at $(q,n)=(71,7)$ gives $46^2+71=3^7$, with exponent of 71 equal to one and 46 not a square. The two surviving modular characters therefore give a concrete example where these three primes do not capture a known obstruction. The small, arithmetically selected cohort gives no estimate for arbitrary bases or for general Beal. For a separately specified follow-up, the three lines at 103 make a smaller target than the five at 119. The known exclusion at 71 offers a way to test a proposed filter before applying it to either base. [Bennett–Siksek, Theorem 1 and its table, pp. 1–2](https://arxiv.org/pdf/2110.05553)

## From an integer solution to the tested space

Suppose $d,b,c$ are pairwise coprime positive integers, $x\ge3$ is odd and $p$ is the indicated class-number prime. If $p\mid x$, the equation gives $c^p+(-d^{x/p})^p=(b^2)^2$, a primitive nontrivial signed solution excluded by Darmon–Merel. This covers that branch for every one of the five pairs. [Darmon–Merel, Main Theorem, part 2](https://www.math.mcgill.ca/darmon/pub/Articles/Research/18.Merel/paper.pdf)

Assume $p\nmid x$. Put $D=d^x$. Then $D\equiv7\pmod{16}$, and odd $b$ would give $v_2(c^p)=3$, impossible for $p\ge5$. Hence $b$ is even and $c$ odd. For $E:Y^2=X(X^2+2b^2X+c^p)$ one has $\Delta=-64Dc^{2p}$ and $c_4=16(b^4-3D)$. At 2 the minimal discriminant has valuation 6. Translation by 1 gives $a'_4\equiv2\pmod4$, $a'_6\equiv0\pmod8$ and $b'_8\equiv4\pmod8$. Tate's algorithm gives type III and Ogg's formula gives conductor exponent $6+1-2=5$. At odd $q\mid dc$, the value of $c_4$ is a unit by primitivity. The displayed model is minimal and multiplicative there. The minimal discriminant valuation is $x$ at each $q\mid d$ since $d$ is squarefree, and $2p\,v_q(c)$ at $q\mid c$. Other odd primes are good. [Tate and Ogg calculations](frey-curve.md#conductor-and-level)

The Diamond–Kramer criterion applies to $E/\mathbb Q$ because $v_2(N_E)=5$. In particular $E$ has no rational cyclic isogeny of degree 5, 7 or 11. This supplies irreducibility for $p=5$ at 103 and 119, $p=7$ at 71 and 151, and $p=11$ at 167. Siksek's level-lowering formula deletes every $q\mid c$ and retains every $q\mid d$, including both prime factors at 119. It gives a weight-two newform of trivial character at the exact level $32d$. [Siksek, §6 Theorem 5 and §5.2 Theorem 3](https://samirsiksek.github.io/siksek.github.io/papers/ihpnotes7.pdf)

At each applied $q$ we retain $b\bmod q$ when $u=d^x+b^4$ is a $p$th power, including zero. For $u\ne0$ we count points on the good curve. For $u=0$ the tangent slopes at the node satisfy $m^2=2b^2$, with $b$ a unit. The lowered trace is $(2/q)(q+1)$. The Python replay counts the points on both types of cubic, checks tangent directions on every singular fiber, and checks the set of traces for every applied $(d,p,r,q)$. [Trace transfer and references](auxiliary-traces.md#from-a-twist-to-a-trace)

## Identifying every survivor

All ten surviving characters take values in their respective prime fields. Each has a one-dimensional simultaneous eigenspace. The following trace values uniquely identify them within the exact-level plus cuspidal newspace after reduction. Operators used for identification take every eigenvalue. They impose no extra condition on a solution.

| $(d,p)$ | Hecke characters |
|---|---|
| $(71,7)$ | $(a_3,a_5)=(3,5)$ for both. The two values of $a_7$ are 5 and 6. |
| $(103,5)$ | $(a_3,a_7)=(0,3),(2,0),(2,3)$. |
| $(119,5)$ | One line has $a_3=1$. The other four have $a_3=0$ and $(a_5,a_7)\in\{0,4\}\times\{1,4\}$. |

PARI supplies the rational plus newspace through `msnew(msinit(N,2,1))`. For a full Hecke-stable lattice at $p$, the replay evaluates its basis on every path generator with `mseval`. Let $V$ be the integral matrix whose columns are the values of the current basis. Each relation among the columns modulo $p$ yields an integral column $Vw/p$. The script normalizes a basis of relations to the identity on pivot rows and replaces the corresponding basis columns by these divisions. A step with $k$ pivots enlarges the lattice by index $p^k$. The process stops at full column rank modulo $p$, which certifies saturation in the integral path-value lattice localized at $p$. Integral modular symbols with values in the trivial module $\mathbb Z_{(p)}$ are stable under the integral Hecke correspondences. Their intersection with the rational newspace therefore gives a stable lattice there. The script checks $p$-integrality of each operator it uses. [PARI documentation for modular symbols, path generators and evaluation](https://pari.math.u-bordeaux.fr/dochtml/html/Modular_symbols.html#mseval)

A characteristic-zero newform supplies a simultaneous eigenvector in this space. Scale its coordinates at the chosen prime above $p$ so they are integral with at least one unit. Its nonzero reduction would belong to each required kernel. The ranks computed over $\mathbb F_p$ persist over residue-field extensions. For survivors the replay decomposes each nonzero tuple space by all eigenvalues of additional commuting Hecke operators in ascending prime order. On this cohort the required characteristic polynomials split linearly, and every final space is a line. All remaining Hecke operators act there by scalars, so no additional characters can share the reported identifiers.

## Reproduce the calculations

From the repository root, using Python 3.12.14 (standard library) and PARI/GP 2.17.2, run

```sh
python3 scripts/check_breadth_inputs.py cohort
python3 scripts/check_breadth_inputs.py traces
gp -q -f scripts/check_breadth_hecke.gp
gp -q -f scripts/check_breadth_151_mf.gp
```

The first two commands emit 12 class-number rows and 90 local rows (60 applied, 30 skipped). The GP log below gives the same class numbers, prime divisors and trace sets, grouping identical residues $r$. The GP verifier uses one thread, works through one level at a time and permits a stack up to 1.8 GB. In its output, `[-1]` marks a skipped trace prime, the three tuple coordinates are ordered $3,5,7$, and `saturation_index_p_power` is the exponent of $p$ in the enlargement index.

```text
class d=7 h=1 primes=[]
class d=23 h=3 primes=[3]
class d=39 h=4 primes=[2]
class d=55 h=4 primes=[2]
class d=71 h=7 primes=[7]
class d=87 h=6 primes=[2, 3]
class d=103 h=5 primes=[5]
class d=119 h=10 primes=[2, 5]
class d=151 h=7 primes=[7]
class d=167 h=11 primes=[11]
class d=183 h=8 primes=[2]
class d=199 h=9 primes=[3]
control N=11 p=5 (a3,a5)=(-1,1) dim=1
control N=11 p=7 (a3,a5)=(-1,1) dim=1
control N=11 p=11 (a3,a5)=(-1,1) dim=1
level d=71 p=7 N=2272 dim=70 saturation_index_p_power=5
  r=[1, 3, 5, 7, 9, 11] S=[[0, 3], [2, 5], [-1]] dims=[5, 2, "skip(2)"]
  character [3, 5, -1] identifiers=[[2, 0], [3, 3], [5, 5], [7, 6]] dim=1
  character [3, 5, -1] identifiers=[[2, 0], [3, 3], [5, 5], [7, 5]] dim=1
level d=103 p=5 N=3296 dim=102 saturation_index_p_power=1
  r=[1, 3, 5, 7, 9, 11] S=[[0, 2], [-1], [0, 1, 3]] dims=[4, "skip(4)", 3]
  character [0, -1, 3] identifiers=[] dim=1
  character [2, -1, 0] identifiers=[] dim=1
  character [2, -1, 3] identifiers=[] dim=1
level d=119 p=5 N=3808 dim=96 saturation_index_p_power=1
  r=[1, 3, 5, 7, 9, 11] S=[[0, 1], [-1], [-1]] dims=[5, "skip(5)", "skip(5)"]
  character [0, -1, -1] identifiers=[[2, 0], [3, 0], [5, 0], [7, 4]] dim=1
  character [0, -1, -1] identifiers=[[2, 0], [3, 0], [5, 0], [7, 1]] dim=1
  character [0, -1, -1] identifiers=[[2, 0], [3, 0], [5, 4], [7, 4]] dim=1
  character [0, -1, -1] identifiers=[[2, 0], [3, 0], [5, 4], [7, 1]] dim=1
  character [1, -1, -1] identifiers=[] dim=1
level d=151 p=7 N=4832 dim=150 saturation_index_p_power=3
  r=[1, 3, 5, 7, 9, 11] S=[[0, 2], [2, 5], [-1]] dims=[0, 0, "skip(0)"]
level d=167 p=11 N=5344 dim=166 saturation_index_p_power=1
  r=[1, 5, 9] S=[[0, 7], [0, 4], [0, 7, 8]] dims=[3, 0, 0]
  r=[3, 7, 11] S=[[0, 7], [2, 7], [0, 7, 8]] dims=[3, 0, 0]
```

The independent check at 151 constructs the newspace using the modular-forms routines `mfinit` and `mfheckemat` and recomputes its two traces at 3. Both determinants are units modulo 7, which verifies the exclusion in a second implementation of the space. Its complete standard output is

```text
level 11 control: a3=-1, a5=1
level 4832: dimension 150, traces [0, 2], det(aI-T3) mod 7 [3, 4]
```
