# Hecke traces from the two surviving twists

At the inert prime 61, the two surviving branches of $2471^x+b^4=c^{31}$ force different Frobenius traces. The branch $(x,k)\equiv(5,23)$ gives $a_{61}=-6$, and $(67,8)$ gives $a_{61}=8$, with the exponent taken modulo 124 and the trace modulo a prime $\lambda\mid31$ of the newform's coefficient field. Four more good primes force a single residue common to both branches. These conditions can be applied to a candidate eigensystem of level 79072. Each branch must use one eigensystem and the same $\lambda$ throughout. [Level lowering and Frey model](frey-curve.md) · [Integral descent](descent.md)

| Prime $q$ | $a_q(f)\bmod\lambda$, $x\equiv5$ | $a_q(f)\bmod\lambda$, $x\equiv67$ |
|---:|---|---|
| 3 | −4, 0 | −4, 0 |
| 5 | −2, 2 | −2, 2 |
| 11 | −12, −4, 0, 4 | −12, −4, 0, 4 |
| 13 | −6, −2, 2 | −6, −2, 2 |
| 17 | −2, 0, 4, 8 | −8, −6, 2, 4, 6 |
| 61 | −6 | 8 |
| 683 | −2 | −2 |
| 1117 | −2, 5 | −2, 5 |
| 1303 | −8, 9 | −8, 9 |
| 1489 | −8 | −8 |
| 1861 | −5 | −5 |
| 2357 | −13 | −13 |
| 2543 | 1, 6 | 1, 6 |
| 2729 | −6, 11 | −6, 11 |
| 3163 | 4 | 4 |

## From a twist to a trace

Write $d=2471$, $s^2=-d$, $\eta=(90621+391s)/2$. Take a prime $q\nmid 2d\cdot31$. For branch representative $x_0\in\{5,67\}$, put $a=d^{(x_0-1)/2}$ and take its prescribed $k$. The integral twist identity requires $\eta^k(b^2+a s)$ to be a 31st power in the residue algebra at $q$. If $x=x_0+124j$, write $b=d^{31j}b_0$ locally. The twisted expression acquires the 31st power factor $d^{62j}$. The substitution $X=d^{62j}X_0$, $Y=d^{93j}Y_0$ identifies the two Frey curves over $\mathbb F_q$ in the good case and preserves the node type in the bad case. Thus the table uses $x_0$ and the normalized $b_0$, denoted $b$ below.

- **Split $q$.** Choose $r$ with $r^2=-d\pmod q$. Both images under $s\mapsto r,-r$ must be 31st powers in $\mathbb F_q$, with the same $b$. Zero is allowed in either component.
- **Inert $q$.** Work in $\mathbb F_{q^2}$. With $g=\gcd(31,q^2-1)$, a nonzero $z$ is a 31st power exactly when $z^{(q^2-1)/g}=1$. Test $z=\eta^k(b^2+as)$.

For each admissible $b$ put $u=b^4+d^{x_0}\bmod q$. If $u\ne0$, the curve has good reduction. The trace is $q+1-\#E(\mathbb F_q)$ for $E:Y^2=X(X^2+2b^2X+u)$. If $u=0$, the original equation forces $q\mid c$. The reduced cubic has a node at zero with tangent slopes $\pm b\sqrt2$, and $b\ne0$ there. The semisimplified Tate-curve representation has eigenvalues $\epsilon,\epsilon q$ for arithmetic Frobenius, where $\epsilon=(2/q)$. The unramified form at the lowered level therefore has trace $\epsilon(q+1)\bmod\lambda$. For example, at 3 the two cases give $0$ and $-4$. At 683 every surviving $b$ gives the multiplicative case and the lowered trace is $-684\equiv-2\pmod{31}$. [Multiplicative local representations and level lowering, §5](https://samirsiksek.github.io/siksek.github.io/papers/ihpnotes7.pdf)

## The small inert-prime calculation

In $\mathbb F_{61^2}^\times$ the 31st powers form the subgroup of order 120. A nonzero $z$ belongs to it exactly when $z^2\in\mathbb F_{61}$, since $z^{120}=1$ is equivalent to $(z^2)^{60}=1$. For $z=U+Vs$ this reduces to $UV=0$. Write $\eta^k=h+ms$. Then $U=hb^2-dma$ and $V=mb^2+ha$.

| $(x_0,k)$ | $(a,h,m)\bmod 61$ | $b^2$ from $U=0$ or $V=0$ | Admissible $b$ | $\#E(\mathbb F_{61})$ |
|---|---|---|---|---:|
| $(5,23)$ | $(46,40,47)$ | 56 or 53 | $\pm19$ | 68 |
| $(67,8)$ | $(38,38,53)$ | 57 or 28 | $\pm22$ | 54 |

The residues 53 and 28 are nonsquares. In both branches $u\ne0$ at 61. Counting points gives the two different traces in the first paragraph.

## Primes dividing the level

At $q=7,353$ the Frey curve has multiplicative reduction and the lowered form is new of conductor exponent one. The tangent slopes are $\pm b\sqrt{-1}$, giving split sign $\epsilon_7=-1$ and $\epsilon_{353}=+1$, where $+1$ denotes split reduction. The semisimplified Frobenius traces are $\epsilon_q(q+1)$ for the curve and $a_q(f)(q+1)$ for the form. At both primes $31\nmid q+1$, so the residual signs coincide. As $a_q(f)=\pm1$ integrally, this fixes $a_7(f)=-1$, $a_{353}(f)=1$, equivalently $W_7=+1$, $W_{353}=-1$ with the normalized Atkin–Lehner operators. At 2 the whole newspace satisfies $a_2=0$ because $2^2\mid79072$. [Frey reduction](frey-curve.md) · [Atkin–Lehner eigenvalues, Theorem 8.4.7](https://kimballmartin.github.io/mfs/mfs.pdf)

## Replay

Run `python3 scripts/check_aux_traces.py` from the repository root. To inspect individual normalized residues use `python3 scripts/check_aux_traces.py --show-b 61 683`. The script accepts any auxiliary prime coprime to $2d\cdot31$. It checks the displayed table and counts each point on the good fibers using integer arithmetic. An independent PARI/GP check reproduced all 30 sets of normalized residues and all traces using `polrootsmod`, `ellap` and explicit enumeration of the 31st powers in $\mathbb F_{61^2}$. [Verifier](../scripts/check_aux_traces.py)
