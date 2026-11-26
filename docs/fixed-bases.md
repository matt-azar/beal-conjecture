# The fourth-power summand for three fixed bases

**Theorem.** For $d\in\{167,263,2471\}$, the equation
$$
d^x+B^y=C^z,\qquad x,y,z\geq3,\qquad 4\mid y,
$$
has no positive primitive solution. Here primitivity means $\gcd(d,B,C)=1$. A prime dividing two bases divides all three. The theorem allows arbitrarily large $x,y,z,B,C$. It concerns three specified values of the first base.

Put $b=B^{y/4}$. If $3\mid z$, substitute $c=C^{z/3}$ in the cubic proofs. They treat both parities of $x$ and, for odd $x$, both parities of $c$. At 263 the final two classes require an elliptic-curve argument. [Bases 167 and 2471](right-exponent-three.md) · [Base 263](transfer-263.md#the-remaining-cubic-equation)

For the remaining cases $z\geq4$. If $x$ is even, $b^4+(d^{x/2})^2=C^z$ is excluded by Theorem 1 of Bennett–Ellenberg–Ng. It remains to treat odd $x$. Since $d\equiv7\pmod{16}$, an odd $b$ would give $C^z\equiv8\pmod{16}$. Thus $b$ is even and $C$ is odd. [Bennett–Ellenberg–Ng, Theorem 1](https://personal.math.ubc.ca/~bennett/BeElNgdraftFINAL.pdf)

**If $z$ is even.** Since $b$ is even, $C^z=d^x+b^4\equiv7\pmod8$, whereas every odd square is $1\pmod8$.

**If a prime $p\geq5$ divides $z$.** Put $c=C^{z/p}$ and $K=\mathbb Q(\sqrt{-d})$. The class numbers for $d=167,263,2471$ are 11, 13 and 62 respectively. Suppose first that $p\nmid h(K)$. The [quadratic factorization](results.md#the-quadratic-class-number-obstruction) gives
$$
\alpha^p=b^2+d^{(x-1)/2}\sqrt{-d},\qquad \alpha\in\mathcal O_K.
$$
The conjugates $\alpha,\bar\alpha$ are a Lucas pair. Their ideals are coprime with norm $c>1$, their nonzero trace is coprime to $c$, and their ratio cannot be a root of unity. Write $\alpha-\bar\alpha=v\sqrt{-d}$. Then $v L_p=2d^{(x-1)/2}$ for $L_p=(\alpha^p-\bar\alpha^p)/(\alpha-\bar\alpha)$. Every odd prime of $L_p$ divides the Lucas discriminant $-dv^2$. The prime 2 already divides $L_2$ if the trace is even and $L_3$ otherwise since $c$ is odd. This would make the pair $p$-defective, meaning that $L_p$ has no primitive prime divisor.

The primitive-divisor theorem excludes every $p>30$. At prime indices $5\leq p\leq30$, the exceptional pairs are confined to $5,7,13$. Their quadratic fields have radicands, up to rational squares, in $\{5,-7,-10,-11,-15,-19,-341\}$. The three fields in the theorem are absent from this list. This uses the classification of **Lucas** pairs. The larger list for Lehmer pairs has different exceptions. [Bilu–Hanrot–Voutier](https://doi.org/10.1515/crll.2001.080) · [Explicit Lucas table, Proposition 2.2](https://pure.mpg.de/pubman/item/item_3118723_4/component/file_3281236/Berczes-Luca-Pink-Ziegler_Trinomials%2Bwith%2Bintegral%2BS-unit%2Bcoefficients%2Bhaving%2Ba%2Bquadratic%2Bfactor_Preprint.pdf)

The only remaining pairs $(d,p)$ are $(167,11)$, $(263,13)$ and $(2471,31)$. For 167, level lowering and the traces at 3 and 5 exclude the required weight-two newform. For 263, the trace at 3 excludes level 8416 and the trace at 5 excludes level 32. For 2471, the quadratic twist forces $683\mid c$. Level lowering then requires a form at level 79072 with $a_5\equiv\pm2$ and $a_{683}\equiv-2$ modulo the same prime over 31. The exact Hecke calculation excludes both choices. This completes the proof since every $z\geq3$ is divisible by 3, by 4, or by a prime at least 5. [Exponent 11](frey-167.md) · [Exponent 13](transfer-263.md) · [Exponent 31](frey-curve.md) · [Hecke certificate](brandt-sieve.md)

## Independent verification and scope

The classical modular-symbol replay uses eclib and exact finite-field rank. On the full relative plus spaces it gives rank $676/676$ for each of the two $(T_3,T_{89})$ tests at level 5344 and rank $11336/11336$ for each of the two $(T_5,T_{683})$ tests at level 79072. It uses all rows of the first operator and 160 of the second. Full column rank on these rows implies full column rank on the complete stacked matrix. A level-11 positive control recovers a one-dimensional kernel. A modular eigensymbol over a number field can be scaled to have integral local coordinates with at least one unit, so reduction modulo the same coefficient prime preserves a nonzero vector. Extension of the residue field preserves each computed rank. [Cremona, Chapter II, §§2.1 and 2.4](https://johncremona.github.io/book/fulltext/chapter2.pdf) · [Standalone verifier and build dependencies](../scripts/check_eclib_hecke.cpp)

The arithmetic proof uses published theorems, explicit ideal arithmetic, and reproducible finite calculations. Lean presently verifies selected steps of the quadratic descent. The full fixed-base theorem awaits formalization and external review. No priority claim is made.
