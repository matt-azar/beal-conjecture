# Two restrictions on primitive Beal solutions

A primitive solution means positive integers satisfying $A^x+B^y=C^z$ with $x,y,z\geq 3$ and $\gcd(A,B,C)=1$. A prime dividing two bases divides the third, so the bases in such a solution are pairwise coprime.

## A square summand and an 11-smooth summand

**Proposition.** If one summand is a square, the other summand must have a prime divisor at least 13.

Write the equation as $X^2+D=C^z$ with $X>0$. If $D=1$ and $X>1$, Mihăilescu’s theorem would force the two consecutive powers to be 8 and 9, but 8 is not a square. If $D=X=1$, then $C^z=2$ is impossible. Suppose now that $D>1$ and every prime dividing $D$ belongs to $S=\{2,3,5,7,11\}$. Theorem 2 of Bennett and Siksek classifies all positive coprime $X,C$ with $C^z>X^2$, $z\geq 3$ and such a difference. Their table has 1,240 triples. This external theorem supplies completeness at arbitrarily large heights. [Paper](https://doi.org/10.1090/tran/8734) · [Pinned solution table](https://github.com/samirsiksek/lebnag/blob/e8b1dab1f30487b0c38eee94b297bd88c821924f/lebesgue_nagell_solutions.txt)

For $D>1$ its largest possible exponent as a power is the gcd of its five prime multiplicities. Retain rows where this gcd is at least three, treating $D=1$ as a power of every exponent. Twelve rows survive this first test. Below are **all** distinct $X$ among them and a prime $q$ with $v_q(X)=1$.

| $X$ | 7 | 10 | 13 | 46 | 2681 | 3419 | 9324 | 36599 | 39151 | 57707 | 1549034 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| $q$ | 7 | 2 | 13 | 2 | 7 | 13 | 7 | 36599 | 17 | 13 | 2 |

The two rows with $X=13$ record $13^2+7^3=8^3=2^9$. In every row the multiplicity of $q$ in $X^2$ is two. An exponent at least three would have to divide that multiplicity. This proves the proposition. The verifier checks the input digest, distinct triples, the equation, coprimality, every listed prime multiplicity, and each exclusion witness. [Python verifier](../scripts/check_smooth.py)

## The quadratic class-number obstruction

**Proposition.** Suppose $A^3+B^4=C^\ell$ is primitive, $A$ is squarefree, and $\ell\geq 11$ is prime. Then

$$
A\equiv 15\pmod{16}\quad\text{or}\quad \ell\mid h(\mathbb Q(\sqrt{-A})),
$$

where $h$ is the ideal class number. If $C$ is even, both $A,B$ are odd and $A^3\equiv -1\pmod{16}$. Cubing is a bijection on the units modulo 16, giving the first alternative.

Suppose $C$ is odd. Write $s=\sqrt{-A}$, $K=\mathbb Q(s)$ and $\gamma=B^2+As$. Then $\gamma\bar\gamma=C^\ell$. Any common prime ideal of $(\gamma)$ and $(\bar\gamma)$ would lie over a prime dividing both $C$ and $2A$, by taking their difference. Unique factorization of integral ideals gives $(\gamma)=\mathfrak a^\ell$. If $\ell\nmid h(K)$, the class of $\mathfrak a$ is trivial. The unit group of an imaginary quadratic field has order 2, 4 or 6, so the unit factor too is an $\ell$th power. Hence $\gamma=\alpha^\ell$ for an algebraic integer $\alpha$ of norm $C$.

The ideals of $\alpha$ and $\bar\alpha$ are coprime and have norm $C>1$. Their ratio cannot be a root of unity since that would make the ideals equal. Their trace $T$ is nonzero (otherwise $\gamma+\bar\gamma=0$), and $\gcd(T,C)=1$. Indeed, an ideal above a common prime divisor of $T$ and $C$ contains at least one of $\alpha,\bar\alpha$ and therefore both. Thus they form a Lucas pair. Write $\alpha-\bar\alpha=vs$ with integer $v\ne0$. The Lucas sequence $L_n=(\alpha^n-\bar\alpha^n)/(\alpha-\bar\alpha)$ gives $vL_\ell=2A$. Each odd prime dividing $L_\ell$ divides $(\alpha-\bar\alpha)^2=-Av^2$, excluding it as a primitive divisor. If $T$ is even then $2\mid L_2=T$. Otherwise $2\mid L_3=T^2-C$. Thus 2 cannot be a primitive divisor of $L_\ell$ either.

The primitive divisor theorem of Bilu, Hanrot and Voutier supplies one at these prime indices, with a possible exception at 13 whose Lucas pair has norm 2, whereas $C$ is odd. Cohen's Theorem 6.7.11 states the small-index exceptions explicitly. This contradiction proves the second alternative. [Cohen, §6.7.4](https://swc-math.github.io/aws/2006/06CohenExtract.pdf) · [Bilu–Hanrot–Voutier](https://doi.org/10.1515/crll.2001.080)

The argument extends to odd $x\geq 3$ in place of 3 and $4\mid y$ in place of 4. Replace $As$ in $\gamma$ by $A^{(x-1)/2}s$ and $B^2$ by $B^{y/2}$. The possible odd prime divisors of $L_\ell$ still divide $A$. Raising an odd residue to an odd power is an automorphism on the units modulo 16.

For $A=167$ the class number is 11. The root ideal can therefore be nonprincipal at $\ell=11$. Retaining its ideal class produces a further exclusion. [Descent and congruence certificates](descent.md)
