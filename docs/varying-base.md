# Varying the base at exponent 31

**Theorem.** Put $d=2471$ and let $m,n,b,c$ be positive integers with $\gcd(dm,b)=1$. Suppose $m$ is coprime to every prime in the following set:
$$
S=\{2,5,31,683,1117,1303,1489,2357,2543,2791,3163\}.
$$
Then $d^n m^{124}+b^4=c^{31}$ is impossible. In particular this excludes every first base $A=2471u^{124}$ with $\gcd(u,\prod_{q\in S}q)=1$, for every $x\geq3$, $4\mid y$ and $31\mid z$ in $A^x+B^y=C^z$. Substitute $n=x$, $m=u^x$, $b=B^{y/4}$ and $c=C^{z/31}$.

For even $n$, the first summand is a square. Theorem 1 of Bennett–Ellenberg–Ng applies to $b^4+(d^{n/2}m^{62})^2=c^{31}$. For $31\mid n$, one can also write $c^{31}+(-d^{n/31}m^4)^{31}=(b^2)^2$ and apply the main theorem of Darmon–Merel. These are nontrivial primitive solutions in the conventions of both theorems. [Bennett–Ellenberg–Ng](https://people.math.wisc.edu/~ellenberg/BeElNgdraftFINAL.pdf) · [Darmon–Merel](https://www.math.mcgill.ca/darmon/pub/Articles/Research/18.Merel/paper.pdf)

Suppose $n$ is odd. Write $D=d^n m^{124}$. Then $D\equiv7\pmod{16}$. An odd $b$ would give $c^{31}\equiv8\pmod{16}$, impossible, so $b$ is even and $c$ is odd. Primitivity gives $\gcd(c,2dm)=1$. In $\mathbb Q(s)$, $s=\sqrt{-d}$, the conjugates of $b^2+d^{(n-1)/2}m^{62}s$ generate coprime ideals and their product is $(c)^{31}$. The quadratic descent thus gives a single $0\leq k<31$ and an integral $\beta$ with
$$
\beta^{31}=\eta^k(b^2+d^{(n-1)/2}m^{62}s).
$$
At each modulus $683,961,1117,1303,1489,2357,2543,2791,3163$, write $n=n_0+124j$ with $1\leq n_0<124$. Dividing by $(d^jm)^{62}$ rescales $b$ by $(d^jm)^{-31}$ and $\beta$ by $(d^jm)^{-2}$. These units give the original fixed-base test for $(n_0,k)$. The exhaustive intersection **including $k=0$** is $(5,23),(31,0),(67,8),(93,0)$. The two principal cases have $31\mid n$, already excluded above. This use of the principal class matters because prime divisors of $m$ could enter the Lucas sequence. [Descent](descent.md) · [Replay with the `--exponents` option](../scripts/check_twists.py)

In the other cases take $E:Y^2=X^3+2b^2X^2+c^{31}X$. Its invariants are $\Delta=-64D c^{62}$ and $c_4=16(b^4-3D)$. At 2 the same calculation gives conductor exponent 5. Each odd $q\mid D c$ is multiplicative. For $q\mid c$ the discriminant valuation is a multiple of 31. For $q\mid m$ outside $d$ it is $124v_q(m)$. These primes lower away. At $q=7,353$ it is $n+124v_q(m)\equiv5\pmod{31}$, so both remain even if they divide $m$. Mazur's theorem and level lowering again give a newform of exact level 79072. [Frey-curve proof and theorem statements](frey-curve.md)

At 5 and 683 the rescaling by $W=d^jm$ is invertible. In the normalized coordinates $b_0=b/W^{31}$ and $c_0=c/W^4$, the Frey curve for $b_0,c_0$ maps to $E$ by $X=W^{62}X_0$, $Y=W^{93}Y_0$. Consequently the good traces at 5 are $\pm2$. At 683 the twist forces $683\mid c$ and the tangents give nonsplit multiplicative reduction, hence lowered trace $-2$ modulo 31. The simultaneous Hecke calculation excludes the required newform. [Exact certificate](brandt-sieve.md)
