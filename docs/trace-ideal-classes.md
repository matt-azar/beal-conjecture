# A class group test for the degree-31 form

The two fixed-base branches of $2471^x+b^4=c^{31}$ would require a single relation in the ordinary ideal class group of the [trace field](trace-field.md). The primes in the relation have norms 2, 17 and 23. The modular-form exclusion settles these branches independently. The relation records an alternative for collaborators investigating related forms.

Write $d=2471$ and $h=(x-1)/2$. For $q=2,7,17,23,353$, let $P_q$ be the unique prime in $E$ with ramification index and residue degree both one. For $q=7,353$, let $Q_q$ be the other prime, with ramification index 2 and residue degree 15. Put $R=Q_7Q_{353}$, $S=P_7P_{353}$ and $U=P_{17}P_{23}$. Then a necessary condition is

$$[P_2]=x[U]\quad\text{in }\mathrm{Cl}(E).$$

## From a form value to a fractional ideal

Use the [trace-field generators](trace-field.md) $r,\bar r=2/r$, $s=\sqrt{-d}$ and $w=(1+s)/2$. Write $L_1=7+3w$, $L_2=w-83$ and define

$$A_i=(\bar r^8L_i-r^8\bar L_i)/s,\qquad t=-A_2/A_1,\qquad J=(1,t).$$

Conjugation fixes the $A_i$. The element $t$ satisfies the root equation for $F(T,1)$ in the [Thue–Mahler reduction](thue-mahler.md). If $a=F(1,0)$, then $F(u,v)=aN_{E/\mathbf Q}(u-vt)$. Direct arithmetic in the maximal order gives

$$N(J)=1/|a|,\quad (A_1,A_2)R=(256),\quad SR^2=(d),\quad (\kappa)R=U,\qquad \kappa=(r-\bar r)/s.$$

Here $(A_1,A_2)= (A_1)J$ and $\kappa^2=(8-(r+\bar r)^2)/d$. The [PARI verifier](../scripts/check_trace_ideal_classes.gp) compares the fractional ideals in Hermite normal form.

For a primitive pair in either branch, $I=(u-vt)J^{-1}$ is integral with norm $|F(u,v)|=2d^h$. Its part above 2 must therefore be $P_2$. At $q=7,353$, the denominator ideal is trivial locally because $J$ contains 1 and $q\nmid a$. The reduction of $t$ at $P_q$ is the admissible simple root of $F(T,1)$, respectively 0 and 119. The required slope $u/v$ lies in that root class. Under $E\hookrightarrow E_{P_q}=\mathbf Q_q$, the other polynomial factor after dividing $F(T,1)$ by $T-t$ is a unit at $u/v$. Therefore $v_{P_q}(u-vt)=h$, using that $v$ is a unit at $q$. The norm leaves no further contributions. Consequently $I=P_2 S^h$.

The class of $J$ is $-[R]$, while $[S]=-2[R]$ and $[R]=[U]$. Taking classes of $I$ gives the claimed identity.

## What a class computation would decide

In $\mathrm{Cl}(E)/\langle124[U]\rangle$, compare $[P_2]$ with $5[U]$ and $67[U]$. Failure of either equality excludes its entire exponent progression. If a class equality holds, recovering the form solutions still requires the equation in units and the original square condition on $b^2$. The totally real degree-31 field has unit rank 30. This makes the route a lower priority for this example after the Hecke test.

Run `gp -fq scripts/check_trace_ideal_classes.gp` from the repository root. It verifies the generator, the two local reductions, the denominator norm and the three ideal identities. The class orders and a basis of units remain uncomputed.
