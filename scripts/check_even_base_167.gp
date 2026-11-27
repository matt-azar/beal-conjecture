\\ Even right base at 167: the Frey curve of 167^x + U^2 = c^p with x odd, U odd, c even.
\\ Replays the finite computations of docs/even-right-base-167.md.
\\ Run from the repository root:  gp -q -f scripts/check_even_base_167.gp < /dev/null
\\ Written and run with PARI/GP 2.15.4. The project pin is 2.17.2 (replay pending under C1).
default(parisize, 1000000000);

\\ Frey curve  Y^2 = X^3 + U X^2 + (C/4) X,  C = U^2 + D,  D = d^x.

\\ Traces of Frobenius at a prime l of good reduction, over all U mod l and all
\\ D = d^x mod l with x odd and C nonzero. If pw > 0 and l = 1 mod pw, C is also
\\ required to be a pw-th power. Returns the set of integers a_l.
goodtraces(d, l, pw) = {
  my(S = List(), o = znorder(Mod(d, l)), D, C);
  forstep(x = 1, 2*o, 2,
    D = Mod(d, l)^x;
    for(U = 0, l-1,
      C = U^2 + D;
      if(C == 0, next);
      if(pw && l % pw == 1 && C^((l-1)/pw) != 1, next);
      listput(S, ellap(ellinit([0, U, 0, C/4, 0]), l))));
  Set(S);
};

\\ 1 if l can divide c for some odd x, that is if -d^x is a square mod l.
canbemult(d, l) = {
  my(o = znorder(Mod(d, l)));
  forstep(x = 1, 2*o, 2, if(issquare(-Mod(d, l)^x), return(1)));
  0;
};

\\ B_l(f) = l * prod_{a good} N(a_l(f) - a) * N(a_l(f)^2 - (l+1)^2), the last
\\ factor only when l can divide c. If f arises from a solution at the prime
\\ exponent p, then p divides B_l(f) for every prime l not dividing 2d.
Bl(d, a, l) = {
  my(A = goodtraces(d, l, 0));
  l * prod(j = 1, #A, norm(a - A[j])) * if(canbemult(d, l), norm(a^2 - (l+1)^2), 1);
};

sieve(d, N, L) = {
  my(mf = mfinit([N, 2], 0), F = mfeigenbasis(mf), flds = mffields(mf), co, g);
  print("level ", N, ": newspace dimension ", mfdim(mf), ", ", #F, " Galois classes");
  for(i = 1, #F,
    co = mfcoefs(F[i], L);
    g = 0;
    forprime(l = 3, L, if(d % l == 0, next); g = gcd(g, Bl(d, co[l+1], l)));
    print("  class ", i, ": degree ", poldegree(flds[i]), ", field ", flds[i],
          ", a_2 = ", lift(co[3]), ", gcd of B_l for 3 <= l <= ", L, ": ",
          if(g, Str(factor(g)), "0")));
  [mf, F, flds];
};

\\ Residues of a_l(f) at the primes above p, and the admissible residues mod p,
\\ now with the p-th power condition on C and the sign of a multiplicative trace.
local_at(d, F, fld, p, l) = {
  my(fa = factormod(fld, p), a = mfcoefs(F, l)[l+1], S = List(), o = znorder(Mod(d, l)), D);
  S = List(apply(t -> t % p, goodtraces(d, l, p)));
  forstep(x = 1, 2*o, 2,
    D = Mod(d, l)^x;
    for(U = 0, l-1, if(U^2 + D == 0, listput(S, (kronecker(U, l)*(l+1)) % p))));
  print("  l = ", l, ": a_l(f) at the primes ", fa[,1]~, " with exponents ", fa[,2]~, " is ",
        vector(#fa[,1], j, lift(Mod(lift(a)*Mod(1, p), fa[j,1]))),
        ", admissible residues mod ", p, ": ", Set(S));
};

print("== Reduction at 2, sampled over odd x < 32 and U mod 2^14 ==");
{
  my(S = Set(), T = Set(), D0, C, E, gr);
  forstep(x = 1, 31, 2,
    D0 = 167^x % 2^14;
    forstep(U = 1, 2^14, 2,
      C = (U^2 + D0) % 2^14;
      if(C && valuation(C, 2) >= 7 && U % 4 == 1,
        E = ellinit([0, U, 0, C/4, 0]); gr = elllocalred(E, 2);
        S = setunion(S, Set([[U % 8, gr[1], ellap(E, 2)]])));
      if(valuation(C, 2) == 5 && U % 4 == 1,
        E = ellinit([0, U, 0, (C + 3*2^14)/4, 0]); gr = elllocalred(E, 2);
        T = setunion(T, Set([[gr[1], gr[2]]])))));
  print("v_2(C) >= 7, U = 1 mod 4: [U mod 8, conductor exponent, a_2] in ", S);
  print("v_2(C) = 5, U = 1 mod 4: [conductor exponent, Kodaira code] in ", T);
}

print("== Level 334 ==");
R = sieve(167, 334, 60);
print("class 6 at 7:");
local_at(167, R[2][6], R[3][6], 7, 3);
local_at(167, R[2][6], R[3][6], 7, 5);

print("== Level 1336 (p = 5 and v_2(c) = 1) ==");
R = sieve(167, 1336, 60);
print("class 1 at 5:");
local_at(167, R[2][1], R[3][1], 5, 41);

print("== Positive control: 7 + 11^2 = 2^7, level 14 ==");
sieve(7, 14, 60);
{
  my(E = ellinit([0, -11, 0, 32, 0]), F = mfeigenbasis(mfinit([14, 2], 0))[1], co = mfcoefs(F, 60), ok = 1);
  forprime(l = 3, 60, if(l != 7 && ellap(E, l) != co[l+1], ok = 0));
  print("  Frey curve of the control: conductor ", ellglobalred(E)[1], ", a_2 = ", ellap(E, 2),
        ", traces agree with the newform for 3 <= l <= 60: ", ok);
}
quit
