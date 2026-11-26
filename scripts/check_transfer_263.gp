\\ PARI/GP 2.17.2. Run with gp -q -f scripts/check_transfer_263.gp.
default(nbthreads, 1);
default(parisizemax, 3000000000);
default(threadsizemax, 3000000000);

verify263() = {
  my(M = msinit(32*263,2,1), newpart = msnew(M));
  my(T3 = mshecke(M,3,newpart));
  if(qfbclassno(-263) != 13 || matsize(newpart[1])[2] != 262,
    error("Unexpected class number or dimension"));
  if(gcd(denominator(T3),13) != 1,error("T3 fails to preserve the lattice at 13"));
  T3 *= Mod(1,13);
  if(matrank(T3*(T3+4)) != 262,error("A new eigensymbol survived at 3"));
  M = msinit(32,2,1); newpart = msnew(M);
  if(matsize(newpart[1])[2] != 1 || mshecke(M,5,newpart) != Mat(-2),
    error("Unexpected level-32 data"));
  print("Level 8416: T3(T3+4) rank 262 of 262 modulo 13");
  print("Level 32: new dimension 1, a5 = -2");
}

iferr(verify263(), failure, print(failure); quit(1));
quit(0);
