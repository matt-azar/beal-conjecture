\\ Independent replay with PARI/GP 2.17.2. The plus modular symbols give
\\ one copy of each weight-two newform. On a simple constituent the
\\ characteristic polynomial of T_l gives the full coefficient-field norm.

pointtrace(u, c, l) = -sum(z=0, l-1, kronecker(z*(4*z^2+4*u*z+c), l));
\\ Multiplying the cubic by 4 preserves its quadratic character.

fibres(d, l, p=0) = {
  my(traces=List(), mult=List(), powers=Set(vector(l, k, (k-1)^max(1,p) % l)));
  my(odd=Set(vector(l-1, k, lift(Mod(d,l)^(2*k-1)))));
  foreach(odd, D, for(u=0, l-1,
    my(c=(u^2+D) % l);
    if(c==0, listput(mult,kronecker(u,l)*(l+1)),
      if(setsearch(powers,c), listput(traces,pointtrace(u,c,l))))));
  [Set(traces),Set(mult)];
};

residues(d,l,p) = Set(apply(a->a%p,concat(fibres(d,l,p))));
orbit_gcd(M,H,ells,localdata) = {
  my(g=0);
  for(j=1,#ells,
    my(l=ells[j], F=charpoly(mshecke(M,l,H)), localrow=localdata[j]);
    my(b=l*prod(i=1,#localrow[1],subst(F,x,localrow[1][i])));
    if(#localrow[2], b*=subst(F,x,l+1)*subst(F,x,-l-1));
    g=gcd(g,b));
  g;
};

\\ A simultaneous eigenpair (a,b) modulo a fixed prime over p must
\\ pass the characteristic polynomial test for every T_l + k*T_m.
possible_pairs(A,B,p) = {
  my(pols=vector(p,i,charpoly(A+(i-1)*B)), pairs=List());
  for(a=0,p-1,for(b=0,p-1,
    if(sum(i=1,p,subst(pols[i],x,a+(i-1)*b)%p != 0)==0,listput(pairs,[a,b]))));
  Vec(pairs);
};

replay(d,N) = {
  my(M=msinit(N,2,1), S=mssplit(M), ells=select(l->d%l && l>2, primes([2,60])));
  my(data=apply(l->fibres(d,l),ells), rows=List());
  foreach(S,H,
    my(n=msdim(H), T2=mshecke(M,2,H), a2=T2[1,1], g=orbit_gcd(M,H,ells,data));
    if(T2!=a2*matid(n),error("U_2 is not scalar"));
    listput(rows,[n,a2,g]);
    if(N==334 && (g==0 || #select(p->p>=11,factor(g)[,1])), error("unexpected large prime"));
    if(N==334 && g%5==0 && (a2+1)%5==0, error("mod 5 nonsplit survivor"));
    if(N==334 && g%7==0,
      my(pairs=possible_pairs(mshecke(M,3,H),mshecke(M,5,H),7));
      my(local3=residues(d,3,7), local5=residues(d,5,7));
      print("mod 7 candidate (T3,T5) pairs = ",pairs);
      print("admissible mod 7 at 3 and 5 = ",[local3,local5]);
      if(select(t->setsearch(local3,t[1]) && setsearch(local5,t[2]),pairs)!=[],
        error("survivor mod 7")));
    if(N==1336 && g%5==0,
      my(F=charpoly(mshecke(M,41,H)), roots=select(a->subst(F,x,a)%5==0,[0..4]));
      my(local41=residues(d,41,5));
      print("mod 5 roots of T41 = ",roots,", admissible = ",local41);
      if(#setintersect(roots,local41),error("survivor mod 5")));
    if(N==14,
      if(g!=0 || a2!=-1,error("control sieve failed"));
      foreach(ells,l,if(mshecke(M,l,H)[1,1]!=pointtrace(-11,128,l),
        error("control trace mismatch at ",l)))));
  print("level ",N," sorted [degree, a2, gcd] = ",vecsort(Vec(rows)));
};

run() = {
  print("PARI/GP ",version());
  print("newspace dimensions at 2 and 8 = ",apply(N->msdim(msnew(msinit(N,2,1))),[2,8]));
  replay(167,334);
  replay(167,1336);
  replay(7,14);
};
iferr(run(), err, { print(err); quit(1); });
quit
