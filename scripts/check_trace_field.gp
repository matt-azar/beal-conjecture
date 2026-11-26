\\ PARI/GP 2.17.2. Replay with: gp -fq scripts/check_trace_field.gp
\\ GP prints interactive errors without a nonzero exit code by default.
check_trace_field() = {
  my(d=2471, p=31, previous=2, current=x, next, T, nf, etaRoot, s, w, ratio, t);
  for(i=2,p, next=x*current-2*previous; previous=current; current=next);
  T=current-90621;
  if(!polisirreducible(T), error("Reducible trace polynomial"));
  if(poldisc(T)!=p^p*(391^2*d)^15, error("Wrong polynomial discriminant"));

  \\ In Q(r), eta=r^31. The expression t recovers u/v at a zero of F.
  etaRoot=Mod(z,z^(2*p)-90621*z^p+2^p);
  s=(2*etaRoot^p-90621)/391;
  w=(1+s)/2;
  ratio=(etaRoot^2/2)^8;
  t=(ratio*(-82-w)-(-83+w))/((7+3*w)-ratio*(10-3*w));
  if(subst(T,x,etaRoot+2/etaRoot)!=0 || s^2!=-d, error("Wrong trace generator"));
  if((7+3*w)*t+w-83 != ratio*((10-3*w)*t-82-w), error("Wrong root map"));
  if(poldegree(minpoly(t))!=p, error("Root has wrong degree"));

  nf=nfinit(T);
  if(nf.sign!=[31,0] || nf.disc!=p^31*d^15 || nf.index!=391^15,
     error("Unexpected signature, discriminant or index"));
  print("signature = ",nf.sign,", field discriminant = 31^31 * 2471^15, index = 391^15");
  my(primes=[2,7,31,353,683],
     expected=[[[1,1],[1,5],[1,5],[1,5],[1,5],[1,5],[1,5]],
               [[1,1],[2,15]],[[31,1]],[[1,1],[2,15]],[[1,31]]]);
  for(i=1,#primes,
    my(ef=vecsort(apply(v->[v.e,v.f],idealprimedec(nf,primes[i]))));
    if(ef!=expected[i],error("Unexpected prime decomposition at ",primes[i]));
    print(primes[i]," ",ef));
}
iferr(check_trace_field(),e,print(e);quit(1));
