\\ Frozen C3 cohort. Run with PARI/GP 2.17.2: gp -q -f scripts/check_breadth_hecke.gp
default(nbthreads, 1);
default(parisizemax, 1800000000);
default(threadsizemax, 1800000000);

allowed_traces(d, p, r, q) = {
  my(traces=List(), powers=Set(vector(q, j, (j-1)^p % q)));
  for(b=0, q-1,
    my(u=(d^r+b^4)%q, a);
    if(!setsearch(powers,u), next);
    if(u, a=ellap(ellinit([0,2*b^2,0,u,0],q)),
      if(b==0,error("singular fiber at b=0"));
      a=kronecker(2,q)*(q+1));
    listput(traces,a%p));
  Set(traces);
}

\\ Return the change from the msnew basis to the p-saturated path-value lattice.
saturated_basis(M,H,p) = {
  my(ev=mseval(M,H[1]), values=Mat(vector(#ev,j,ev[j]~)));
  my(n=#values, change=matid(n));
  if(denominator(values)!=1,error("expected integral starting path values"));
  while(1,
    my(K=matker(Mod(1,p)*values), k=#K);
    if(!k, return(change));
    my(rows=matindexrank(K)[1], replace=matid(n));
    K=lift(K*vecextract(K,rows,"..")^(-1));
    for(i=1,k,replace[,rows[i]]=K[,i]/p);
    change=change*replace; values=values*replace;
    if(denominator(values)!=1,error("nonintegral path value after saturation")));
}

hecke(M,H,change,inverse,p,q) = {
  my(A=inverse*mshecke(M,q,H)*change);
  if(denominator(A)%p==0,error("Hecke denominators at residual prime"));
  Mod(1,p)*A;
}

\\ Split by every eigenvalue of A on a stable subspace. The fixed cohort
\\ reaches rational lines. An extension-field factor fails loudly.
split_all(A,V,p) = {
  my(rows=matindexrank(V)[1], C=matsolve(vecextract(V,rows,".."),vecextract(A*V,rows,"..")));
  if(A*V!=V*C,error("subspace is not Hecke-stable"));
  my(factors=factor(charpoly(C)), result=List());
  for(i=1,matsize(factors)[1],
    my(f=factors[i,1]);
    if(poldegree(f)!=1,error("unidentified extension-field factor ",f));
    my(a=lift(-polcoef(f,0)), W=V*matker(C-a));
    listput(result,[a,W]));
  Vec(result);
}

positive_control(p) = {
  my(M=msinit(11,2,1),H=msnew(M), S=saturated_basis(M,H,p), V=Mod(1,p)*matid(#S));
  V=V*matker((hecke(M,H,S,S^(-1),p,3)+1)*V);
  V=V*matker((hecke(M,H,S,S^(-1),p,5)-1)*V);
  if(#V!=1,error("level-11 positive control failed"));
  print("control N=11 p=",p," (a3,a5)=(-1,1) dim=",#V);
}

survey(d,p) = {
  my(N=32*d,M=msinit(N,2,1), H=msnew(M), S=saturated_basis(M,H,p), inverse=S^(-1));
  my(I=Mod(1,p)*matid(#S), ops=Map(), groups=Map(), qs=[3,5,7]);
  for(i=1,#qs, my(q=qs[i]); if(2*d*p%q, mapput(ops,q,hecke(M,H,S,inverse,p,q))));
  forstep(r=1,11,2,
    my(key=vector(3,i,if(mapisdefined(ops,qs[i]),allowed_traces(d,p,r,qs[i]),[-1])), rs=[]);
    if(mapisdefined(groups,key,&rs), mapput(groups,key,concat(rs,r)), mapput(groups,key,[r])));
  print("level d=",d," p=",p," N=",N," dim=",#S," saturation_index_p_power=",-valuation(matdet(S),p));

  my(systems=Map());
  foreach(Vec(groups), key,
    my(V=I, dims=List(), blocks=[[[],I]]);
    for(i=1,3,
      my(q=qs[i], traces=key[i], A);
      if(!mapisdefined(ops,q,&A),
        listput(dims,Str("skip(",#V,")"));
        blocks=vector(#blocks,j,[concat(blocks[j][1],-1),blocks[j][2]]);
        next);
      my(image=V, candidates=List());
      foreach(traces,a,image=(A-a)*image);
      V=V*matker(image); listput(dims,#V);
      foreach(blocks,b,foreach(traces,a,
        my(W=b[2]*matker((A-a)*b[2]));
        if(#W,listput(candidates,[concat(b[1],a),W]))));
      blocks=Vec(candidates);
      if(sum(j=1,#blocks,#blocks[j][2])!=#V,error("trace decomposition failed")));
    foreach(blocks,b,mapput(systems,b[1],b[2]));
    print("  r=",mapget(groups,key)," S=",key," dims=",Vec(dims)));
  my(states=vector(#systems,j,my(key=Vec(systems)[j]);[key,[],mapget(systems,key)]));
  \\ The Sturm bound (weight 2, Gamma_0(N)) also bounds algebra generators.
  my(bound=floor(N/6*prod(i=1,#factor(N)[,1],1+1/factor(N)[i,1])));
  forprime(q=2,bound,
    if(!sum(j=1,#states,#states[j][3]>1),break);
    my(A);
    if(!mapisdefined(ops,q,&A), A=hecke(M,H,S,inverse,p,q));
    my(children=List());
    foreach(states,st,
      if(#st[3]==1,listput(children,st);next);
      foreach(split_all(A,st[3],p),part,
        listput(children,[st[1],concat(st[2],[[q,part[1]]]),part[2]])));
    states=Vec(children));
  foreach(states,st,
    if(#st[3]!=1,error("unidentified higher multiplicity at Sturm bound"));
    print("  character ",st[1]," identifiers=",st[2]," dim=1"));
}

main() = {
  if(version()!=[2,17,2],error("expected PARI/GP 2.17.2"));
  my(cohort=List(), pairs=List(), primes=List());
  forstep(d=7,199,16,
    if(!issquarefree(d),next);
    listput(cohort,d);
    my(h=qfbclassno(-d), divisors=Vec(factor(h)[,1]));
    print("class d=",d," h=",h," primes=",divisors);
    foreach(divisors,p,if(p>=5,listput(pairs,[d,p]);listput(primes,p))));
  if(Vec(cohort)!=[7,23,39,55,71,87,103,119,151,167,183,199],error("cohort mismatch"));
  foreach(Set(primes),p,positive_control(p));
  foreach(pairs,pair,survey(pair[1],pair[2]));
}
iferr(main(), failure, print(failure); quit(1));
quit(0);
