\\ PARI/GP 2.17.2. Replay with gp -fq check_trace_ideal_classes.gp.
\\ Certificates involve fractional ideals in the maximal order, without bnfinit.
unique_prime(nf,q,e,f) = {
  my(L=select(P->P.e==e && P.f==f,idealprimedec(nf,q)));
  if(#L!=1,error("Prime is not unique: ",[q,e,f]));
  return(L[1]);
}
fixed_element(z) = {
  my(v=lift(z));
  if(poldegree(v,x)>0,error("Element is not in the real subfield"));
  return(polcoef(v,0,x));
}
check_trace_ideal_classes() = {
  my(d=2471,previous=2,current=y,next);
  for(i=2,31,next=y*current-2*previous;previous=current;current=next);
  my(pol=current-90621,nf=nfinit(pol),theta=Mod(y,pol));
  my(r=Mod(x,x^2-theta*x+2),rbar=2/r,s=(2*r^31-90621)/391,w=(1+s)/2);
  my(A=fixed_element((rbar^8*(7+3*w)-r^8*(10-3*w))/s));
  my(B=fixed_element((rbar^8*(w-83)-r^8*(-82-w))/s));
  my(t=-B/A,ratio=(r^2/2)^8,leading=-12305514202952265789);
  if(r+rbar!=theta || s^2!=-d || r^31!=(90621+391*s)/2,error("Trace generator"));
  if((7+3*w)*t+w-83!=ratio*((10-3*w)*t-82-w),error("Form root"));
  if(poldegree(minpoly(t))!=31,error("Degree of the form root"));
  if(idealnorm(nf,idealadd(nf,1,t))!=1/abs(leading),error("Root denominator ideal"));

  my(P2=unique_prime(nf,2,1,1),P7=unique_prime(nf,7,1,1),P353=unique_prime(nf,353,1,1));
  if(nfmodpr(nf,t,P7)!=0 || nfmodpr(nf,t,P353)!=119,error("Local lines"));
  my(R=idealmul(nf,unique_prime(nf,7,2,15),unique_prime(nf,353,2,15)));
  my(S=idealmul(nf,P7,P353),U=idealmul(nf,unique_prime(nf,17,1,1),unique_prime(nf,23,1,1)));
  if(idealmul(nf,R,idealadd(nf,A,B))!=idealhnf(nf,256),error("Coordinate ideal"));
  if(idealmul(nf,S,idealpow(nf,R,2))!=idealhnf(nf,d),error("Ramification ideal"));
  my(kappa=fixed_element((r-rbar)/s));
  if(kappa^2!=(8-theta^2)/d,error("Real element identity"));
  if(idealmul(nf,kappa,R)!=U,error("Small norm representative"));
  if(idealnorm(nf,P2)!=2 || idealnorm(nf,U)!=391,error("Norms"));
  print("(A,B) R = (256); S R^2 = (2471); (kappa) R = P_17 P_23.");
  print("Necessary class relation: [P_2] = x [P_17 P_23].");
}
iferr(check_trace_ideal_classes(),e,print(e);quit(1));
