\\ Independent PARI/GP 2.17.2 q-expansion check of the first survey filter at 151.
default(nbthreads,1);
default(parisizemax,512000000);
default(threadsizemax,512000000);

check151() = {
  if(version() != [2,17,2], error("Expected PARI/GP 2.17.2"));
  my(C = mfinit([11,2],0));
  if(mfheckemat(C,3) != Mat(-1) || mfheckemat(C,5) != Mat(1),
     error("Level-11 positive control failed"));
  print("level 11 control: a3=-1, a5=1");
  \\ 151^r=1 in F_3, and the seventh-power map is the identity there.
  my(traces = Set(vector(3,j,my(b=j-1,u=Mod(b^4+1,3));
                    if(!u,error("Unexpected bad fiber"));
                    ellap(ellinit([0,Mod(2*b^2,3),0,u,0])))));
  if(traces != [0,2], error("Unexpected Frey traces at 3"));
  my(A = mfheckemat(mfinit([4832,2],0),3));
  if(matsize(A) != [150,150] || denominator(A)%7 == 0,
     error("Unexpected newspace dimension or denominator"));
  my(B = Mod(1,7)*A, determinants = vector(#traces,j,lift(matdet(traces[j]-B))));
  if(determinants != [3,4], error("Unexpected determinant certificate"));
  print("level 4832: dimension 150, traces ",traces,", det(aI-T3) mod 7 ",determinants);
}
iferr(check151(),failure,print(failure);quit(1));
quit(0);
