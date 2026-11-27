\\ PARI/GP 2.17.2. Run with gp -fq -s 192M scripts/check_square_263_newspace.gp.
default(nbthreads, 1);
default(parisizemax, 1800000000);

check263() = {
  my(cm = mfinit([32,2],0));
  if(mfdim(cm) != 1 || mfheckemat(cm,3) != Mat(0), error("level-32 control failed"));
  print("level-32 CM control: dimension 1, T3 = 0");
  my(W = mfinit([8416,2],0), T = mfheckemat(W,3));
  my(d = mfdim(W), den = denominator(T));
  if(d != 262 || gcd(13,den) != 1, error("unexpected dimension or denominator"));
  T *= Mod(1,13);
  my(traces = [0,4,-4], dets = vector(#traces,i,lift(matdet(T-traces[i]))));
  print("level 8416: dimension ",d,", denominator mod 13 = ",den%13);
  print("traces ",traces,", determinants mod 13 ",dets);
  if(dets != [3,10,10],error("determinant mismatch"));
}

iferr(check263(),failure,print(failure);quit(1));
quit(0);
