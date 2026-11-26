\\ PARI/GP 2.17.2. Run from the repository root with gp -q -f scripts/check_new_5344.gp.
default(nbthreads, 1);
default(parisizemax, 1200000000);
default(threadsizemax, 1200000000);

verify_levels() = {
  my(small = msinit(32, 2, 1), small_new = msnew(small));
  my(space = msinit(5344, 2, 1), newpart = msnew(space));
  my(T3 = mshecke(space, 3, newpart), T5 = mshecke(space, 5, newpart));
  my(T89 = mshecke(space, 89, newpart), K3, K89, image);
  if(matsize(small_new[1])[2] != 1 || mshecke(small, 5, small_new) != Mat(-2),
    error("Level 32 should have one newform with a5 = -2"));
  if(matsize(newpart[1])[2] != 166, error("Unexpected dimension at level 5344"));
  if(gcd(11, denominator(T3)*denominator(T5)*denominator(T89)) != 1,
    error("An operator fails to preserve the chosen lattice at 11"));
  T3 *= Mod(1,11); T5 *= Mod(1,11); T89 *= Mod(1,11);
  K3 = matker(T3*(T3+4));
  if(matsize(K3)[2] != 3, error("Expected dimension 3 after T3"));
  image = K3;
  foreach([-4,0,2,4], a, image = (T5-a)*image);
  if(matrank(image) != 3, error("A vector survived the combined T3,T5 test"));
  K89 = matker(T89+3);
  if(matsize(K89)[2] != 2 || matrank(T3*(T3+4)*K89) != 2,
    error("Unexpected result for the alternative T89,T3 test"));
  \\ The square summand U² allows both nonsplit and split multiplicative traces at 3.
  for(D = 2, 3,
    my(S = Set(vector(5,j,ellap(ellinit([0,2*(j-1),0,(j-1)^2+D,0],5)))));
    if(S != if(D==2, [-2,0,4], [-4,0,2]), error("Unexpected traces at 5")));
  K3 = matker(T3*(T3+4)*(T3-4));
  if(matsize(K3)[2] != 4,error("Unexpected arbitrary-square T3 kernel"));
  foreach([[-2,0,4],[-4,0,2]], S,
    image = K3;
    foreach(S,a,image=(T5-a)*image);
    if(matrank(image)!=4,error("An arbitrary-square eigensymbol survived")));
  print("Level 5344: arbitrary square, T3 kernel 4, both T5 intersections zero");
  print("Level 32: new dimension 1, a5 = -2");
  print("Level 5344: new dimension 166; T3 then T5 kernel dimensions 3, 0");
  print("Level 5344: T89 then T3 kernel dimensions 2, 0");
}

iferr(verify_levels(), failure, print(failure); quit(1));
quit(0);
