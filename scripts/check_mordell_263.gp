\\ Verify the rank and the denominator obstruction on Y^2 = X^3 - 263^5.
\\ Run with gp -fq scripts/check_mordell_263.gp (PARI/GP 2.17.2).
check_mordell() = {
  my(E = ellinit([0, -263^5]), R = ellrankinit(E));
  my(P = [133402841906728032413158874135959681634586 / 12140590446948261961816879461062114089,
          11065419309148454640078300299083598074536290899383440509590667 / 42301884310304561148887123782350796214945389469072004437]);
  my(q = 26723, m = 26724, witnesses = [[2,5,6,2,0], [3,5,6,3,3], [17,101,102,73,99], [131,1571,1572,1439,851]]);

  if (#R[3] != 1 || R[3][1].disc != -1867563 || bnfcertify(R[3][1]) != 1,
      error("Failed to certify the cubic field used by ellrankinit"));
  my(rank_data = ellrank(R), torsion = elltors(E));
  if (rank_data[1] != 1 || rank_data[2] != 1 || torsion[1] != 1,
      error("Expected rank one and trivial torsion"));
  if (!ellisoncurve(E,P) || !isprime(q) || E.disc % q == 0 || valuation(P[1],q) != -2,
      error("Expected a rational point reducing to the identity at a good prime"));
  if (ellcard(E,q) != m || m != 2^2*3*17*131, error("Wrong reduction group order"));
  print("Certified cubic field; rank bounds ", rank_data[1], ",", rank_data[2], "; torsion order ", torsion[1]);
  print("Good prime ",q,", group order ",m,", X-coordinate valuation ",valuation(P[1],q));
  for (i = 1, #witnesses,
    my(w = witnesses[i], l = w[1], r = w[2], card = w[3]);
    if (!isprime(l) || !isprime(r) || E.disc % r == 0 || denominator(P[1]) % r == 0 ||
        ellcard(E,r) != card || card % l != 0, error("Invalid witness prime or order"));
    my(F = ellinit([0, Mod(-263^5,r)]), Q = ellmul(F, Mod(1,r)*P, card/l));
    if (lift(Q) != [w[4],w[5]], error("Incorrect nonidentity multiple"));
    print("l=",l," r=",r," order=",card," witness=",lift(Q));
  );
};
iferr(check_mordell(), e, print(e); quit(1));
