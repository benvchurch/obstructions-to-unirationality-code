/*
  This code can be loaded, or copied and pasted, into Magma.
  It will load the data associated to the HMF, including
  the field, level, and Hecke and Atkin-Lehner eigenvalue data.
  At the *bottom* of the file, there is code to recreate the
  Hilbert modular form in Magma, by creating the HMF space
  and cutting out the corresponding Hecke irreducible subspace.
  From there, you can ask for more eigenvalues or modify as desired.
  It is commented out, as this computation may be lengthy.
*/

P<x> := PolynomialRing(Rationals());
g := P![1, -2, -1, 1];
F<w> := NumberField(g);
ZF := Integers(F);

NN := ideal<ZF | {169, 169, -w^2 + w + 7}>;

Cl, mCl := RayClassGroup(Radical(NN), [1..3]);   
K := NumberField(AbelianExtension(mCl));
ZK := RingOfIntegers(K);

Kabs := AbsoluteField(K);
ZKabs := Integers(Kabs);

function compute_elliptic_curve()
  primesArray := [
  [7, 7, 2*w^2 - w - 3],
  [8, 2, 2],
  [13, 13, -w^2 - w + 3],
  [13, 13, -w^2 + 2*w + 2],
  [13, 13, -2*w^2 + w + 2],
  [27, 3, 3],
  [29, 29, 3*w^2 - 2*w - 4],
  [29, 29, 2*w^2 + w - 4],
  [29, 29, -w^2 + 3*w + 1],
  [41, 41, w^2 - w - 5],
  [41, 41, 2*w^2 - 3*w - 4],
  [41, 41, -3*w^2 + w + 3],
  [43, 43, w^2 + 2*w - 5],
  [43, 43, 2*w^2 + w - 5],
  [43, 43, 3*w^2 - 2*w - 3],
  [71, 71, 4*w^2 - 3*w - 5],
  [71, 71, 3*w^2 - 4*w - 5],
  [71, 71, -4*w^2 + w + 5],
  [83, 83, w^2 + w - 7],
  [83, 83, w^2 - 2*w - 6],
  [83, 83, -3*w^2 - 2*w + 5],
  [97, 97, 3*w^2 + w - 7],
  [97, 97, 3*w^2 - 4*w - 7],
  [97, 97, 2*w^2 - w - 8],
  [113, 113, 3*w^2 + w - 8],
  [113, 113, 2*w^2 - 4*w - 5],
  [113, 113, 2*w^2 + 2*w - 7],
  [125, 5, -5],
  [127, 127, 2*w^2 - 9],
  [127, 127, -3*w^2 - 2*w + 6],
  [127, 127, -5*w^2 + 3*w + 7],
  [139, 139, 5*w^2 - 4*w - 6],
  [139, 139, 4*w^2 - 5*w - 7],
  [139, 139, -5*w^2 + w + 6],
  [167, 167, w^2 + w - 8],
  [167, 167, 6*w^2 - 4*w - 9],
  [167, 167, -4*w^2 - 2*w + 7],
  [181, 181, 4*w^2 + w - 9],
  [181, 181, 4*w^2 - 5*w - 9],
  [181, 181, 2*w^2 - w - 9],
  [197, 197, 2*w - 7],
  [197, 197, 3*w^2 - 5*w - 6],
  [197, 197, 2*w^2 - 2*w - 9],
  [211, 211, 3*w^2 - 5*w - 7],
  [211, 211, 2*w^2 + 3*w - 8],
  [211, 211, 4*w^2 + w - 10],
  [223, 223, 3*w^2 + 2*w - 9],
  [223, 223, 4*w^2 + w - 11],
  [223, 223, 3*w^2 + 2*w - 10],
  [239, 239, 6*w^2 - 5*w - 7],
  [239, 239, -5*w^2 + 6*w + 9],
  [239, 239, -6*w^2 + w + 7],
  [251, 251, w^2 - 3*w - 8],
  [251, 251, -3*w^2 + 2*w - 3],
  [251, 251, 2*w^2 + w - 11],
  [281, 281, -7*w^2 + 6*w + 9],
  [281, 281, 6*w^2 + w - 11],
  [281, 281, w^2 - 7*w],
  [293, 293, -7*w^2 + 2*w + 10],
  [293, 293, 5*w^2 - 7*w - 7],
  [293, 293, 2*w^2 + 5*w - 6],
  [307, 307, -3*w^2 + w - 3],
  [307, 307, 2*w^2 - 3*w - 10],
  [307, 307, w^2 + 2*w - 10],
  [337, 337, 7*w^2 - 3*w - 10],
  [337, 337, 7*w^2 - 4*w - 10],
  [337, 337, -4*w^2 - 3*w + 8],
  [349, 349, 5*w^2 + w - 15],
  [349, 349, 7*w^2 - 8*w - 11],
  [349, 349, -6*w^2 + 5*w + 2],
  [379, 379, 3*w^2 + 3*w - 11],
  [379, 379, 4*w^2 + 2*w - 11],
  [379, 379, 5*w^2 + w - 14],
  [419, 419, -5*w^2 - 3*w + 9],
  [419, 419, 2*w^2 + w - 12],
  [419, 419, w^2 - 3*w - 9],
  [421, 421, 9*w^2 - 5*w - 15],
  [421, 421, 3*w^2 + 5*w - 7],
  [421, 421, 4*w^2 - w - 15],
  [433, 433, -8*w^2 + 7*w + 10],
  [433, 433, 7*w^2 + w - 13],
  [433, 433, w^2 - 8*w],
  [449, 449, -7*w^2 + 2*w + 8],
  [449, 449, 8*w^2 - 6*w - 11],
  [449, 449, -6*w^2 - 2*w + 11],
  [461, 461, 2*w^2 + 6*w - 7],
  [461, 461, -8*w^2 + 2*w + 11],
  [461, 461, 6*w^2 - 8*w - 9],
  [463, 463, -7*w^2 + 8*w + 12],
  [463, 463, w^2 + 7*w - 7],
  [463, 463, -8*w^2 + w + 10],
  [491, 491, w^2 + 2*w - 11],
  [491, 491, 4*w^2 - 7*w - 7],
  [491, 491, 2*w^2 - 3*w - 11],
  [503, 503, 5*w^2 - 7*w - 10],
  [503, 503, 2*w^2 - 2*w - 11],
  [503, 503, -7*w^2 + 2*w + 7],
  [547, 547, 4*w^2 + 3*w - 15],
  [547, 547, -3*w^2 + 10*w],
  [547, 547, -7*w^2 + 4*w + 3],
  [587, 587, 6*w^2 + w - 17],
  [587, 587, 5*w^2 - 3*w - 17],
  [587, 587, w^2 - 7*w - 6],
  [601, 601, 4*w^2 + 3*w - 14],
  [601, 601, 4*w^2 + 3*w - 12],
  [601, 601, 6*w^2 + w - 16],
  [617, 617, 5*w^2 + 2*w - 14],
  [617, 617, 4*w^2 + 3*w - 13],
  [617, 617, 5*w^2 + 2*w - 15],
  [631, 631, -9*w^2 + 8*w + 11],
  [631, 631, 8*w^2 + w - 15],
  [631, 631, w^2 - 9*w],
  [643, 643, 6*w^2 - 9*w - 8],
  [643, 643, 3*w^2 + 6*w - 8],
  [643, 643, 4*w^2 - w - 16],
  [659, 659, -8*w^2 + 2*w + 9],
  [659, 659, 9*w^2 - 7*w - 12],
  [659, 659, 7*w^2 + 2*w - 13],
  [673, 673, -8*w^2 + 9*w + 14],
  [673, 673, w^2 + 8*w - 8],
  [673, 673, -9*w^2 + w + 11],
  [701, 701, 9*w^2 - 4*w - 13],
  [701, 701, -5*w^2 - 4*w + 10],
  [701, 701, -4*w^2 - 5*w + 9],
  [727, 727, -7*w^2 - 3*w + 12],
  [727, 727, w^2 + 2*w - 12],
  [727, 727, 10*w^2 - 7*w - 15],
  [743, 743, 5*w^2 - 2*w - 18],
  [743, 743, 4*w^2 - 5*w - 16],
  [743, 743, w^2 + 4*w - 14],
  [757, 757, 11*w^2 - 7*w - 18],
  [757, 757, w^2 + 3*w - 13],
  [757, 757, 3*w^2 + 5*w - 15],
  [769, 769, 2*w^2 - 11*w + 1],
  [769, 769, -10*w^2 + w + 13],
  [769, 769, 9*w^2 + 2*w - 15],
  [797, 797, -8*w^2 + 5*w + 3],
  [797, 797, -3*w^2 + 11*w],
  [797, 797, 5*w^2 + 3*w - 18],
  [811, 811, -9*w^2 + 2*w + 11],
  [811, 811, 7*w^2 - 9*w - 12],
  [811, 811, 9*w^2 - 7*w - 11],
  [827, 827, 3*w^2 + 5*w - 14],
  [827, 827, 5*w^2 + 3*w - 13],
  [827, 827, 8*w^2 - 21],
  [839, 839, -6*w^2 - 4*w + 11],
  [839, 839, w^2 - 4*w - 11],
  [839, 839, 3*w^2 + w - 16],
  [853, 853, -8*w^2 + 7*w + 3],
  [853, 853, 7*w^2 + w - 20],
  [853, 853, w^2 - 8*w - 7],
  [881, 881, -10*w^2 + 9*w + 12],
  [881, 881, 9*w^2 + w - 17],
  [881, 881, w^2 - 10*w],
  [883, 883, 7*w^2 + w - 18],
  [883, 883, -8*w^2 + 5*w + 4],
  [883, 883, 5*w^2 + 3*w - 17],
  [911, 911, 10*w^2 - 7*w - 14],
  [911, 911, 2*w^2 + w - 14],
  [911, 911, -7*w^2 - 3*w + 13],
  [937, 937, -9*w^2 + 10*w + 16],
  [937, 937, w^2 + 9*w - 9],
  [937, 937, -10*w^2 + w + 12],
  [953, 953, 9*w^2 - 7*w - 10],
  [953, 953, -10*w^2 + 2*w + 13],
  [953, 953, 8*w^2 - 10*w - 13],
  [967, 967, 2*w^2 + 2*w - 15],
  [967, 967, 11*w^2 - 7*w - 17],
  [967, 967, -7*w^2 - 4*w + 12]];
  primes := [ideal<ZF | {F!x : x in I}> : I in primesArray];

  heckePol := x^2 - 12;
  Kf<e> := NumberField(heckePol);

  heckeEigenvaluesArray := [e, -1/2*e, 1, 0, -3/2*e, 2, 1/2*e, -9, 1/2*e, 2*e, 3, 3, -8, -e, -e, -6, -6, -4*e, 6, 6, 4*e, 5/2*e, -4*e, 5/2*e, -2*e, 9/2*e, -3, -1/2*e, 3*e, -2, 3*e, -16, -2*e, -2*e, 12, -5*e, 12, 13/2*e, 0, -13, 3, 3, -9/2*e, 7*e, -6*e, 4, 2*e, 16, -10, 4*e, 6, 6, -e, 18, -e, -30, 9, 6*e, -11/2*e, 21, 21, -7*e, -4, -4, 13, -13, 13, 3/2*e, -1, -14, 16, 2*e, -10, 30, 30, 30, -5/2*e, 4*e, 4*e, -15/2*e, -15/2*e, -34, 15/2*e, -11/2*e, -11/2*e, 5/2*e, -4*e, -21/2*e, 22, -4, 6*e, 3*e, 24, -10*e, -42, 36, 36, 28, -3*e, -3*e, 2*e, 2*e, 2*e, 43, -22, 17, 33, 5/2*e, -6, 34, e, 8, -32, 9*e, -32, -2*e, 11*e, -42, -2, -7/2*e, -10*e, 0, 13/2*e, 39, -26, 26, -26, -11*e, 15*e, -11*e, -25/2*e, -22, 27/2*e, 2*e, -23, -49, -14*e, 18, 12*e, -9*e, 4*e, -9*e, -7*e, -30, 48, -18, e, -18, 35, 22, 6*e, -54, 19/2*e, -7/2*e, -13*e, 26, 0, -24, -3*e, 10*e, 33/2*e, -37, 10*e, 18, -21, -21, 4*e, 32, -46];
  heckeEigenvalues := AssociativeArray();
  for i := 1 to #heckeEigenvaluesArray do
    heckeEigenvalues[primes[i]] := heckeEigenvaluesArray[i];
  end for;

  ALEigenvalues := AssociativeArray();
  ALEigenvalues[ideal<ZF | {13, 13, -w^2 + 2*w + 2}>] := -1;

  // EXAMPLE:
  // pp := Factorization(2*ZF)[1][1];
  // heckeEigenvalues[pp];

  print "To reconstruct the Hilbert newform f, type
    f, iso := Explode(make_newform());";

  function make_newform();
  M := HilbertCuspForms(F, NN);
  S := NewSubspace(M);
  // SetVerbose("ModFrmHil", 1);
  NFD := NewformDecomposition(S);
  newforms := [* Eigenform(U) : U in NFD *];

  if #newforms eq 0 then;
    print "No Hilbert newforms at this level";
    return 0;
  end if;

  print "Testing ", #newforms, " possible newforms";
  newforms := [* f: f in newforms | IsIsomorphic(BaseField(f), K) *];
  print #newforms, " newforms have the correct Hecke field";

  if #newforms eq 0 then;
    print "No Hilbert newform found with the correct Hecke field";
    return 0;
  end if;

  autos := Automorphisms(K);
  xnewforms := [* *];
  for f in newforms do;
    if K eq RationalField() then;
    Append(~xnewforms, [* f, autos[1] *]);
    else;
    flag, iso := IsIsomorphic(K,BaseField(f));
    for a in autos do;
      Append(~xnewforms, [* f, a*iso *]);
    end for;
    end if;
  end for;
  newforms := xnewforms;

  for P in primes do;
    xnewforms := [* *];
    for f_iso in newforms do;
    f, iso := Explode(f_iso);
    if HeckeEigenvalue(f,P) eq iso(heckeEigenvalues[P]) then;
      Append(~xnewforms, f_iso);
    end if;
    end for;
    newforms := xnewforms;
    if #newforms eq 0 then;
    print "No Hilbert newform found which matches the Hecke eigenvalues";
    return 0;
    else if #newforms eq 1 then;
    print "success: unique match";
    return newforms[1];
    end if;
    end if;
  end for;
  print #newforms, "Hilbert newforms found which match the Hecke eigenvalues";
  return newforms[1];

  end function;


  qqs := [qq : qq in PrimesUpTo(1000,K) | Norm(qq) + NN eq 1*ZF]; // look at primes coprime to NN
  aqqs := [];
  for qq in qqs do;
    pp := qq meet ZF;
    ppfact := Factorization(ZK!!pp);
    if #ppfact eq 1 and ppfact[1][2] eq 1 then // inert
      Append(~aqqs, heckeEigenvalues[pp]^2 - 2*Norm(pp));
    else // split or ramified
      Append(~aqqs, heckeEigenvalues[pp]);
    end if;
  end for;

  qqs := [ZKabs!!qq : qq in qqs];

  curves := [];

  for NNp in Divisors(ZKabs!!NN) do
    try
      Es := EllipticCurveSearch(ZKabs!!NNp, 20 : Primes := qqs, Traces := aqqs);
      for E in Es do
        Append(~curves, E);
      end for;
    catch e;
      print e;
    end try;
  end for;

  return curves;
end function;

function find_supersingular_prime(D, K, jE, BadPrimes) // uses Elkies's method to find a supersingular prime quickly 
  if (D mod 4) eq 1 or (D mod 4) eq 2 then
    return 0*RingOfIntegers(K);
  end if;
  PD := HilbertClassPolynomial(-D);
  R<x> := PolynomialRing(K);
  PD := R ! PD;
  fac := Factorization(Evaluate(PD, K ! jE) * RingOfIntegers(K));
  for f in fac do
    p := Factorization(AbsoluteNorm(f[1]))[1][1];
    if not (p in BadPrimes) and LegendreSymbol(-D, p) eq -1 then
      return f[1];
    end if;
  end for;
  return 0*RingOfIntegers(K);
end function;

function find_minimal_supersingular_prime(Kabs, E, badPrimes) // give a field Kabs over Q and a j-invariant jE, find the minimal supersingular prime of the elliptic curve with this j-invariant over Kabs
  bounds := [];

  for D in [1..10] do
    if (D mod 4) eq 1 or (D mod 4) eq 2 then
      continue;
    end if;
    pp := find_supersingular_prime(D,Kabs,jInvariant(E), badPrimes);
    if pp ne 0*RingOfIntegers(Kabs) then 
      Append(~bounds, pp);
    end if;
  end for;

  bound := Min([Norm(b) : b in bounds]);
  primes := PrimesUpTo(10000,Kabs);

  min := bounds[1]; 

  for pp in primes do
    if (ZKabs ! Norm(Conductor(E))) in pp then 
      continue;
    end if;
    if TraceOfFrobenius(E, pp) eq 0 then
      pp;
      Norm(pp); 
      if Norm(pp) le Norm(min) then
        min := pp;
        print min;
      end if;
    end if;
  end for;
  return min;
end function;



function print_traces(E1, E2, bound)
  pps := PrimesUpTo(bound, F);
  for pp in pps do
    if (ZF ! 2) in pp or (ZF ! 3) in pp or (ZF ! 13) in pp then
      continue;
    end if;
    qqs := Factorization(ZK!!pp); 
    print "Prime of F with norm: ", Norm(pp);
    for dat in qqs do
      qq := ZKabs !! dat[1];
      print TraceOfFrobenius(E1, qq), TraceOfFrobenius(E2, qq); 
    end for;
  end for;
  return true;
end function;

E1 := curves[1];
E2 := curves[2];

find_minimal_supersingular_prime(Kabs, E1, [2,3,13]);
print_traces(E1, E2, 100);