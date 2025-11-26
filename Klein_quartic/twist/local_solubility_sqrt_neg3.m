/* Check local solubility of C_twist over K = Q(sqrt(-3))

   For each rational prime p:
   - If p splits in K: completions are Q_p, need C_twist(Q_p) ≠ ∅
     => sufficient to find a smooth F_p-point (Hensel)
   - If p is inert in K: completion is unram. quad. ext. of Q_p, residue field F_{p^2}
     => sufficient to find a smooth F_{p^2}-point
   - If p ramifies (p=3): completion has residue field F_3
     => sufficient to find a smooth F_3-point
   - If p=7 (bad reduction): need careful analysis
*/

Q := Rationals();
P2<x,y,z> := ProjectiveSpace(Q, 2);
g := x^4 + y^4 + z^4 + 6*(x*y^3 + y*z^3 + z*x^3)
     - 3*(x^2*y^2 + y^2*z^2 + z^2*x^2) + 3*x*y*z*(x+y+z);
C_twist := Curve(P2, g);

print "=== LOCAL SOLUBILITY OF C_twist OVER Q(sqrt(-3)) ===\n";

// Discriminant of Q(sqrt(-3)) is -3, so only p=3 ramifies
// KroneckerSymbol(-3, p) = 1 means splits, -1 means inert, 0 means ramifies

print "=== GOOD REDUCTION PRIMES ===";
for p in PrimesUpTo(200) do
    if p eq 7 then continue; end if;  // handle separately

    kron := KroneckerSymbol(-3, p);
    Cp := ChangeRing(C_twist, GF(p));
    smooth := IsNonsingular(Cp);
    np := #RationalPoints(Cp);

    if kron eq 0 then
        // p=3, ramifies. Residue field F_3.
        split_str := "ramifies";
        res_size := p;
        nres := np;
        // Check if there's a smooth point
        pts := RationalPoints(Cp);
        has_smooth := exists{P : P in pts | IsNonsingular(P)};
    elif kron eq 1 then
        // splits. Residue field F_p.
        split_str := "splits  ";
        res_size := p;
        nres := np;
        pts := RationalPoints(Cp);
        has_smooth := exists{P : P in pts | IsNonsingular(P)};
    else
        // inert. Residue field F_{p^2}.
        split_str := "inert   ";
        res_size := p^2;
        Cp2 := ChangeRing(C_twist, GF(p^2));
        nres := #RationalPoints(Cp2);
        pts2 := RationalPoints(Cp2);
        has_smooth := exists{P : P in pts2 | IsNonsingular(P)};
    end if;

    status := has_smooth select "OK (smooth lift)" else "** NEEDS ATTENTION **";

    if not has_smooth then
        printf "p=%3o %o: #C(F_%o)=%3o, #C(res)=%3o — %o\n",
               p, split_str, p, np, nres, status;
    end if;

    // Only print problematic primes or first few
    if p le 30 or not has_smooth then
        printf "p=%3o %o: #C(F_%o)=%3o, #C(res)=%3o — %o\n",
               p, split_str, p, np, nres, status;
    end if;
end for;

print "\n=== BAD REDUCTION AT p=7 ===";
// C_twist has bad reduction at 7. We need to analyze this carefully.
F7 := GF(7);
R7<x,y,z> := PolynomialRing(F7, 3);
g7 := x^4 + y^4 + z^4 + 6*(x*y^3 + y*z^3 + z*x^3)
      - 3*(x^2*y^2 + y^2*z^2 + z^2*x^2) + 3*x*y*z*(x+y+z);
print "g mod 7 =", g7;

// Check: does g factor nicely mod 7?
// 6 ≡ -1, -3 ≡ 4, 3 ≡ 3 mod 7
// g7 = x^4 + y^4 + z^4 - (x*y^3 + y*z^3 + z*x^3) + 4*(x^2*y^2 + y^2*z^2 + z^2*x^2) + 3*x*y*z*(x+y+z)
print "Factoring g mod 7 in polynomial ring:";

P27<x,y,z> := ProjectiveSpace(F7, 2);
C7 := Curve(P27, g7);
print "Irreducible components:";
comps := IrreducibleComponents(C7);
for i in [1..#comps] do
    printf "  Component %o: degree %o, %o\n", i, Degree(comps[i]), DefiningPolynomials(comps[i]);
end for;

pts7 := RationalPoints(C7);
print "#C_twist(F_7) =", #pts7;
if #pts7 gt 0 then
    print "Points:", pts7;
    for P in pts7 do
        print "  Point", P, "smooth?", IsNonsingular(P);
    end for;
end if;

// Also check over F_49 since 7 could be inert or split in Q(sqrt(-3))
print "\nKroneckerSymbol(-3, 7) =", KroneckerSymbol(-3, 7);
// -3 mod 7: (-3/7) = ?
// 7 ≡ 1 mod 3, so by quadratic reciprocity / direct computation:
// -3 is a QR mod 7 iff 7 ≡ 1 mod 3 (which it does), so (-3/7) = 1
// So 7 SPLITS in Q(sqrt(-3))
print "=> 7 splits in Q(sqrt(-3))";
print "=> completions at primes above 7 are Q_7";
print "=> we need C_twist(Q_7) ≠ ∅";

// For the bad-reduction case, smooth F_7-points lift by Hensel.
// If all F_7-points are singular, we need to do more work.

print "\n=== DETAILED p=7 ANALYSIS ===";
// The reduction mod 7 splits into a line and a cubic, so the singular locus
// is positive-dimensional (intersection points). Check which F_7-points are smooth.

smooth_pts := [P : P in pts7 | IsNonsingular(P)];
sing_count := #pts7 - #smooth_pts;
print "Smooth F_7-points:", #smooth_pts;
print "Singular F_7-points:", sing_count;

if #smooth_pts gt 0 then
    print "=> Hensel's lemma gives Q_7-points from any smooth F_7-point";
    print "=> LOCAL SOLUBILITY AT 7: OK";
    print "Example smooth points:";
    for P in smooth_pts do
        print "  ", P;
    end for;
else
    print "=> All F_7-points are singular. Need further analysis (blowup/lifting).";
end if;

// === ALSO: Check solubility at the infinite place ===
print "\n=== ARCHIMEDEAN PLACE ===";
print "Q(sqrt(-3)) has one complex place (since disc < 0)";
print "=> C_twist(C) is always nonempty for a smooth projective curve";
print "=> No archimedean obstruction.";

// === Also do a direct search for small-height points over Q(sqrt(-3)) ===
print "\n=== DIRECT POINT SEARCH OVER Q(sqrt(-3)) ===";
K<w> := QuadraticField(-3);
OK := RingOfIntegers(K);
P2K<x,y,z> := ProjectiveSpace(K, 2);
CK := Curve(P2K, x^4 + y^4 + z^4 + 6*(x*y^3 + y*z^3 + z*x^3)
             - 3*(x^2*y^2 + y^2*z^2 + z^2*x^2) + 3*x*y*z*(x+y+z));

// Search with small coordinates: a + b*w where a, b in [-B..B]
B := 5;
print "Searching with coordinate bound", B, "...";
found := false;
count := 0;
for a1 in [-B..B] do
for b1 in [-B..B] do
for a2 in [-B..B] do
for b2 in [-B..B] do
for a3 in [-B..B] do
for b3 in [0..B] do  // can assume one coord has b >= 0 by projective scaling
    p1 := a1 + b1*w;
    p2 := a2 + b2*w;
    p3 := a3 + b3*w;
    if p1 eq 0 and p2 eq 0 and p3 eq 0 then continue; end if;

    val := p1^4 + p2^4 + p3^4 + 6*(p1*p2^3 + p2*p3^3 + p3*p1^3)
           - 3*(p1^2*p2^2 + p2^2*p3^2 + p3^2*p1^2) + 3*p1*p2*p3*(p1+p2+p3);
    if val eq 0 then
        printf "POINT FOUND: (%o : %o : %o)\n", p1, p2, p3;
        found := true;
    end if;
    count +:= 1;
end for;
end for;
end for;
end for;
end for;
end for;
printf "Searched %o projective triples.\n", count;
if not found then
    print "No points found with this height bound.";
end if;

// === Summary ===
print "\n=== SUMMARY ===";
print "For C_twist over Q(sqrt(-3)):";
print "  - p=2: inert in Q(sqrt(-3)). Need #C_twist(F_4) > 0 for Hensel.";
C4 := ChangeRing(C_twist, GF(4));
n4 := #RationalPoints(C4);
printf "    #C_twist(F_4) = %o => %o\n", n4, n4 gt 0 select "OK" else "OBSTRUCTION";

print "  - p=3: ramifies in Q(sqrt(-3)). Need smooth F_3-point for Hensel.";
C3 := ChangeRing(C_twist, GF(3));
pts3 := RationalPoints(C3);
smooth3 := [P : P in pts3 | IsNonsingular(P)];
printf "    #C_twist(F_3) = %o, #smooth = %o => %o\n", #pts3, #smooth3,
       #smooth3 gt 0 select "OK" else "NEEDS MORE WORK";

print "  - p=7: bad reduction, splits in Q(sqrt(-3)). Need C_twist(Q_7) ≠ ∅.";
print "    (See detailed analysis above)";
print "  - All other primes: checked up to 200.";

quit;
