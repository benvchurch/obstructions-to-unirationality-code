/*******************************************************************************
 * mod2_cover_twist.m
 *
 * Compute the mod-2 L-polynomial of C_twist and determine the 2-torsion field
 * of J(C_twist). Compare with J(C) where C is the Klein quartic.
 *
 * Recall: C ≅ C_twist over Q(cos(2π/7)), and L_p(C) = L_p(C_twist)
 * iff p is a cube mod 7 (p mod 7 ∈ {0,1,2,4}).
 ******************************************************************************/

Q := Rationals();
F2t<u> := PolynomialRing(GF(2));
Zt<t> := PolynomialRing(Integers());

// =============================================================================
// Compute L_p mod 2 for BOTH curves
// =============================================================================
print "=== MOD-2 L-POLYNOMIALS: C vs C_twist ===";
printf "%-5o %-6o %-8o %-24o %-24o %-6o\n",
       "p", "p%7", "cube?", "L_C mod 2", "L_tw mod 2", "same?";

for p in PrimesInInterval(3, 100) do
    if p eq 7 then continue; end if;

    Fp := GF(p);

    // --- Klein quartic C ---
    P2<xp,yp,zp> := ProjectiveSpace(Fp, 2);
    Cp := Curve(P2, xp^3*yp + yp^3*zp + zp^3*xp);
    np_C := #RationalPoints(Cp);

    Fp2 := GF(p^2);
    P22<x2,y2,z2> := ProjectiveSpace(Fp2, 2);
    Cp2 := Curve(P22, x2^3*y2 + y2^3*z2 + z2^3*x2);
    np2_C := #RationalPoints(Cp2);

    Fp3 := GF(p^3);
    P23<x3,y3,z3> := ProjectiveSpace(Fp3, 2);
    Cp3 := Curve(P23, x3^3*y3 + y3^3*z3 + z3^3*x3);
    np3_C := #RationalPoints(Cp3);

    s1 := p+1-np_C; s2 := p^2+1-np2_C; s3 := p^3+1-np3_C;
    a1_C := -s1;
    a2_C := (s1^2 - s2) div 2;
    a3_C := (-s1^3 + 3*s1*s2 - 2*s3) div 6;
    LC2 := F2t ! [GF(2)|1, a1_C, a2_C, a3_C, a2_C, a1_C, 1];

    // --- Twisted curve C_twist ---
    P2t<xt,yt,zt> := ProjectiveSpace(Fp, 2);
    ftw := xt^4 + yt^4 + zt^4 + 6*(xt*yt^3 + yt*zt^3 + zt*xt^3)
           - 3*(xt^2*yt^2 + yt^2*zt^2 + zt^2*xt^2) + 3*xt*yt*zt*(xt+yt+zt);
    Ctw := Curve(P2t, ftw);
    np_tw := #RationalPoints(Ctw);

    P2t2<xt2,yt2,zt2> := ProjectiveSpace(Fp2, 2);
    ftw2 := xt2^4 + yt2^4 + zt2^4 + 6*(xt2*yt2^3 + yt2*zt2^3 + zt2*xt2^3)
            - 3*(xt2^2*yt2^2 + yt2^2*zt2^2 + zt2^2*xt2^2) + 3*xt2*yt2*zt2*(xt2+yt2+zt2);
    Ctw2 := Curve(P2t2, ftw2);
    np2_tw := #RationalPoints(Ctw2);

    P2t3<xt3,yt3,zt3> := ProjectiveSpace(Fp3, 2);
    ftw3 := xt3^4 + yt3^4 + zt3^4 + 6*(xt3*yt3^3 + yt3*zt3^3 + zt3*xt3^3)
            - 3*(xt3^2*yt3^2 + yt3^2*zt3^2 + zt3^2*xt3^2) + 3*xt3*yt3*zt3*(xt3+yt3+zt3);
    Ctw3 := Curve(P2t3, ftw3);
    np3_tw := #RationalPoints(Ctw3);

    s1t := p+1-np_tw; s2t := p^2+1-np2_tw; s3t := p^3+1-np3_tw;
    a1_tw := -s1t;
    a2_tw := (s1t^2 - s2t) div 2;
    a3_tw := (-s1t^3 + 3*s1t*s2t - 2*s3t) div 6;
    Ltw2 := F2t ! [GF(2)|1, a1_tw, a2_tw, a3_tw, a2_tw, a1_tw, 1];

    // Classification
    p7 := p mod 7;
    is_cube := (p7 in {0,1,2,4});

    // Format factorizations
    fC := Factorization(LC2);
    ftw := Factorization(Ltw2);

    sC := "";
    for pair in fC do
        sC cat:= Sprintf("(%o)^%o", pair[1], pair[2]);
    end for;

    stw := "";
    for pair in ftw do
        stw cat:= Sprintf("(%o)^%o", pair[1], pair[2]);
    end for;

    printf "%-5o %-6o %-8o %-24o %-24o %-6o\n",
           p, p7, is_cube, sC, stw, LC2 eq Ltw2;
end for;

// =============================================================================
// Analyze the pattern for C_twist
// =============================================================================
print "\n=== PATTERN ANALYSIS FOR C_twist ===";
print "For C: L_p mod 2 = (t+1)^6 iff p ≡ ±1 mod 7";
print "";
print "For C_twist, checking which primes give (t+1)^6:";

trivial_tw := [];
nontrivial_tw := [];

for p in PrimesInInterval(3, 100) do
    if p eq 7 then continue; end if;

    Fp := GF(p);
    P2t<xt,yt,zt> := ProjectiveSpace(Fp, 2);
    ftw := xt^4 + yt^4 + zt^4 + 6*(xt*yt^3 + yt*zt^3 + zt*xt^3)
           - 3*(xt^2*yt^2 + yt^2*zt^2 + zt^2*xt^2) + 3*xt*yt*zt*(xt+yt+zt);
    Ctw := Curve(P2t, ftw);
    np_tw := #RationalPoints(Ctw);

    Fp2 := GF(p^2);
    P2t2<xt2,yt2,zt2> := ProjectiveSpace(Fp2, 2);
    ftw2 := xt2^4 + yt2^4 + zt2^4 + 6*(xt2*yt2^3 + yt2*zt2^3 + zt2*xt2^3)
            - 3*(xt2^2*yt2^2 + yt2^2*zt2^2 + zt2^2*xt2^2) + 3*xt2*yt2*zt2*(xt2+yt2+zt2);
    Ctw2 := Curve(P2t2, ftw2);
    np2_tw := #RationalPoints(Ctw2);

    Fp3 := GF(p^3);
    P2t3<xt3,yt3,zt3> := ProjectiveSpace(Fp3, 2);
    ftw3 := xt3^4 + yt3^4 + zt3^4 + 6*(xt3*yt3^3 + yt3*zt3^3 + zt3*xt3^3)
            - 3*(xt3^2*yt3^2 + yt3^2*zt3^2 + zt3^2*xt3^2) + 3*xt3*yt3*zt3*(xt3+yt3+zt3);
    Ctw3 := Curve(P2t3, ftw3);
    np3_tw := #RationalPoints(Ctw3);

    s1t := p+1-np_tw; s2t := p^2+1-np2_tw; s3t := p^3+1-np3_tw;
    a1_tw := -s1t;
    a2_tw := (s1t^2 - s2t) div 2;
    a3_tw := (-s1t^3 + 3*s1t*s2t - 2*s3t) div 6;
    Ltw2 := F2t ! [GF(2)|1, a1_tw, a2_tw, a3_tw, a2_tw, a1_tw, 1];

    is_trivial := Ltw2 eq (F2t.1 + 1)^6;
    if is_trivial then
        Append(~trivial_tw, p);
    else
        Append(~nontrivial_tw, p);
    end if;
end for;

print "Primes with L_tw mod 2 = (t+1)^6:";
print trivial_tw;
print "  Residues mod 7:", [p mod 7 : p in trivial_tw];

print "\nPrimes with L_tw mod 2 = (t+1)^2(t^2+t+1)^2:";
print nontrivial_tw;
print "  Residues mod 7:", [p mod 7 : p in nontrivial_tw];

// =============================================================================
// v_2 analysis for C_twist
// =============================================================================
print "\n=== v_2(L_tw(1)) FOR RATIONAL 2-TORSION BOUND ===";
printf "%-5o %-6o %-12o %-6o\n", "p", "p%7", "L_tw(1)", "v_2";

for p in PrimesInInterval(3, 50) do
    if p eq 7 then continue; end if;

    Fp := GF(p);
    P2t<xt,yt,zt> := ProjectiveSpace(Fp, 2);
    ftw := xt^4 + yt^4 + zt^4 + 6*(xt*yt^3 + yt*zt^3 + zt*xt^3)
           - 3*(xt^2*yt^2 + yt^2*zt^2 + zt^2*xt^2) + 3*xt*yt*zt*(xt+yt+zt);
    Ctw := Curve(P2t, ftw);
    np_tw := #RationalPoints(Ctw);

    Fp2 := GF(p^2);
    P2t2<xt2,yt2,zt2> := ProjectiveSpace(Fp2, 2);
    ftw2 := xt2^4 + yt2^4 + zt2^4 + 6*(xt2*yt2^3 + yt2*zt2^3 + zt2*xt2^3)
            - 3*(xt2^2*yt2^2 + yt2^2*zt2^2 + zt2^2*xt2^2) + 3*xt2*yt2*zt2*(xt2+yt2+zt2);
    Ctw2 := Curve(P2t2, ftw2);
    np2_tw := #RationalPoints(Ctw2);

    Fp3 := GF(p^3);
    P2t3<xt3,yt3,zt3> := ProjectiveSpace(Fp3, 2);
    ftw3 := xt3^4 + yt3^4 + zt3^4 + 6*(xt3*yt3^3 + yt3*zt3^3 + zt3*xt3^3)
            - 3*(xt3^2*yt3^2 + yt3^2*zt3^2 + zt3^2*xt3^2) + 3*xt3*yt3*zt3*(xt3+yt3+zt3);
    Ctw3 := Curve(P2t3, ftw3);
    np3_tw := #RationalPoints(Ctw3);

    s1t := p+1-np_tw; s2t := p^2+1-np2_tw; s3t := p^3+1-np3_tw;
    a1_tw := -s1t;
    a2_tw := (s1t^2 - s2t) div 2;
    a3_tw := (-s1t^3 + 3*s1t*s2t - 2*s3t) div 6;
    Ltw1 := 1 + a1_tw + a2_tw + a3_tw + p*a2_tw + p^2*a1_tw + p^3;
    v2 := Valuation(Ltw1, 2);

    printf "%-5o %-6o %-12o %-6o\n", p, p mod 7, Ltw1, v2;
end for;

quit;
