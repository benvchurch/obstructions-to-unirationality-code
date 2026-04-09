/*******************************************************************************
 * brauer_obstruction2.m
 *
 * Verify the Fermat quartic x^4+y^4+z^4=0 gives a nonzero Brauer obstruction.
 *
 * Key facts:
 *   - C(R) = empty => no odd-degree closed points
 *   - J[2](Q) ≅ (Z/2Z)^3 (from 2-rank computation)
 *   - 2-torsion field = Q(zeta_8)
 *
 * Now: verify J(C) ≅ E_i^3 where E_i: y^2 = x^3-x, and analyze the
 * Brauer obstruction delta: J[2](Q) -> Br(Q)[2].
 ******************************************************************************/

// =============================================================================
// STEP 1: Compare J(C)(F_p) with E_i(F_p)^3
// =============================================================================
print "=== COMPARING J(C) WITH E_i^3 ===";
print "E_i: y^2 = x^3 - x  (CM by Z[i], conductor 32)";

E := EllipticCurve([0, 0, 0, -1, 0]); // y^2 = x^3 - x
printf "E_i: %o\n", aInvariants(E);
cm, d := HasComplexMultiplication(E);
printf "CM discriminant: %o\n", d;
Etors := TorsionSubgroup(E);
printf "E_i(Q)_tors: %o\n", Invariants(Etors);
printf "E_i[2](Q) = (Z/2Z)^2: points (0,0), (1,0), (-1,0)\n";

// Compare #J(F_p) = L_C(1) with #E(F_p)^3
print "\n--- Point count comparison ---";
printf "%-5o %-10o %-10o %-10o %-6o\n", "p", "#J(Fp)", "#E(Fp)^3", "ratio", "match?";

for p in [3, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61] do
    Fp := GF(p);

    // E_i over F_p
    Ep := ChangeRing(E, Fp);
    nE := #Ep;

    // C over F_p, F_{p^2}, F_{p^3}
    P2p<xp,yp,zp> := ProjectiveSpace(Fp, 2);
    Cp := Curve(P2p, xp^4 + yp^4 + zp^4);
    np := #RationalPoints(Cp);

    Fp2 := GF(p^2);
    P2p2<xp2,yp2,zp2> := ProjectiveSpace(Fp2, 2);
    Cp2 := Curve(P2p2, xp2^4 + yp2^4 + zp2^4);
    np2 := #RationalPoints(Cp2);

    Fp3 := GF(p^3);
    P2p3<xp3,yp3,zp3> := ProjectiveSpace(Fp3, 2);
    Cp3 := Curve(P2p3, xp3^4 + yp3^4 + zp3^4);
    np3 := #RationalPoints(Cp3);

    s1 := p + 1 - np;
    s2 := p^2 + 1 - np2;
    s3 := p^3 + 1 - np3;
    a1 := -s1;
    a2 := (s1^2 - s2) div 2;
    a3 := (-s1^3 + 3*s1*s2 - 2*s3) div 6;
    Lp1 := 1 + a1 + a2 + a3 + p*a2 + p^2*a1 + p^3;

    nE3 := nE^3;
    same := (Lp1 eq nE3);

    printf "%-5o %-10o %-10o %-10o %-6o\n", p, Lp1, nE3, Lp1/nE3, same;
end for;

// =============================================================================
// STEP 2: L-polynomial comparison L_C(t) vs L_E(t)^3
// =============================================================================
print "\n=== L-POLYNOMIAL FACTORIZATION ===";
Zt<t> := PolynomialRing(Integers());

for p in [3, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43] do
    Fp := GF(p);

    // E
    Ep := ChangeRing(E, Fp);
    nE := #Ep;
    aE := p + 1 - nE;
    LE := 1 - aE*t + p*t^2;

    // C
    P2p<xp,yp,zp> := ProjectiveSpace(Fp, 2);
    Cp := Curve(P2p, xp^4 + yp^4 + zp^4);
    np := #RationalPoints(Cp);

    Fp2 := GF(p^2);
    P2p2<xp2,yp2,zp2> := ProjectiveSpace(Fp2, 2);
    Cp2 := Curve(P2p2, xp2^4 + yp2^4 + zp2^4);
    np2 := #RationalPoints(Cp2);

    Fp3 := GF(p^3);
    P2p3<xp3,yp3,zp3> := ProjectiveSpace(Fp3, 2);
    Cp3 := Curve(P2p3, xp3^4 + yp3^4 + zp3^4);
    np3 := #RationalPoints(Cp3);

    s1 := p + 1 - np;
    s2 := p^2 + 1 - np2;
    s3 := p^3 + 1 - np3;
    a1 := -s1;
    a2 := (s1^2 - s2) div 2;
    a3 := (-s1^3 + 3*s1*s2 - 2*s3) div 6;
    LC := 1 + a1*t + a2*t^2 + a3*t^3 + p*a2*t^4 + p^2*a1*t^5 + p^3*t^6;

    same := (LC eq LE^3);
    printf "p=%-3o (mod8=%-1o): L_C = L_E^3? %-5o", p, p mod 8, same;
    if not same then
        fac := Factorization(LC);
        printf "  L_C = ";
        for pair in fac do
            printf "(%o)^%o ", pair[1], pair[2];
        end for;
        printf "\n                    L_E = %o,  L_E^3 = %o", LE, LE^3;
    end if;
    printf "\n";
end for;

// =============================================================================
// STEP 3: Explicit 2-torsion analysis
// The 2-torsion of E_i: y^2 = x^3-x is {O, (0,0), (1,0), (-1,0)}
// If J(C) ≅ E_i^3 over Q, then J[2](Q) ≅ E_i[2](Q)^3 = ((Z/2Z)^2)^3 = (Z/2Z)^6
// But we computed J[2](Q) ≅ (Z/2Z)^3, so J(C) ≇ E_i^3 over Q!
// The isogeny is only defined over a larger field.
// =============================================================================
print "\n=== 2-TORSION FIELD ANALYSIS ===";
print "E_i[2](Q) = (Z/2Z)^2 (full 2-torsion rational on E_i)";
print "If J ≅ E_i^3 over Q, we'd have J[2](Q) = (Z/2Z)^6";
print "But J[2](Q) = (Z/2Z)^3 (from 2-rank computation)";
print "So the isogeny J(C) ≅ E_i^3 is NOT defined over Q.";
print "";
print "2-torsion field of J(C) = Q(zeta_8) (from 2-rank pattern mod 8)";
print "Galois group Gal(Q(zeta_8)/Q) = (Z/8Z)* = (Z/2Z)^2 (Klein 4-group)";
print "J[2](Q) = (Z/2Z)^3 = fixed subspace of (Z/2Z)^6 under (Z/2Z)^2 action";

// =============================================================================
// STEP 4: Brauer obstruction analysis
// =============================================================================
print "\n=== BRAUER OBSTRUCTION ===";
print "For C: x^4+y^4+z^4 = 0 (Fermat quartic):";
print "  - C(R) = empty => no odd-degree closed points";
print "  - J[2](Q) = (Z/2Z)^3 != 0";
print "  - Exact sequence: J[2](Q) ->^delta Br(Q)[2]";
print "";
print "LOCAL ANALYSIS:";
print "  At v=infinity: C(R)=empty, so the local sequence doesn't split.";
print "  The local obstruction delta_infty: J[2](Q) -> Br(R)[2] = Z/2Z";
print "  might be nonzero.";
print "";

// Check: which primes p have C(Q_p) = empty?
// C(F_p) = 0 at p=5,29,... These give C(Q_p) = empty.
print "  Primes p with C(F_p) = 0 (hence C(Q_p) = empty):";
bad_primes := [];
for p in PrimesInInterval(2, 200) do
    Fp := GF(p);
    P2<x,y,z> := ProjectiveSpace(Fp, 2);
    C := Curve(P2, x^4 + y^4 + z^4);
    if #RationalPoints(C) eq 0 then
        Append(~bad_primes, p);
    end if;
end for;
print "  ", bad_primes;
print "  Residues mod 8:", [p mod 8 : p in bad_primes];
print "";
print "  So C(Q_p) = empty for these p. At these places, the local";
print "  spectral sequence also doesn't split, giving potential local obstructions.";

// =============================================================================
// STEP 5: Check the mod-2 pattern more carefully
// For each p, compute L_C mod 2 factorization
// =============================================================================
print "\n=== L_C(t) MOD 2 ===";
F2t<u> := PolynomialRing(GF(2));

for p in [3, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97] do
    Fp := GF(p);
    P2p<xp,yp,zp> := ProjectiveSpace(Fp, 2);
    Cp := Curve(P2p, xp^4 + yp^4 + zp^4);
    np := #RationalPoints(Cp);

    Fp2 := GF(p^2);
    P2p2<xp2,yp2,zp2> := ProjectiveSpace(Fp2, 2);
    Cp2 := Curve(P2p2, xp2^4 + yp2^4 + zp2^4);
    np2 := #RationalPoints(Cp2);

    Fp3 := GF(p^3);
    P2p3<xp3,yp3,zp3> := ProjectiveSpace(Fp3, 2);
    Cp3 := Curve(P2p3, xp3^4 + yp3^4 + zp3^4);
    np3 := #RationalPoints(Cp3);

    s1 := p + 1 - np;
    s2 := p^2 + 1 - np2;
    s3 := p^3 + 1 - np3;
    a1 := -s1;
    a2 := (s1^2 - s2) div 2;
    a3 := (-s1^3 + 3*s1*s2 - 2*s3) div 6;

    LC2 := F2t ! [GF(2)|1, a1, a2, a3, a2, a1, 1];
    fac2 := Factorization(LC2);

    sC := "";
    for pair in fac2 do
        sC cat:= Sprintf("(%o)^%o", pair[1], pair[2]);
    end for;

    printf "p=%-3o (mod8=%-1o): L_C mod 2 = %o\n", p, p mod 8, sC;
end for;

// =============================================================================
// STEP 6: Try to detect the obstruction by comparing covers over F_p
// For each 2-torsion point P in J[2](Q), the unramified double cover
// D_P -> C has genus 5. If D_P descends to Q, then #D_P(F_p) should
// satisfy Weil bounds for a genus 5 curve and have consistent L-poly.
//
// The 2-torsion of J(F_p) gives the double covers of C/F_p.
// We compute these and check for consistency.
// =============================================================================
print "\n=== UNRAMIFIED DOUBLE COVERS OVER F_p ===";
print "For each p, the unramified Z/2Z-covers of C/F_p correspond to";
print "elements of J(F_p)[2] / (identity). The number of such covers is";
print "2^(2-rank) - 1.";
print "";

for p in [3, 7, 11, 13, 17] do
    Fp := GF(p);
    Fpt<tp> := FunctionField(Fp);
    Fptu<up> := PolynomialRing(Fpt);

    f := up^4 + tp^4 + 1;

    if not IsIrreducible(f) then
        printf "p=%o: polynomial reducible\n", p;
        continue;
    end if;

    FF := FunctionField(f);
    Cl, m := ClassGroup(FF);
    invs := Invariants(Cl);

    // 2-torsion elements (excluding identity and the Z/0Z part)
    two_tors_elts := [];
    for i in [1..#invs] do
        if invs[i] gt 0 and invs[i] mod 2 eq 0 then
            Append(~two_tors_elts, i);
        end if;
    end for;

    printf "p=%o: J(F_p) has %o 2-torsion generators (2-rank=%o), ", p, #two_tors_elts, #two_tors_elts;
    printf "%o nontrivial 2-torsion elements\n", 2^#two_tors_elts - 1;
end for;

quit;
