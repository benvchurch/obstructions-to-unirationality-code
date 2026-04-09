/*******************************************************************************
 * generic_quartic_search.m
 *
 * Search for smooth plane quartics with Aut=1, positive definite, and two
 * rational bitangent lines (giving nontrivial J[2](Q) element).
 * Then verify the best candidate's properties.
 *
 * Merged from: generic_quartic_bt.m, generic_quartic_2rank.m,
 *              generic_quartic_search.m, generic_quartic_verify.m
 *
 * Contents:
 *   1. Parametric construction: quartics with two built-in bitangent lines
 *   2. Verification of best candidate
 ******************************************************************************/


// =========== PARAMETRIC CONSTRUCTION ===========
// Setup: f = (x^2+y^2)^2 + z*R(x,y,z) with f(x,y,-x) also a perfect square.
//
// Fix z=0 bitangent: f(x,y,0) = (x^2+y^2)^2
// Fix x+z=0 bitangent: f(x,y,-x) = (x^2+y^2)^2
//
// These two bitangent lines give nontrivial J[2](Q) element.
//
// Parametrize: f = (x^2+y^2)^2 + a1*x^3*z + a2*x^2*y*z + a5*x^2*z^2
//              + a6*x*y*z^2 + a8*x*z^3 + a9*y*z^3 + a10*z^4
// with constraints for x+z=0 bitangent:
//   a1 = a5 - a8 + a10,  a2 = a6 - a9,  a3=a4=a7=0
//
// Free params: a5, a6, a8, a9, a10

Q := Rationals();
Poly<x,y,z> := PolynomialRing(Q, 3);

printf "=== Searching quartics with two built-in bitangent lines ===\n";
printf "Bitangents: z=0 and x+z=0, both giving (x^2+y^2)^2\n\n";

vals := [-3,-2,-1,0,1,2,3];
found := 0;

for a5 in vals do
for a6 in vals do
for a8 in vals do
for a9 in vals do
for a10 in vals do
    a1 := a5 - a8 + a10;
    a2 := a6 - a9;

    f := x^4 + 2*x^2*y^2 + y^4
         + a1*x^3*z + a2*x^2*y*z
         + a5*x^2*z^2 + a6*x*y*z^2
         + a8*x*z^3 + a9*y*z^3 + a10*z^4;

    // Quick check: smoothness
    P2<X,Y,Z> := ProjectiveSpace(Q, 2);
    fp := Evaluate(f, [X, Y, Z]);
    C := Curve(P2, fp);
    if not IsNonsingular(C) then continue; end if;
    if Genus(C) ne 3 then continue; end if;

    // Positive definiteness check
    R := RealField(15);
    pi := Pi(R);
    min_val := R!100;
    N := 50;
    posdef := true;
    for i := 0 to N do
        phi := pi * R!i / R!N;
        sp := Sin(phi); cp := Cos(phi);
        for j := 0 to 2*N-1 do
            theta := 2*pi*R!j / (2*R!N);
            xv := sp*Cos(theta); yv := sp*Sin(theta); zv := cp;
            val := Evaluate(f, [xv, yv, zv]);
            if val lt min_val then min_val := val; end if;
            if val le 0 then posdef := false; break; end if;
        end for;
        if not posdef then break; end if;
    end for;
    if not posdef then continue; end if;

    // Check Aut = 1 at p=13
    P2p<xp,yp,zp> := ProjectiveSpace(GF(13), 2);
    fp13 := Evaluate(f, [xp, yp, zp]);
    Cp := Curve(P2p, fp13);
    if not IsNonsingular(Cp) then continue; end if;
    Ap := AutomorphismGroup(Cp);
    if #Ap ne 1 then continue; end if;

    // Confirm Aut = 1 at p=29
    P2q<xq,yq,zq> := ProjectiveSpace(GF(29), 2);
    fq := Evaluate(f, [xq, yq, zq]);
    Cq := Curve(P2q, fq);
    if not IsNonsingular(Cq) then continue; end if;
    Aq := AutomorphismGroup(Cq);
    if #Aq ne 1 then continue; end if;

    found +:= 1;
    printf "CANDIDATE %o: (a5,a6,a8,a9,a10) = (%o,%o,%o,%o,%o)\n",
        found, a5, a6, a8, a9, a10;
    printf "  => (a1,a2) = (%o,%o)\n", a1, a2;
    printf "  f = %o\n", f;
    printf "  min_val on sphere: %o\n", min_val;
    printf "  Aut mod 13 = 1, Aut mod 29 = 1\n\n";

    if found ge 5 then
        break a5;
    end if;
end for; end for; end for; end for; end for;

printf "Total found: %o\n\n", found;


// =========== VERIFICATION OF BEST CANDIDATE ===========
// Verify candidate: f = x^4+2*x^2*y^2+2*x^2*y*z-3*x^2*z^2-x*y*z^2+y^4-3*y*z^3+3*z^4
// (a5,a6,a8,a9,a10) = (-3,-1,0,-3,3), (a1,a2) = (0,2)

print "======================================================";
print "VERIFICATION: best candidate";
print "======================================================";

f := x^4 + 2*x^2*y^2 + 2*x^2*y*z - 3*x^2*z^2 - x*y*z^2 + y^4 - 3*y*z^3 + 3*z^4;

printf "f = %o\n\n", f;

// === 1. Basic properties ===
P2v<X,Y,Z> := ProjectiveSpace(Q, 2);
Cv := Curve(P2v, Evaluate(f, [X, Y, Z]));
printf "Smooth: %o\n", IsNonsingular(Cv);
printf "Genus: %o\n", Genus(Cv);
printf "Irreducible: %o\n\n", IsIrreducible(Cv);

// === 2. Verify bitangent lines ===
Qu<u> := PolynomialRing(Q);
// z=0: f(x,y,0) should be (x^2+y^2)^2
fz0 := Evaluate(f, [u, Q!1, Q!0]);
printf "f(u,1,0) = %o\n", fz0;
printf "  = (u^2+1)^2? %o\n", fz0 eq (u^2+1)^2;

// x+z=0, i.e. z=-x: f(x,y,-x)
fxz := Evaluate(f, [u, Q!1, -u]);
printf "f(u,1,-u) = %o\n", fxz;
printf "  = (u^2+1)^2? %o\n\n", fxz eq (u^2+1)^2;

// === 3. Positive definiteness (fine grid) ===
Rv := RealField(20);
pi_v := Pi(Rv);
min_val := Rv!100;
min_pt := [Rv|0,0,1];
N := 150;
for i := 0 to N do
    phi := pi_v * Rv!i / Rv!N;
    sp := Sin(phi); cp := Cos(phi);
    for j := 0 to 2*N-1 do
        theta := 2*pi_v*Rv!j / (2*Rv!N);
        xv := sp*Cos(theta); yv := sp*Sin(theta); zv := cp;
        val := Evaluate(f, [xv, yv, zv]);
        if val lt min_val then
            min_val := val;
            min_pt := [xv, yv, zv];
        end if;
    end for;
end for;
printf "Min on sphere (N=%o): %o\n", N, min_val;
printf "  at (%o, %o, %o)\n", min_pt[1], min_pt[2], min_pt[3];
printf "Positive definite: %o\n\n", min_val gt 0;

// === 4. Geometric automorphisms at many primes ===
printf "Geometric automorphisms:\n";
for p in [5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61] do
    P2p<xp,yp,zp> := ProjectiveSpace(GF(p), 2);
    fp := Evaluate(f, [xp, yp, zp]);
    Cp := Curve(P2p, fp);
    if not IsNonsingular(Cp) then
        printf "  p=%o: bad reduction\n", p;
        continue;
    end if;
    Ap := AutomorphismGroup(Cp);
    printf "  p=%o: |Aut|=%o\n", p, #Ap;
end for;

// === 5. L-polynomial and #J(F_p) ===
printf "\nL-polynomial data:\n";
for p in [5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53] do
    P2p<xp,yp,zp> := ProjectiveSpace(GF(p), 2);
    fp := Evaluate(f, [xp, yp, zp]);
    Cp := Curve(P2p, fp);
    if not IsNonsingular(Cp) then continue; end if;

    n1 := #RationalPoints(Cp);
    Cp2 := BaseChange(Cp, GF(p^2));
    n2 := #RationalPoints(Cp2);
    Cp3 := BaseChange(Cp, GF(p^3));
    n3 := #RationalPoints(Cp3);

    a1 := p + 1 - n1;
    a2 := (a1^2 - (p^2 + 1 - n2)) div 2;
    a3 := (a1^3 - 3*a1*a2 - (p^3 + 1 - n3)) div 3;
    Jp := 1 + a1 + a2 + a3 + p*a2 + p^2*a1 + p^3;
    v2 := Valuation(Jp, 2);
    printf "  p=%o: #C=%o, L=[1,%o,%o,%o], #J=%o, v2=%o\n",
        p, n1, a1, a2, a3, Jp, v2;
end for;

printf "\nDone.\n";
quit;
