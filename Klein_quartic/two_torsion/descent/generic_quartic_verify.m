// Verify candidate: f = x^4+2*x^2*y^2+2*x^2*y*z-3*x^2*z^2-x*y*z^2+y^4-3*y*z^3+3*z^4
// (a5,a6,a8,a9,a10) = (-3,-1,0,-3,3), (a1,a2) = (0,2)

Q := Rationals();
Poly<x,y,z> := PolynomialRing(Q, 3);
f := x^4 + 2*x^2*y^2 + 2*x^2*y*z - 3*x^2*z^2 - x*y*z^2 + y^4 - 3*y*z^3 + 3*z^4;

printf "f = %o\n\n", f;

// === 1. Basic properties ===
P2<X,Y,Z> := ProjectiveSpace(Q, 2);
C := Curve(P2, Evaluate(f, [X, Y, Z]));
printf "Smooth: %o\n", IsNonsingular(C);
printf "Genus: %o\n", Genus(C);
printf "Irreducible: %o\n\n", IsIrreducible(C);

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
R := RealField(20);
pi := Pi(R);
min_val := R!100;
min_pt := [R|0,0,1];
N := 150;
for i := 0 to N do
    phi := pi * R!i / R!N;
    sp := Sin(phi); cp := Cos(phi);
    for j := 0 to 2*N-1 do
        theta := 2*pi*R!j / (2*R!N);
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
    A := AutomorphismGroup(Cp);
    printf "  p=%o: |Aut|=%o\n", p, #A;
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
