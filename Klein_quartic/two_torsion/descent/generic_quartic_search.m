// Task 4: Construct quartic with TWO rational bitangent lines built in
//
// Setup: f = (x^2+y^2)^2 + z*R(x,y,z) with f(x,y,-x) also a perfect square.
//
// Fix z=0 bitangent: f(x,y,0) = (x^2+y^2)^2
// Fix x+z=0 bitangent: f(x,y,-x) = (x^2+y^2)^2
//
// These two bitangent lines give nontrivial J[2](Q) element (since the quartic
// is non-hyperelliptic, there's no degree-2 function, so the theta-characteristic
// difference is nonzero).
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
    A := AutomorphismGroup(Cp);
    if #A ne 1 then continue; end if;

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
        break a5; // break out of all loops
    end if;
end for; end for; end for; end for; end for;

printf "Total found: %o\n", found;
printf "Done.\n";
quit;
