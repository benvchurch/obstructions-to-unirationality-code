// Deeper analysis of candidate #8
// f = 3x^4+4x^3z+7x^2y^2-2x^2yz+5x^2z^2+2xy^2z+2xz^3+y^4+y^2z^2+z^4

Q := Rationals();
Poly<x,y,z> := PolynomialRing(Q, 3);
f := 3*x^4 + 4*x^3*z + 7*x^2*y^2 - 2*x^2*y*z + 5*x^2*z^2 + 2*x*y^2*z + 2*x*z^3 + y^4 + y^2*z^2 + z^4;

// === 1. 2-rank over F_p via L-poly mod 2 ===
// L(t) mod 2: if L(t) = (1+t)^6 mod 2, then 2-rank = 6
// Otherwise 2-rank is smaller
printf "L-polynomial mod 2 analysis:\n";
F2<t> := PolynomialRing(GF(2));
target := (1+t)^6;

for p in [7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43] do
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

    Lp := 1 + GF(2)!a1*t + GF(2)!a2*t^2 + GF(2)!a3*t^3 + GF(2)!p*GF(2)!a2*t^4 + GF(2)!(p^2)*GF(2)!a1*t^5 + t^6;
    printf "  p=%o: L mod 2 = %o", p, Lp;
    if Lp eq target then printf " = (1+t)^6"; end if;
    printf ", 2-rk(C/F_p) = ";
    // 2-rank is the multiplicity of 1 as root of L mod 2
    rk := 0;
    if Evaluate(Lp, GF(2)!1) eq 0 then
        // Factor out (1+t) repeatedly
        temp := Lp;
        while Evaluate(temp, GF(2)!1) eq 0 do
            temp := temp div (1+t);
            rk +:= 1;
        end while;
    end if;
    printf "%o\n", rk;
end for;

// === 2. Bitangent analysis over extension fields ===
// Check bitangents mod p to get a sense of the field of definition
printf "\nBitangent data over small fields:\n";
for p in [7, 11, 13, 17] do
    printf "  p=%o:\n", p;
    Fp := GF(p);
    P2p<xp,yp,zp> := ProjectiveSpace(Fp, 2);
    fp := Evaluate(f, [xp, yp, zp]);
    Cp := Curve(P2p, fp);
    if not IsNonsingular(Cp) then
        printf "    bad reduction\n";
        continue;
    end if;

    // Count bitangent lines over F_p
    // Line: a*X+b*Y+Z=0 (affine patch c=1) and a*X+b*Y=0 (c=0) and a*X+Z=0 (b=0,c=1)
    Qu<u> := PolynomialRing(Fp);
    bt := 0;

    // Lines with Z-coeff nonzero: a*X+b*Y+Z=0, parametrize as (u, 1, -a*u-b) or (1, u, -a-b*u)
    // Use: substitute Z = -a*X - b*Y, then restrict to line
    for a in Fp do
    for b in Fp do
        // Line: a*X + b*Y + Z = 0 => Z = -a*X-b*Y
        // f(X, Y, -a*X-b*Y), set Y=1
        fu := Evaluate(fp, [u, Fp!1, -a*u - b]);
        if Degree(fu) lt 4 then continue; end if;
        g := GCD(fu, Derivative(fu));
        if Degree(g) eq 2 then bt +:= 1; end if;
    end for;
    end for;

    // Lines through (0:0:1): X = a*Z, Y = b*Z => (a*u, b*u, u) = (a:b:1)
    // Already covered above (as a*X+b*Y+Z=0 includes all lines not passing through [0:0:1]... no wait)
    // Lines with Z-coeff = 0: a*X + b*Y = 0
    for a in Fp do
        // a*X + Y = 0, parametrize (u, -a*u, 1)... wait this is Z=1
        if a eq 0 then
            // Y=0: f(u, 0, 1)
            fu := Evaluate(fp, [u, Fp!0, Fp!1]);
        else
            // X = (-1/a)*Y, ((-1/a)*u, u, 1)... but also need Y=0 line: f(1, 0, u)
            fu := Evaluate(fp, [u, -a*u, Fp!1]);
        end if;
        if Degree(fu) lt 4 then continue; end if;
        g := GCD(fu, Derivative(fu));
        if Degree(g) eq 2 then bt +:= 1; end if;
    end for;
    // Line X = 0: f(0, u, 1)
    fu := Evaluate(fp, [Fp!0, u, Fp!1]);
    if Degree(fu) ge 4 then
        g := GCD(fu, Derivative(fu));
        if Degree(g) eq 2 then bt +:= 1; end if;
    end if;

    printf "    bitangent lines over F_%o: %o\n", p, bt;
end for;

// === 3. Discriminant ===
printf "\nBad primes (discriminant):\n";
// Compute discriminant of the ternary quartic
// Use the resultant approach: discriminant is the resultant system
// Actually, just check which primes give singular reduction
for p in [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] do
    P2p<xp,yp,zp> := ProjectiveSpace(GF(p), 2);
    fp := Evaluate(f, [xp, yp, zp]);
    Cp := Curve(P2p, fp);
    if not IsNonsingular(Cp) then
        printf "  p=%o: SINGULAR\n", p;
    else
        printf "  p=%o: smooth\n", p;
    end if;
end for;

printf "\nDone.\n";
quit;
