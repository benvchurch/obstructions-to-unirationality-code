// Deeper analysis of candidate #8
// f = 3x^4+4x^3z+7x^2y^2-2x^2yz+5x^2z^2+2xy^2z+2xz^3+y^4+y^2z^2+z^4
// From A=2x^2+xz+y^2+z^2, B=xy, Q2=x^2+yz

Q := Rationals();
Poly<x,y,z> := PolynomialRing(Q, 3);
f := 3*x^4 + 4*x^3*z + 7*x^2*y^2 - 2*x^2*y*z + 5*x^2*z^2
     + 2*x*y^2*z + 2*x*z^3 + y^4 + y^2*z^2 + z^4;

// === 1. Careful bitangent count over F_p ===
// A bitangent to C: f=0 is a line L such that L.C = 2P+2Q
// Equivalently: restricting f to L gives a perfect square of a quadratic.
printf "=== Bitangent lines over F_p ===\n";
for p in [7, 11, 13, 17, 19, 23, 29, 31] do
    Fp := GF(p);
    P2p<xp,yp,zp> := ProjectiveSpace(Fp, 2);
    fp := Evaluate(f, [xp, yp, zp]);
    Cp := Curve(P2p, fp);
    if not IsNonsingular(Cp) then
        printf "p=%o: bad reduction\n", p;
        continue;
    end if;

    Qu<u> := PolynomialRing(Fp);
    bt_lines := [];

    // Lines Z=aX+bY (passing through dual coordinates)
    // Parametrize: for line aX+bY+cZ=0 with c!=0, normalize c=1: Z=-aX-bY
    for a in Fp do
    for b in Fp do
        fu := Evaluate(fp, [u, Qu!1, -a*u - b]);
        if Degree(fu) ne 4 then
            // Line might be tangent at infinity, check separately
            continue;
        end if;
        lc := LeadingCoefficient(fu);
        fu_monic := fu/lc;
        g := GCD(fu, Derivative(fu));
        if Degree(g) eq 2 then
            Append(~bt_lines, [a, b, Fp!1]);
        end if;
    end for;
    end for;

    // Lines through (0:1:0): X=aY+bZ, normalize by setting Y=1
    // But need lines with Y-coeff = 0: aX+cZ = 0 with a!=0
    for c in Fp do
        // X = -c*Z, Y = u*Z => point is (-c:u:1)
        fu := Evaluate(fp, [-c*u, u, Qu!1]);
        if Degree(fu) ne 4 then continue; end if;
        g := GCD(fu, Derivative(fu));
        if Degree(g) eq 2 then
            Append(~bt_lines, [Fp!1, Fp!0, c]);
        end if;
    end for;

    // Line Y=0: f(u, 0, 1) (the line X=0,Y=0 is a point)
    fu := Evaluate(fp, [u, Fp!0, Qu!1]);
    if Degree(fu) eq 4 then
        g := GCD(fu, Derivative(fu));
        if Degree(g) eq 2 then
            Append(~bt_lines, [Fp!0, Fp!1, Fp!0]);
        end if;
    end if;

    printf "p=%o: %o bitangent lines\n", p, #bt_lines;
    if #bt_lines le 6 then
        for L in bt_lines do
            printf "  %o*X + %o*Y + %o*Z = 0\n", L[1], L[2], L[3];
        end for;
    end if;
end for;

// === 2. More L-poly data for v2 analysis ===
printf "\n=== Extended L-poly data ===\n";
for p in [47, 53, 59, 61, 67, 71, 73, 79, 83] do
    P2p<xp,yp,zp> := ProjectiveSpace(GF(p), 2);
    fp := Evaluate(f, [xp, yp, zp]);
    Cp := Curve(P2p, fp);
    if not IsNonsingular(Cp) then
        printf "p=%o: bad reduction\n", p;
        continue;
    end if;

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
    printf "  p=%o: #J=%o, v2=%o\n", p, Jp, v2;
end for;

// === 3. Try to determine #J[2](Q) precisely ===
// Use: the Frobenius at p acts on J[2](Qbar) = F_2^6
// J[2](Q) = intersection of ker(Frob_p - 1) over all good primes p
// We can approximate this by computing Frob action on J[2] over F_{p^k}
// At p=7: 2-rank of J(F_{7^k}) for k=1,2,3...
printf "\n=== 2-rank over extensions of F_7 ===\n";
for k := 1 to 4 do
    q := 7^k;
    P2q<xq,yq,zq> := ProjectiveSpace(GF(q), 2);
    fq := Evaluate(f, [xq, yq, zq]);
    Cq := Curve(P2q, fq);

    nk := #RationalPoints(Cq);
    printf "  F_{7^%o}: #C = %o\n", k, nk;
end for;

printf "\nDone.\n";
quit;
