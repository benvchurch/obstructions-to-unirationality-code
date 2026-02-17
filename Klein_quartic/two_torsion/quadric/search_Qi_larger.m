/*******************************************************************************
 * search_Qi_larger.m
 *
 * Search for Q(i)-decompositions F = Q1*Q3 - Q2^2 with larger bounds.
 * Classify the J[2] class of each Q1 found.
 * Pay attention to whether Q1 is singular (rank < 3) or nonsingular.
 ******************************************************************************/

P<x> := PolynomialRing(Rationals());
K<i> := NumberField(x^2 + 1);
RK<X,Y,Z> := PolynomialRing(K, 3);
FK := X^4 + Y^4 + Z^4;

printf "=== LARGER SEARCH FOR Q(i) DECOMPOSITIONS ===\n\n";

// Classify J[2] class over F_p
p := 73;
Fp := GF(p);
im := Sqrt(Fp!-1);
s3 := Sqrt(Fp!-3);
A2<t,u> := AffineSpace(Fp, 2);
Caff := Curve(A2, t^4 + u^4 + 1);
KC := FunctionField(Caff);
t := KC.1; u := KC.2;

function HalfDiv(D)
    B := D - D;
    for pl in Support(D) do
        v := Valuation(D, pl);
        if v mod 2 ne 0 then return false, B; end if;
        B := B + (v div 2) * pl;
    end for;
    return true, B;
end function;

function HalfPositive(D)
    B := D - D;
    for pl in Support(D) do
        v := Valuation(D, pl);
        if v gt 0 then B := B + (v div 2) * pl; end if;
    end for;
    return B;
end function;

L := [t+u+1, t+u-1, t-u+1, t-u-1];
B := [HalfPositive(Divisor(KC!L[j])) : j in [1..4]];
v1 := B[1] - B[2];
v2 := B[1] - B[3];
q1_ref := KC!(2*t^2 + (1-s3)*u^2 + (1+s3));
_, half_ref := HalfDiv(Divisor(q1_ref));

function ClassifyHalf(half_D)
    if not IsPrincipal(2*half_D) then return "NOT 2-torsion"; end if;
    for a0 in [0,1] do for a1 in [0,1] do for a2 in [0,1] do
        test := half_D - a0*half_ref - a1*v1 - a2*v2;
        if IsPrincipal(test) then
            labels := ["0","v1","v2","v1+v2","eta","eta+v1","eta+v2","eta+v1+v2"];
            return labels[4*a0 + 2*a1 + a2 + 1];
        end if;
    end for; end for; end for;
    return "UNKNOWN";
end function;

function ClassifyQ1(Q1_poly)
    // Extract coefficients of Q1 (homogeneous degree 2 in X,Y,Z)
    // Reduce mod p: coefficients a+bi -> a+im*b in F_p
    cX2 := MonomialCoefficient(Q1_poly, X^2);
    cY2 := MonomialCoefficient(Q1_poly, Y^2);
    cZ2 := MonomialCoefficient(Q1_poly, Z^2);
    cXY := MonomialCoefficient(Q1_poly, X*Y);
    cXZ := MonomialCoefficient(Q1_poly, X*Z);
    cYZ := MonomialCoefficient(Q1_poly, Y*Z);

    function Red(c)
        // c is in K = Q(i), reduce to F_p
        coeffs := Eltseq(c);
        return Fp!coeffs[1] + im*Fp!coeffs[2];
    end function;

    q1_fp := Red(cX2)*t^2 + Red(cY2)*u^2 + Red(cZ2)
           + Red(cXY)*t*u + Red(cXZ)*t + Red(cYZ)*u;

    D := Divisor(q1_fp);
    ok, half := HalfDiv(D);
    if ok then
        return ClassifyHalf(half);
    else
        return "ODD";
    end if;
end function;

function Q1Rank(Q1_poly)
    cX2 := MonomialCoefficient(Q1_poly, X^2);
    cY2 := MonomialCoefficient(Q1_poly, Y^2);
    cZ2 := MonomialCoefficient(Q1_poly, Z^2);
    cXY := MonomialCoefficient(Q1_poly, X*Y);
    cXZ := MonomialCoefficient(Q1_poly, X*Z);
    cYZ := MonomialCoefficient(Q1_poly, Y*Z);
    M := Matrix(K, 3, 3,
        [cX2, cXY/2, cXZ/2,
         cXY/2, cY2, cYZ/2,
         cXZ/2, cYZ/2, cZ2]);
    return Rank(M), Determinant(M);
end function;

// =========================================================================
// Search with diagonal Q2 and larger bound
// Q2 = c1*X^2 + c2*Y^2 + c3*Z^2, coefficients a+bi with |a|,|b| <= bnd
// =========================================================================
bnd := 3;
found := 0;
classes := {};
class_examples := AssociativeArray();

printf "Search 1: diagonal Q2, bound %o\n", bnd;
for a1 in [-bnd..bnd] do for b1 in [-bnd..bnd] do
for a2 in [-bnd..bnd] do for b2 in [-bnd..bnd] do
for a3 in [-bnd..bnd] do for b3 in [-bnd..bnd] do
    c1 := a1+b1*i; c2 := a2+b2*i; c3 := a3+b3*i;
    Q2 := c1*X^2 + c2*Y^2 + c3*Z^2;
    if Q2 eq 0 then continue; end if;
    // Normalize
    coeffs := [a1,b1,a2,b2,a3,b3];
    first := 0;
    for j in [1..6] do
        if coeffs[j] ne 0 then first := coeffs[j]; break; end if;
    end for;
    if first lt 0 then continue; end if;

    G := FK + Q2^2;
    fac := Factorization(G);
    has_quad := false;
    if #fac eq 2 and TotalDegree(fac[1][1]) eq 2 and TotalDegree(fac[2][1]) eq 2 then
        has_quad := true;
    elif #fac eq 1 and fac[1][2] eq 2 and TotalDegree(fac[1][1]) eq 2 then
        has_quad := true;
    end if;

    if has_quad then
        found +:= 1;
        Q1 := fac[1][1];
        rk, det := Q1Rank(Q1);
        cls := ClassifyQ1(Q1);
        Include(~classes, cls);
        key := cls cat (rk eq 3 select " [nonsingular]" else " [singular]");
        if key notin Keys(class_examples) then
            class_examples[key] := <Q1, Q2>;
            printf "  #%o: cls=%o, rank=%o, Q1=%o, Q2=%o\n", found, cls, rk, Q1, Q2;
        end if;
    end if;
end for; end for;
end for; end for;
end for; end for;

printf "  Total: %o decomps, classes: %o\n\n", found, classes;

// =========================================================================
// Search with cross terms, bound 2
// =========================================================================
bnd2 := 2;
printf "Search 2: full Q2 (with cross terms), bound %o\n", bnd2;
found2 := 0;
for a1 in [-bnd2..bnd2] do for b1 in [-bnd2..bnd2] do
for a2 in [-bnd2..bnd2] do for b2 in [-bnd2..bnd2] do
for a3 in [-bnd2..bnd2] do for b3 in [-bnd2..bnd2] do
for a4 in [-bnd2..bnd2] do for b4 in [-bnd2..bnd2] do
for a5 in [-bnd2..bnd2] do for b5 in [-bnd2..bnd2] do
for a6 in [-bnd2..bnd2] do for b6 in [-bnd2..bnd2] do
    c1 := a1+b1*i; c2 := a2+b2*i; c3 := a3+b3*i;
    c4 := a4+b4*i; c5 := a5+b5*i; c6 := a6+b6*i;
    Q2 := c1*X^2 + c2*Y^2 + c3*Z^2 + c4*X*Y + c5*X*Z + c6*Y*Z;
    if Q2 eq 0 then continue; end if;
    coeffs := [a1,b1,a2,b2,a3,b3,a4,b4,a5,b5,a6,b6];
    first := 0;
    for j in [1..12] do
        if coeffs[j] ne 0 then first := coeffs[j]; break; end if;
    end for;
    if first lt 0 then continue; end if;

    G := FK + Q2^2;
    fac := Factorization(G);
    has_quad := false;
    if #fac eq 2 and TotalDegree(fac[1][1]) eq 2 and TotalDegree(fac[2][1]) eq 2 then
        has_quad := true;
    elif #fac eq 1 and fac[1][2] eq 2 and TotalDegree(fac[1][1]) eq 2 then
        has_quad := true;
    end if;

    if has_quad then
        found2 +:= 1;
        Q1 := fac[1][1];
        rk, det := Q1Rank(Q1);
        cls := ClassifyQ1(Q1);
        Include(~classes, cls);
        key := cls cat (rk eq 3 select " [nonsingular]" else " [singular]");
        if key notin Keys(class_examples) then
            class_examples[key] := <Q1, Q2>;
            printf "  #%o: cls=%o, rank=%o, Q1=%o\n    Q2=%o\n", found2, cls, rk, Q1, Q2;
        end if;
    end if;
end for; end for;
end for; end for;
end for; end for;
end for; end for;
end for; end for;
end for; end for;

printf "  Total: %o decomps, classes: %o\n\n", found2, classes;

// =========================================================================
printf "=== ALL CLASSES FOUND ===\n";
for key in Sort(SetToSequence(Keys(class_examples))) do
    data := class_examples[key];
    printf "  %o:\n    Q1 = %o\n    Q2 = %o\n\n", key, data[1], data[2];
end for;

quit;
