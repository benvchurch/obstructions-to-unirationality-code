/*******************************************************************************
 * search_over_Qi.m
 *
 * Search for Q(i)-decompositions F = Q1*Q3 - Q2^2 of F = x^4+y^4+z^4,
 * classify the J[2] class of each Q1 found.
 *
 * Merged from: search_over_Qi.m + search_Qi_larger.m + classify_Qi_decomps.m
 *
 * The Brauer obstruction has invariants at (inf, 2), so Q(i) should kill it,
 * meaning decompositions MUST exist over Q(i).
 ******************************************************************************/

P<x> := PolynomialRing(Rationals());
K<i> := NumberField(x^2 + 1);
RK<X,Y,Z> := PolynomialRing(K, 3);
FK := X^4 + Y^4 + Z^4;

// =========== CLASSIFICATION SETUP OVER F_p ===========

// Use F_p where sqrt(-1) and sqrt(-3) both exist (p = 1 mod 12)
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

// V_rat and eta reference divisors
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
    cX2 := MonomialCoefficient(Q1_poly, X^2);
    cY2 := MonomialCoefficient(Q1_poly, Y^2);
    cZ2 := MonomialCoefficient(Q1_poly, Z^2);
    cXY := MonomialCoefficient(Q1_poly, X*Y);
    cXZ := MonomialCoefficient(Q1_poly, X*Z);
    cYZ := MonomialCoefficient(Q1_poly, Y*Z);

    function Red(c)
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

// =========== SEARCH 1: INITIAL Q(i) SEARCH, BOUND 1 ===========

print "=== INITIAL Q(i) SEARCH (bound 1) ===";
print "";

bnd := 1;
found := 0;
total := 0;

for a1 in [-bnd..bnd] do for b1 in [-bnd..bnd] do
for a2 in [-bnd..bnd] do for b2 in [-bnd..bnd] do
for a3 in [-bnd..bnd] do for b3 in [-bnd..bnd] do
for a4 in [-bnd..bnd] do for b4 in [-bnd..bnd] do
for a5 in [-bnd..bnd] do for b5 in [-bnd..bnd] do
for a6 in [-bnd..bnd] do for b6 in [-bnd..bnd] do
    c1 := a1 + b1*i; c2 := a2 + b2*i; c3 := a3 + b3*i;
    c4 := a4 + b4*i; c5 := a5 + b5*i; c6 := a6 + b6*i;
    Q2 := c1*X^2 + c2*Y^2 + c3*Z^2 + c4*X*Y + c5*X*Z + c6*Y*Z;
    if Q2 eq 0 then continue; end if;

    G := FK + Q2^2;
    total +:= 1;
    fac := Factorization(G);

    has_quad := false;
    if #fac eq 2 and TotalDegree(fac[1][1]) eq 2 and TotalDegree(fac[2][1]) eq 2 then
        has_quad := true;
    elif #fac eq 1 and fac[1][2] eq 2 and TotalDegree(fac[1][1]) eq 2 then
        has_quad := true;
    end if;

    if has_quad then
        found +:= 1;
        if found le 30 then
            printf "FOUND #%o: Q2 = %o\n", found, Q2;
            for pair in fac do
                Q1 := pair[1]; exp := pair[2];
                printf "  factor: (%o)^%o\n", Q1, exp;
            end for;
            if #fac eq 2 then
                Q1 := fac[1][1]; Q3 := fac[2][1];
                lc := LeadingCoefficient(G) / LeadingCoefficient(Q1*Q3);
                Q1s := lc * Q1;
                if Q1s*Q3 - Q2^2 eq FK then
                    printf "  VERIFIED: F = Q1*Q3 - Q2^2\n";
                    printf "  Q1 = %o\n  Q3 = %o\n", Q1s, Q3;
                end if;
            end if;
            printf "\n";
        end if;
    end if;
end for; end for;
end for; end for;
end for; end for;
end for; end for;
end for; end for;
end for; end for;

printf "Total Q2 tested: %o, decompositions found: %o (bound=%o)\n\n", total, found, bnd;

// =========== SEARCH 2: DIAGONAL Q2 WITH LARGER BOUND ===========

printf "=== LARGER SEARCH: DIAGONAL Q2 (bound 3) ===\n\n";
bnd2 := 3;
found2 := 0;
classes := {};
class_examples := AssociativeArray();

for a1 in [-bnd2..bnd2] do for b1 in [-bnd2..bnd2] do
for a2 in [-bnd2..bnd2] do for b2 in [-bnd2..bnd2] do
for a3 in [-bnd2..bnd2] do for b3 in [-bnd2..bnd2] do
    c1 := a1+b1*i; c2 := a2+b2*i; c3 := a3+b3*i;
    Q2 := c1*X^2 + c2*Y^2 + c3*Z^2;
    if Q2 eq 0 then continue; end if;
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
        found2 +:= 1;
        Q1 := fac[1][1];
        rk, det := Q1Rank(Q1);
        cls := ClassifyQ1(Q1);
        Include(~classes, cls);
        key := cls cat (rk eq 3 select " [nonsingular]" else " [singular]");
        if key notin Keys(class_examples) then
            class_examples[key] := <Q1, Q2>;
            printf "  #%o: cls=%o, rank=%o, Q1=%o, Q2=%o\n", found2, cls, rk, Q1, Q2;
        end if;
    end if;
end for; end for;
end for; end for;
end for; end for;

printf "  Total: %o decomps, classes: %o\n\n", found2, classes;

// =========== SEARCH 3: FULL Q2 WITH CROSS TERMS, BOUND 2 ===========

printf "=== FULL Q2 SEARCH (with cross terms, bound 2) ===\n\n";
bnd3 := 2;
found3 := 0;

for a1 in [-bnd3..bnd3] do for b1 in [-bnd3..bnd3] do
for a2 in [-bnd3..bnd3] do for b2 in [-bnd3..bnd3] do
for a3 in [-bnd3..bnd3] do for b3 in [-bnd3..bnd3] do
for a4 in [-bnd3..bnd3] do for b4 in [-bnd3..bnd3] do
for a5 in [-bnd3..bnd3] do for b5 in [-bnd3..bnd3] do
for a6 in [-bnd3..bnd3] do for b6 in [-bnd3..bnd3] do
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
        found3 +:= 1;
        Q1 := fac[1][1];
        rk, det := Q1Rank(Q1);
        cls := ClassifyQ1(Q1);
        Include(~classes, cls);
        key := cls cat (rk eq 3 select " [nonsingular]" else " [singular]");
        if key notin Keys(class_examples) then
            class_examples[key] := <Q1, Q2>;
            printf "  #%o: cls=%o, rank=%o, Q1=%o\n    Q2=%o\n", found3, cls, rk, Q1, Q2;
        end if;
    end if;
end for; end for;
end for; end for;
end for; end for;
end for; end for;
end for; end for;
end for; end for;

printf "  Total: %o decomps, classes: %o\n\n", found3, classes;

// =========== CLASSIFICATION OF FOUND Q1 VALUES ===========

printf "=== ALL CLASSES FOUND ===\n";
for key in Sort(SetToSequence(Keys(class_examples))) do
    data := class_examples[key];
    printf "  %o:\n    Q1 = %o\n    Q2 = %o\n\n", key, data[1], data[2];
end for;

// =========== DETAILED CLASSIFICATION AT p = 13 ===========

printf "=== DETAILED CLASSIFICATION AT p = 13 ===\n\n";

p2 := 13;
Fp2 := GF(p2);
im2 := Sqrt(Fp2!-1);
w2  := Sqrt(Fp2!-3);
printf "p = %o, i = %o, sqrt(-3) = %o\n\n", p2, im2, w2;

A2b<t2,u2> := AffineSpace(Fp2, 2);
Caff2 := Curve(A2b, t2^4 + u2^4 + 1);
KC2 := FunctionField(Caff2);
tt := KC2.1; uu := KC2.2;

// V_rat reference
L2 := [tt+uu+1, tt+uu-1, tt-uu+1, tt-uu-1];
B2 := [HalfPositive(Divisor(KC2!L2[j])) : j in [1..4]];
v1b := B2[1] - B2[2];
v2b := B2[1] - B2[3];

// eta reference
q1_ref2 := KC2!(2*tt^2 + (1-w2)*uu^2 + (1+w2));
_, half_ref2 := HalfDiv(Divisor(q1_ref2));

function ClassifyHalf2(half_D)
    if not IsPrincipal(2*half_D) then return "NOT 2-torsion"; end if;
    for a0 in [0,1] do for a1 in [0,1] do for a2 in [0,1] do
        test := half_D - a0*half_ref2 - a1*v1b - a2*v2b;
        if IsPrincipal(test) then
            labels := ["0","v1","v2","v1+v2","eta","eta+v1","eta+v2","eta+v1+v2"];
            return labels[4*a0 + 2*a1 + a2 + 1];
        end if;
    end for; end for; end for;
    return "UNKNOWN";
end function;

// Distinct Q1 forms from the searches (affine z=1)
print "--- Q1 classes (reduced to F_13) ---";
q1_list := [
    <(2*im2+1)*tt^2 + (-im2+2)*uu^2,       "(2i+1)x^2 + (-i+2)y^2">,
    <(2*im2+1)*tt^2 + (-im2+2),            "(2i+1)x^2 + (-i+2)z^2">,
    <(2*im2+1)*tt^2 + (im2-2),             "(2i+1)x^2 + (i-2)z^2">,
    <(2*im2+1)*tt^2 + (im2-2)*uu^2,         "(2i+1)x^2 + (i-2)y^2">,
    <2*tt^2 + 2*im2,                       "2x^2 + 2iz^2 [cleanest]">
];

for data in q1_list do
    q := data[1]; name := data[2];
    D := Divisor(q);
    ok, half := HalfDiv(D);
    if ok then
        cls := ClassifyHalf2(half);
        printf "  %-35o -> %o\n", name, cls;
    else
        printf "  %-35o -> odd multiplicities\n", name;
    end if;
end for;

// Conjugate decompositions (sigma: i -> -i)
print "\n--- Conjugate Q1 values ---";
conj_q1 := [
    <(-2*im2+1)*tt^2 + (im2+2)*uu^2,        "sigma(Q1#1) = (-2i+1)x^2+(i+2)y^2">,
    <2*tt^2 - 2*im2,                        "sigma(Q1#9) = 2x^2-2iz^2">,
    <(-2*im2+1)*tt^2 + (im2+2),             "sigma(Q1#3) = (-2i+1)x^2+(i+2)z^2">
];

for data in conj_q1 do
    q := data[1]; name := data[2];
    D := Divisor(q);
    ok, half := HalfDiv(D);
    if ok then
        cls := ClassifyHalf2(half);
        printf "  %-45o -> %o\n", name, cls;
    else
        printf "  %-45o -> odd multiplicities\n", name;
    end if;
end for;

// Rational Q1 forms for comparison
print "\n--- Rational Q1 forms (should give V_rat or 0) ---";
rat_q1 := [
    <2*tt^2 + uu^2 + 1,     "2x^2+y^2+z^2 (F_3 eta)">,
    <tt^2 + 2*uu^2 + 1,     "x^2+2y^2+z^2">,
    <tt^2 + uu^2 + 2,       "x^2+y^2+2z^2">,
    <tt^2 + uu^2,            "x^2+y^2">,
    <tt^2 + 1,              "x^2+z^2">,
    <uu^2 + 1,              "y^2+z^2">,
    <tt*uu + 1,              "xy+z^2">,
    <tt + uu^2,              "xz+y^2">
];

for data in rat_q1 do
    q := data[1]; name := data[2];
    D := Divisor(q);
    ok, half := HalfDiv(D);
    if ok then
        cls := ClassifyHalf2(half);
        printf "  %-30o -> %o\n", name, cls;
    else
        printf "  %-30o -> odd multiplicities\n", name;
    end if;
end for;

quit;
