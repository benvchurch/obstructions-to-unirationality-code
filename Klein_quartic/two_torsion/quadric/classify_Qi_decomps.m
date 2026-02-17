/*******************************************************************************
 * classify_Qi_decomps.m
 *
 * Classify the Q(i) decompositions found by search_over_Qi.m.
 * For each Q1, reduce to F_p and compute which J[2] class it gives.
 ******************************************************************************/

p := 13;
Fp := GF(p);
im := Sqrt(Fp!-1);
w  := Sqrt(Fp!-3);
printf "p = %o, i = %o, sqrt(-3) = %o\n\n", p, im, w;

A2<t,u> := AffineSpace(Fp, 2);
Caff := Curve(A2, t^4 + u^4 + 1);
KC := FunctionField(Caff);
t := KC.1;
u := KC.2;

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

// V_rat reference
L := [t+u+1, t+u-1, t-u+1, t-u-1];
B := [HalfPositive(Divisor(KC!L[j])) : j in [1..4]];
v1 := B[1] - B[2];
v2 := B[1] - B[3];

// eta reference
q1_ref := KC!(2*t^2 + (1-w)*u^2 + (1+w));
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

// =========================================================================
// The 9 decompositions from search_over_Qi.m (Q1 values, affine z=1)
// All have form Q1(x,y,z)/z^2 -> Q1(t,u,1) in function field
//
// From output, the Q1 values (after scalar normalization) were:
// #1: Q1 = (2i+1)X^2 + (-i+2)Y^2
// #2: Q1 = (2i+1)X^2 + (-i+2)Y^2  (same Q1, diff Q2/Q3)
// #3: Q1 = (2i+1)X^2 + (-i+2)Z^2
// #4: Q1 = (2i+1)X^2 + (i-2)Z^2
// #5: Q1 = (2i+1)X^2 + (-i+2)Z^2  (same as #3)
// #6: Q1 = (2i+1)X^2 + (i-2)Z^2   (same as #4)
// #7: Q1 = (2i+1)X^2 + (i-2)Y^2
// #8: Q1 = (2i+1)X^2 + (i-2)Y^2   (same as #7)
// #9: Q1 = 2X^2 + 2iZ^2
// =========================================================================

print "=== Q1 VALUES FROM SEARCH (reduced to F_p) ===\n";

// Distinct Q1 forms (affine z=1): Q1(t,u,1)
q1_list := [
    <(2*im+1)*t^2 + (-im+2)*u^2,       "(2i+1)x^2 + (-i+2)y^2">,
    <(2*im+1)*t^2 + (-im+2),            "(2i+1)x^2 + (-i+2)z^2">,
    <(2*im+1)*t^2 + (im-2),             "(2i+1)x^2 + (i-2)z^2">,
    <(2*im+1)*t^2 + (im-2)*u^2,         "(2i+1)x^2 + (i-2)y^2">,
    <2*t^2 + 2*im,                       "2x^2 + 2iz^2 [=#9, cleanest]">
];

// Also include Q3 from each decomposition (Q3 also gives a class via HalfDiv)
q3_list := [
    <t^2 + ((-3*im+4)/5)*u^2 + ((6*im+2)/5),  "Q3 of #1">,
    <t^2 + ((6*im+2)/5)*u^2 + ((-3*im+4)/5),   "Q3 of #3">,
    <t^2 + im*u^2,                               "Q3 of #9">
];

print "--- Q1 classes ---";
for data in q1_list do
    q := data[1];
    name := data[2];
    D := Divisor(q);
    ok, half := HalfDiv(D);
    if ok then
        cls := ClassifyHalf(half);
        printf "  %-35o -> %o\n", name, cls;
    else
        printf "  %-35o -> odd multiplicities\n", name;
    end if;
end for;

print "\n--- Q3 classes ---";
for data in q3_list do
    q := data[1];
    name := data[2];
    D := Divisor(q);
    ok, half := HalfDiv(D);
    if ok then
        cls := ClassifyHalf(half);
        printf "  %-35o -> %o\n", name, cls;
    else
        printf "  %-35o -> odd multiplicities\n", name;
    end if;
end for;

// =========================================================================
// Also try some "random" Q1 forms over F_p to see other classes
// These are NOT from Q(i) decompositions, just probing J[2]
// =========================================================================
print "\n=== ADDITIONAL PROBES ===";

// From conjugate decomposition: sigma(Q1) = (2(-i)+1)X^2 + (i+2)Y^2
//                                         = (-2i+1)X^2 + (i+2)Y^2
conj_q1 := [
    <(-2*im+1)*t^2 + (im+2)*u^2,        "sigma(Q1#1) = (-2i+1)x^2+(i+2)y^2">,
    <2*t^2 - 2*im,                        "sigma(Q1#9) = 2x^2-2iz^2">,
    <(-2*im+1)*t^2 + (im+2),             "sigma(Q1#3) = (-2i+1)x^2+(i+2)z^2">
];

for data in conj_q1 do
    q := data[1];
    name := data[2];
    D := Divisor(q);
    ok, half := HalfDiv(D);
    if ok then
        cls := ClassifyHalf(half);
        printf "  %-45o -> %o\n", name, cls;
    else
        printf "  %-45o -> odd multiplicities\n", name;
    end if;
end for;

// =========================================================================
// Try Q1 forms with RATIONAL coefficients (should give V_rat classes)
// =========================================================================
print "\n=== RATIONAL Q1 FORMS (should give V_rat or 0) ===";
rat_q1 := [
    <2*t^2 + u^2 + 1,     "2x^2+y^2+z^2 (F_3 eta)">,
    <t^2 + 2*u^2 + 1,     "x^2+2y^2+z^2">,
    <t^2 + u^2 + 2,       "x^2+y^2+2z^2">,
    <t^2 + u^2,            "x^2+y^2">,
    <t^2 + 1,              "x^2+z^2">,
    <u^2 + 1,              "y^2+z^2">,
    <t*u + 1,              "xy+z^2">,
    <t + u^2,              "xz+y^2">
];

for data in rat_q1 do
    q := data[1];
    name := data[2];
    D := Divisor(q);
    ok, half := HalfDiv(D);
    if ok then
        cls := ClassifyHalf(half);
        printf "  %-30o -> %o\n", name, cls;
    else
        printf "  %-30o -> odd multiplicities\n", name;
    end if;
end for;

quit;
