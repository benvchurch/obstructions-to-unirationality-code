/*******************************************************************************
 * splitting_fields.m
 *
 * Field-of-definition analysis for quadric decompositions of x^4+y^4+z^4.
 * Tests factorization of F+Q2^2 over Q, Q(i), Q(sqrt(-2)), Q(sqrt(2)),
 * Q(zeta_8), and compares Q(i) vs Q(sqrt(-3)) decomposition classes.
 *
 * Merged from: splitting_fields.m + compare_Qi_Qsqrt3.m
 ******************************************************************************/

// =========== FACTORING OVER Q ===========

print "=== FACTORING F + Q2^2 OVER Q ===";
RQ<X,Y,Z> := PolynomialRing(Rationals(), 3);
FQ := X^4 + Y^4 + Z^4;

Q2 := Y^2 + Z^2;
G := FQ + Q2^2;
printf "F + (Y^2+Z^2)^2 = %o\n", G;
facQ := Factorization(G);
printf "Factorization over Q: ";
for pair in facQ do printf "(%o)^%o ", pair[1], pair[2]; end for;
printf "\n\n";

for Q2_data in [
    <X*Y + Z^2, "XY+Z^2">,
    <X*Z + Y^2, "XZ+Y^2">,
    <Y^2 + Y*Z + Z^2, "Y^2+YZ+Z^2">
] do
    Q2 := Q2_data[1]; name := Q2_data[2];
    G := FQ + Q2^2;
    facQ := Factorization(G);
    printf "Q2 = %o: F+Q2^2 = ", name;
    for pair in facQ do printf "(%o)^%o ", pair[1], pair[2]; end for;
    printf "\n";
end for;

// =========== FACTORING OVER Q(sqrt(-2)) ===========

print "";
print "=== FACTORING OVER Q(sqrt(-2)) ===";
Km2<w> := QuadraticField(-2);
RKm2<X,Y,Z> := PolynomialRing(Km2, 3);
FKm2 := X^4 + Y^4 + Z^4;

for Q2_data in [
    <Y^2 + Z^2, "Y^2+Z^2">,
    <X*Y + Z^2, "XY+Z^2">,
    <X*Z + Y^2, "XZ+Y^2">,
    <Y^2 + Y*Z + Z^2, "Y^2+YZ+Z^2">
] do
    Q2 := Q2_data[1]; name := Q2_data[2];
    G := FKm2 + Q2^2;
    facK := Factorization(G);
    printf "Q2 = %o: ", name;
    for pair in facK do printf "(%o)^%o ", pair[1], pair[2]; end for;
    printf "\n";
end for;

// =========== FACTORING OVER Q(i) ===========

print "";
print "=== FACTORING OVER Q(i) ===";
Ki<i> := QuadraticField(-1);
RKi<X,Y,Z> := PolynomialRing(Ki, 3);
FKi := X^4 + Y^4 + Z^4;

for Q2_data in [
    <Y^2 + Z^2, "Y^2+Z^2">,
    <X*Y + Z^2, "XY+Z^2">,
    <X*Z + Y^2, "XZ+Y^2">,
    <Y^2 + Y*Z + Z^2, "Y^2+YZ+Z^2">
] do
    Q2 := Q2_data[1]; name := Q2_data[2];
    G := FKi + Q2^2;
    facKi := Factorization(G);
    printf "Q2 = %o: ", name;
    for pair in facKi do printf "(%o)^%o ", pair[1], pair[2]; end for;
    printf "\n";
end for;

// =========== FACTORING OVER Q(sqrt(2)) ===========

print "";
print "=== FACTORING OVER Q(sqrt(2)) ===";
K2<s> := QuadraticField(2);
RK2<X,Y,Z> := PolynomialRing(K2, 3);
FK2 := X^4 + Y^4 + Z^4;

for Q2_data in [
    <Y^2 + Z^2, "Y^2+Z^2">,
    <X*Y + Z^2, "XY+Z^2">,
    <X*Z + Y^2, "XZ+Y^2">,
    <Y^2 + Y*Z + Z^2, "Y^2+YZ+Z^2">
] do
    Q2 := Q2_data[1]; name := Q2_data[2];
    G := FK2 + Q2^2;
    facK2 := Factorization(G);
    printf "Q2 = %o: ", name;
    for pair in facK2 do printf "(%o)^%o ", pair[1], pair[2]; end for;
    printf "\n";
end for;

// =========== FACTORING OVER Q(zeta_8) ===========

print "";
print "=== FACTORING OVER Q(zeta_8) ===";
PP<x> := PolynomialRing(Rationals());
K8<z8> := NumberField(x^4 + 1);
RK8<X,Y,Z> := PolynomialRing(K8, 3);
FK8 := X^4 + Y^4 + Z^4;

for Q2_data in [
    <Y^2 + Z^2, "Y^2+Z^2">,
    <X*Y + Z^2, "XY+Z^2">,
    <X*Z + Y^2, "XZ+Y^2">,
    <Y^2 + Y*Z + Z^2, "Y^2+YZ+Z^2">
] do
    Q2 := Q2_data[1]; name := Q2_data[2];
    G := FK8 + Q2^2;
    facK8 := Factorization(G);
    printf "Q2 = %o: ", name;
    for pair in facK8 do printf "(%o)^%o ", pair[1], pair[2]; end for;
    printf "\n";
end for;

// =========== COMPARING Q(i) AND Q(sqrt(-3)) CLASSES ===========

print "";
print "============================================================";
print "=== COMPARING Q(i) AND Q(sqrt(-3)) DECOMPOSITION CLASSES ===";
print "============================================================";
print "";

// Work over F_p where both sqrt(-1) and sqrt(-3) exist (p = 1 mod 12)
p := 13;
Fp := GF(p);
im := Sqrt(Fp!-1);
ww := Sqrt(Fp!-3);
printf "p = %o, i = %o, sqrt(-3) = %o\n", p, im, ww;

A2<t,u> := AffineSpace(Fp, 2);
Caff := Curve(A2, t^4 + u^4 + 1);
KC := FunctionField(Caff);
t := KC.1; u := KC.2;

printf "%o places of degree 1\n", #Places(Caff, 1);

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

// Q(sqrt(-3)) decomposition: Q1 = 2x^2 + (1-w)y^2 + (1+w)z^2
print "\n=== Q(sqrt(-3)) DECOMPOSITION ===";
q1_s := KC!(2*t^2 + (1-ww)*u^2 + (1+ww));
D_s := Divisor(q1_s);
supp_s, mults_s := Support(D_s);
printf "div(q1): %o places, mults = %o\n", #supp_s, mults_s;
all_even_s := &and[m mod 2 eq 0 : m in mults_s];
printf "All even: %o\n", all_even_s;
half_s := &+[Integers()!(mults_s[j] div 2) * supp_s[j] : j in [1..#supp_s]];

// Q(i) decomposition: Q1 = 2x^2 + 2i*z^2
print "\n=== Q(i) DECOMPOSITION ===";
q1_i := KC!(2*t^2 + 2*im);
D_i := Divisor(q1_i);
supp_i, mults_i := Support(D_i);
printf "div(q1): %o places, mults = %o\n", #supp_i, mults_i;
all_even_i := &and[m mod 2 eq 0 : m in mults_i];
printf "All even: %o\n", all_even_i;
half_i := &+[Integers()!(mults_i[j] div 2) * supp_i[j] : j in [1..#supp_i]];

// Compare classes
print "\n=== COMPARISON ===";
printf "2 * half_s principal? %o\n", IsPrincipal(2*half_s);
printf "2 * half_i principal? %o\n", IsPrincipal(2*half_i);

delta := half_s - half_i;
is_same, _ := IsPrincipal(delta);
printf "\nhalf_s - half_i principal (same class)? %o\n", is_same;

if is_same then
    print "==> SAME 2-torsion class from both decompositions!";
else
    is_2tor, _ := IsPrincipal(2*delta);
    printf "2*(half_s - half_i) principal (difference is 2-torsion)? %o\n", is_2tor;
end if;

// V_rat membership check
print "\n=== V_rat GENERATORS ===";
LL := [t+u+1, t+u-1, t-u+1, t-u-1];
Lnames := ["x+y+z", "x+y-z", "x-y+z", "x-y-z"];

vrat_gens := [];
vrat_names := [];
for pair in [<1,2>, <1,3>] do
    j := pair[1]; k := pair[2];
    ratio := KC!(LL[j] / LL[k]);
    D_ratio := Divisor(ratio);
    supp_r, mults_r := Support(D_ratio);
    ok := &and[m mod 2 eq 0 : m in mults_r];
    printf "%o / %o: mults = %o, all even: %o\n", Lnames[j], Lnames[k], mults_r, ok;
    if ok then
        half_r := &+[Integers()!(mults_r[ii] div 2) * supp_r[ii] : ii in [1..#supp_r]];
        Append(~vrat_gens, half_r);
        Append(~vrat_names, Sprintf("%o/%o", Lnames[j], Lnames[k]));
    end if;
end for;

print "\n=== MEMBERSHIP IN V_rat ===";
for data in [<half_s, "half_s (Q(sqrt(-3)))">, <half_i, "half_i (Q(i))">] do
    cls := data[1]; name := data[2];
    printf "\n%o:\n", name;
    in_vrat := false;

    chk0, _ := IsPrincipal(cls);
    if chk0 then printf "  = 0 (trivial)\n"; in_vrat := true; continue data; end if;

    if #vrat_gens ge 2 then
        for sgn1 in [-1,0,1] do for sgn2 in [-1,0,1] do
            if sgn1 eq 0 and sgn2 eq 0 then continue; end if;
            test := cls - sgn1*vrat_gens[1] - sgn2*vrat_gens[2];
            chk, _ := IsPrincipal(test);
            if chk then
                printf "  = %o*%o + %o*%o\n", sgn1, vrat_names[1], sgn2, vrat_names[2];
                in_vrat := true;
                break sgn1;
            end if;
        end for; end for;
    end if;
    if not in_vrat then printf "  NOT in V_rat\n"; end if;
end for;

// =========== CROSS-CHECK AT p = 37 ===========

print "\n\n=== CROSS-CHECK AT p = 37 ===";
p2 := 37;
Fp2 := GF(p2);
im2 := Sqrt(Fp2!-1);
w2  := Sqrt(Fp2!-3);
printf "p = %o, i = %o, sqrt(-3) = %o\n", p2, im2, w2;

A2b<t2,u2> := AffineSpace(Fp2, 2);
Caff2 := Curve(A2b, t2^4 + u2^4 + 1);
KC2 := FunctionField(Caff2);
tt := KC2.1; uu := KC2.2;

q1_s2 := KC2!(2*tt^2 + (1-w2)*uu^2 + (1+w2));
q1_i2 := KC2!(2*tt^2 + 2*im2);

D_s2 := Divisor(q1_s2);
D_i2 := Divisor(q1_i2);
supp_s2, mults_s2 := Support(D_s2);
supp_i2, mults_i2 := Support(D_i2);

ok2_s := &and[m mod 2 eq 0 : m in mults_s2];
ok2_i := &and[m mod 2 eq 0 : m in mults_i2];
printf "Q(sqrt(-3)) all even: %o, Q(i) all even: %o\n", ok2_s, ok2_i;

if ok2_s and ok2_i then
    half2_s := &+[Integers()!(mults_s2[j] div 2) * supp_s2[j] : j in [1..#supp_s2]];
    half2_i := &+[Integers()!(mults_i2[j] div 2) * supp_i2[j] : j in [1..#supp_i2]];
    delta2 := half2_s - half2_i;
    same2, _ := IsPrincipal(delta2);
    printf "Same class at p=%o? %o\n", p2, same2;
end if;

quit;
