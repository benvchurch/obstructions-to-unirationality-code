/*******************************************************************************
 * compare_Qi_Qsqrt3.m
 *
 * Compare the 2-torsion classes from the Q(i) and Q(sqrt(-3)) quadric
 * decompositions of x^4+y^4+z^4.  Work over F_p where both sqrt(-1)
 * and sqrt(-3) exist (p = 1 mod 12).
 ******************************************************************************/

p := 13;
Fp := GF(p);
im := Sqrt(Fp!-1);
w  := Sqrt(Fp!-3);
printf "p = %o, i = %o, sqrt(-3) = %o\n", p, im, w;

// Affine model C: t^4 + u^4 + 1 = 0
A2<t,u> := AffineSpace(Fp, 2);
Caff := Curve(A2, t^4 + u^4 + 1);
KC := FunctionField(Caff);
t := KC.1;
u := KC.2;

printf "%o places of degree 1\n", #Places(Caff, 1);

// =========================================================================
// Q(sqrt(-3)) decomposition:  Q1 = 2x^2 + (1-w)y^2 + (1+w)z^2
// =========================================================================
print "\n=== Q(sqrt(-3)) DECOMPOSITION ===";
q1_s := KC!(2*t^2 + (1-w)*u^2 + (1+w));
D_s := Divisor(q1_s);
supp_s, mults_s := Support(D_s);
printf "div(q1): %o places, mults = %o\n", #supp_s, mults_s;
all_even_s := &and[m mod 2 eq 0 : m in mults_s];
printf "All even: %o\n", all_even_s;
half_s := &+[Integers()!(mults_s[j] div 2) * supp_s[j] : j in [1..#supp_s]];

// =========================================================================
// Q(i) decomposition:  Q1 = 2x^2 + 2i*z^2
// =========================================================================
print "\n=== Q(i) DECOMPOSITION ===";
q1_i := KC!(2*t^2 + 2*im);
D_i := Divisor(q1_i);
supp_i, mults_i := Support(D_i);
printf "div(q1): %o places, mults = %o\n", #supp_i, mults_i;
all_even_i := &and[m mod 2 eq 0 : m in mults_i];
printf "All even: %o\n", all_even_i;
half_i := &+[Integers()!(mults_i[j] div 2) * supp_i[j] : j in [1..#supp_i]];

// =========================================================================
// Check both are 2-torsion and compare
// =========================================================================
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

// =========================================================================
// V_rat check: use ratios of bitangent lines
// Bitangent lines: L1=x+y+z, L2=x+y-z, L3=x-y+z, L4=x-y-z
// The ratios L_j/L_k give functions whose half-divisors span V_rat
// =========================================================================
print "\n=== V_rat GENERATORS ===";
L := [t+u+1, t+u-1, t-u+1, t-u-1];
Lnames := ["x+y+z", "x+y-z", "x-y+z", "x-y-z"];

// V_rat generators: half-divisors of div(L1/L2) and div(L1/L3)
vrat_gens := [];
vrat_names := [];
for pair in [<1,2>, <1,3>] do
    j := pair[1]; k := pair[2];
    ratio := KC!(L[j] / L[k]);
    D_ratio := Divisor(ratio);
    supp_r, mults_r := Support(D_ratio);
    ok := &and[m mod 2 eq 0 : m in mults_r];
    printf "%o / %o: mults = %o, all even: %o\n", Lnames[j], Lnames[k], mults_r, ok;
    if ok then
        half_r := &+[Integers()!(mults_r[i] div 2) * supp_r[i] : i in [1..#supp_r]];
        Append(~vrat_gens, half_r);
        Append(~vrat_names, Sprintf("%o/%o", Lnames[j], Lnames[k]));
    end if;
end for;

// Check if half_s and half_i are in V_rat
print "\n=== MEMBERSHIP IN V_rat ===";
for data in [<half_s, "half_s (Q(sqrt(-3)))">  , <half_i, "half_i (Q(i))">] do
    cls := data[1];
    name := data[2];
    printf "\n%o:\n", name;
    in_vrat := false;

    // Check cls = 0
    chk0, _ := IsPrincipal(cls);
    if chk0 then printf "  = 0 (trivial)\n"; in_vrat := true; continue data; end if;

    // Check cls = v1, v2, v1+v2
    if #vrat_gens ge 2 then
        chk1, _ := IsPrincipal(cls - vrat_gens[1]);
        if chk1 then printf "  = %o\n", vrat_names[1]; in_vrat := true;
            continue data; end if;

        chk2, _ := IsPrincipal(cls - vrat_gens[2]);
        if chk2 then printf "  = %o\n", vrat_names[2]; in_vrat := true;
            continue data; end if;

        chk3, _ := IsPrincipal(cls - vrat_gens[1] - vrat_gens[2]);
        if chk3 then printf "  = %o + %o\n", vrat_names[1], vrat_names[2];
            in_vrat := true; continue data; end if;

        // Also try with opposite signs (2-torsion so +/- same, but
        // Magma might not simplify)
        chk4, _ := IsPrincipal(cls + vrat_gens[1]);
        if chk4 then printf "  = -%o = %o\n", vrat_names[1], vrat_names[1];
            in_vrat := true; continue data; end if;

        chk5, _ := IsPrincipal(cls + vrat_gens[2]);
        if chk5 then printf "  = -%o = %o\n", vrat_names[2], vrat_names[2];
            in_vrat := true; continue data; end if;

        chk6, _ := IsPrincipal(cls + vrat_gens[1] + vrat_gens[2]);
        if chk6 then printf "  = -(%o + %o)\n", vrat_names[1], vrat_names[2];
            in_vrat := true; continue data; end if;

        chk7, _ := IsPrincipal(cls + vrat_gens[1] - vrat_gens[2]);
        if chk7 then printf "  = %o - %o\n", vrat_names[2], vrat_names[1];
            in_vrat := true; continue data; end if;

        chk8, _ := IsPrincipal(cls - vrat_gens[1] + vrat_gens[2]);
        if chk8 then printf "  = %o - %o\n", vrat_names[1], vrat_names[2];
            in_vrat := true; continue data; end if;
    end if;
    if not in_vrat then
        printf "  NOT in V_rat\n";
    end if;
end for;

// =========================================================================
// Cross-check at p = 37
// =========================================================================
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
