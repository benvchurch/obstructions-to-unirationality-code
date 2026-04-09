/*******************************************************************************
 * check_cover_class.m
 *
 * Investigate whether g = (xy+z^2)(x^2y^2+z^4) on C: x^4+y^4+z^4=0
 * gives the "missing" 2-torsion class e3.
 *
 * Part 1: Detailed single-prime search over F_3 — systematic search for
 *         Q-rational functions giving e3.
 * Part 2: Multi-prime verification — test g across primes of good reduction.
 *
 * CONCLUSION: g does NOT give e3. It gives a class in V_rat (bitangent span).
 ******************************************************************************/


// =========== PART 1: SINGLE-PRIME SEARCH OVER F_3 ===========

p := 3;
Fp := GF(p);
Fpt<t> := FunctionField(Fp);
Fptu<u> := PolynomialRing(Fpt);
f := u^4 + t^4 + 1;
FF := FunctionField(f);
Cl, m := ClassGroup(FF);

elt_t := FF ! t;
elt_u := FF.1;

e1 := 2*Cl.1; e2 := 2*Cl.2; e3 := 2*Cl.3;
J2 := sub<Cl | e1, e2, e3>;

function HalfPositive(D)
    B := D - D;
    for pl in Support(D) do
        v := Valuation(D, pl);
        if v gt 0 then
            B := B + (v div 2) * pl;
        end if;
    end for;
    return B;
end function;

// Q-rational bitangent classes for reference
L1 := elt_t + elt_u + 1;
L2 := elt_t + elt_u - 1;
L3 := elt_t - elt_u + 1;
B1 := HalfPositive(Divisor(L1));
B2 := HalfPositive(Divisor(L2));
B3 := HalfPositive(Divisor(L3));
P12 := (B1-B2) @@ m;
P13 := (B1-B3) @@ m;
V_rat := sub<Cl | P12, P13>;

printf "e1 = %o, e2 = %o, e3 = %o\n", e1, e2, e3;
printf "P12 = %o, P13 = %o\n", P12, P13;
printf "V_rat = span(P12,P13), order %o\n\n", #(V_rat meet J2);

// ---- Test g = (xy+z^2)(x^2y^2+z^4) ----
print "=== TESTING g = (xy+z^2)(x^2y^2+z^4) ===";
g1 := elt_t*elt_u + 1;  // xy + z^2 (z=1)
g2 := elt_t^2*elt_u^2 + 1;  // x^2y^2 + z^4 (z=1)
g := g1 * g2;

printf "g = %o\n", g;
D_g := Divisor(g);
printf "div(g): degree %o\n", Degree(D_g);
for pl in Support(D_g) do
    v := Valuation(D_g, pl);
    printf "  degree-%o place, mult %o\n", Degree(pl), v;
end for;

// Check if div(g) is 2 times a divisor (even multiplicities)
all_even := true;
for pl in Support(D_g) do
    v := Valuation(D_g, pl);
    if v mod 2 ne 0 then
        all_even := false;
        printf "  ODD multiplicity at degree-%o place!\n", Degree(pl);
    end if;
end for;

if all_even then
    print "All multiplicities even: div(g) = 2D for some D.";
    D_half := HalfPositive(D_g) - HalfPositive(-D_g);
    cls_g := D_half @@ m;
    printf "2-torsion class [D] = %o\n", cls_g;
    printf "In J[2]? %o\n", cls_g in J2;
    printf "Equals e3? %o\n", cls_g eq e3;
    printf "In V_rat? %o\n", cls_g in V_rat;
else
    print "Odd multiplicities: g does NOT define an etale double cover.";
    print "The cover w^2 = g is ramified.";
end if;

// ---- Also test individual factors ----
print "";
print "=== TESTING g1 = xy+z^2 ===";
D_g1 := Divisor(g1);
printf "div(g1): degree %o\n", Degree(D_g1);
for pl in Support(D_g1) do
    v := Valuation(D_g1, pl);
    printf "  degree-%o place, mult %o\n", Degree(pl), v;
end for;

print "";
print "=== TESTING g2 = x^2y^2+z^4 ===";
D_g2 := Divisor(g2);
printf "div(g2): degree %o\n", Degree(D_g2);
for pl in Support(D_g2) do
    v := Valuation(D_g2, pl);
    printf "  degree-%o place, mult %o\n", Degree(pl), v;
end for;

// ---- Systematic search for Q-rational functions giving e3 ----
print "";
print "=== SYSTEMATIC SEARCH FOR Q-RATIONAL FUNCTIONS GIVING e3 ===";

simple_funcs := [
    <elt_t, "t">,
    <elt_u, "u">,
    <elt_t+1, "t+1">,
    <elt_t-1, "t-1">,
    <elt_u+1, "u+1">,
    <elt_u-1, "u-1">,
    <elt_t+elt_u, "t+u">,
    <elt_t-elt_u, "t-u">,
    <elt_t*elt_u+1, "tu+1">,
    <elt_t*elt_u-1, "tu-1">,
    <elt_t^2+1, "t^2+1">,
    <elt_u^2+1, "u^2+1">,
    <elt_t^2+elt_u^2, "t^2+u^2">,
    <elt_t^2-elt_u^2, "t^2-u^2">,
    <elt_t^2+elt_u^2+1, "t^2+u^2+1">,
    <elt_t^2+elt_u^2-1, "t^2+u^2-1">,
    <elt_t^2*elt_u^2+1, "t^2u^2+1">,
    <elt_t^2+elt_t*elt_u+elt_u^2, "t^2+tu+u^2">,
    <elt_t^2-elt_t*elt_u+elt_u^2, "t^2-tu+u^2">
];

// For each function, compute its class and check if it gives e3
print "Function classes (mod squares, i.e., in k(C)*/k(C)*^2 -> J[2]):";
for pair in simple_funcs do
    func := pair[1];
    name := pair[2];
    D_func := Divisor(func);
    cls := D_func @@ m;
    // Check if cls is in J[2] (i.e., 2*cls = 0)
    in_J2 := (2*cls eq Cl!0);
    if in_J2 then
        is_e3 := (cls eq e3) or (cls eq -e3);
        printf "  %o: class = %o  [IN J[2]", name, cls;
        if cls eq Cl!0 then
            printf ", TRIVIAL";
        elif is_e3 then
            printf ", = e3!!!";
        elif cls in V_rat then
            printf ", in V_rat";
        else
            printf ", NEW DIRECTION";
        end if;
        printf "]\n";
    end if;
end for;

// Also try products of two simple functions
print "";
print "Products of two functions (checking for e3):";
found_e3 := false;
for i in [1..#simple_funcs] do
    for j in [i..#simple_funcs] do
        func := simple_funcs[i][1] * simple_funcs[j][1];
        D_func := Divisor(func);
        cls := D_func @@ m;
        if cls eq e3 or cls eq -e3 then
            printf "  %o * %o: class = %o = e3!\n",
                   simple_funcs[i][2], simple_funcs[j][2], cls;
            found_e3 := true;
        end if;
    end for;
end for;

if not found_e3 then
    print "  No product of two simple functions gives e3.";
    print "  e3 may require functions defined over an extension field.";
end if;


// =========== PART 2: MULTI-PRIME VERIFICATION ===========

print "";
print "===============================================================";
print "PART 2: Multi-prime verification of g = (tu+1)(t^2u^2+1)";
print "===============================================================";

for p in [3, 7, 11, 13, 17, 19, 23, 31, 37, 41, 43] do
    if p eq 2 then continue; end if;

    printf "=== p = %o ===\n", p;
    Fp := GF(p);
    Fpt<t> := FunctionField(Fp);
    Fptu<u> := PolynomialRing(Fpt);
    f := u^4 + t^4 + 1;

    if not IsIrreducible(f) then
        printf "  u^4+t^4+1 reducible over F_%o, skipping.\n\n", p;
        continue;
    end if;

    FF := FunctionField(f);
    elt_t := FF ! t;
    elt_u := FF.1;

    // g = (xy+z^2)(x^2y^2+z^4) in affine chart z=1
    g1 := elt_t*elt_u + 1;
    g2 := elt_t^2*elt_u^2 + 1;
    g := g1 * g2;

    D_g := Divisor(g);

    // Check all-even multiplicities
    all_even := true;
    for pl in Support(D_g) do
        v := Valuation(D_g, pl);
        if v mod 2 ne 0 then
            all_even := false;
            printf "  ODD mult %o at degree-%o place\n", v, Degree(pl);
        end if;
    end for;

    if all_even then
        printf "  div(g) has ALL EVEN multiplicities.\n";

        // Compute the double cover
        Rw<w> := PolynomialRing(FF);
        h := w^2 - g;
        if IsIrreducible(h) then
            FD := ext<FF | h>;
            gD := Genus(FD);
            printf "  Double cover w^2=g has genus %o", gD;
            if gD eq 5 then
                printf " (ETALE, unramified)\n";
            else
                printf " (RAMIFIED)\n";
            end if;
        else
            printf "  w^2-g is REDUCIBLE (g is a square): trivial cover\n";
        end if;
    else
        printf "  div(g) has ODD multiplicities: NOT an etale cover!\n";
    end if;
    printf "\n";
end for;

// ---- Class check at p=3 ----
print "=== CLASS CHECK AT p=3 ===";
p := 3;
Fp := GF(p);
Fpt<t> := FunctionField(Fp);
Fptu<u> := PolynomialRing(Fpt);
f := u^4 + t^4 + 1;
FF := FunctionField(f);
Cl, m := ClassGroup(FF);
elt_t := FF ! t;
elt_u := FF.1;

e1 := 2*Cl.1; e2 := 2*Cl.2; e3 := 2*Cl.3;
J2 := sub<Cl | e1, e2, e3>;

// Q-rational bitangent classes
L1 := elt_t + elt_u + 1; L2 := elt_t + elt_u - 1;
L3 := elt_t - elt_u + 1; L4 := -elt_t + elt_u + 1;
B1 := HalfPositive(Divisor(L1)); B2 := HalfPositive(Divisor(L2));
B3 := HalfPositive(Divisor(L3)); B4 := HalfPositive(Divisor(L4));
P12 := (B1-B2) @@ m; P13 := (B1-B3) @@ m; P14 := (B1-B4) @@ m;
V_rat := sub<Cl | P12, P13>;

g := (elt_t*elt_u + 1)*(elt_t^2*elt_u^2 + 1);
D_g := Divisor(g);
D_half := HalfPositive(D_g) - HalfPositive(-D_g);
cls_g := D_half @@ m;

printf "g = (tu+1)(t^2u^2+1)\n";
printf "Class of (1/2)div(g) = %o\n", cls_g;
printf "e3 = %o\n", e3;
printf "Equals e3? %o\n", cls_g eq e3;
printf "In V_rat (bitangent span)? %o\n\n", cls_g in V_rat;

// Full span including g
V_full := sub<Cl | P12, P13, cls_g>;
V_full_J2 := V_full meet J2;
printf "Span of {P12, P13, class(g)} in J[2]: order %o\n", #V_full_J2;
printf "J[2] order: %o\n\n", #J2;

if #V_full_J2 eq #J2 then
    print "*** ALL of J[2] is now reached! ***";
else
    printf "Only %o/%o reached. g does NOT give the missing class.\n", #V_full_J2, #J2;
end if;

quit;
