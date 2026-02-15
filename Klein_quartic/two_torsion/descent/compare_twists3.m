/*******************************************************************************
 * compare_twists3.m
 *
 * Focused comparison: V_rat and quadric decompositions for C2: x^4+y^4-z^4=0.
 *
 * Key correction: the isomorphism C1 -> C2 requires zeta_8 (not just i),
 * since zeta_8^4 = -1 sends z^4 to -z^4.
 ******************************************************************************/

function HalfPositive(D)
    B := D - D;
    for pl in Support(D) do
        v := Valuation(D, pl);
        if v gt 0 then B := B + (v div 2) * pl; end if;
    end for;
    return B;
end function;

function J2Subgroup(Cl, invs)
    gens := [];
    for i in [1..#invs] do
        if invs[i] ne 0 and invs[i] mod 2 eq 0 then
            Append(~gens, (invs[i] div 2) * Cl.i);
        end if;
    end for;
    if #gens eq 0 then return sub<Cl | Cl!0>; end if;
    return sub<Cl | gens>;
end function;

// =========================================================================
// Part 1: Quadric decomposition analysis for C2 over F_3
// C2: x^4+y^4-z^4=0. Over F_3 this is x^4+y^4+2z^4=0.
// =========================================================================
print "=== QUADRIC DECOMPOSITIONS OF x^4+y^4-z^4 OVER F_3 ===";
p := 3; Fp := GF(p);

// Function field setup
Fpt<t> := FunctionField(Fp);
Fptu<u> := PolynomialRing(Fpt);
f2 := u^4 + t^4 - 1;
assert IsIrreducible(f2);
FF2<uu2> := FunctionField(f2);
Cl2, m2 := ClassGroup(FF2);
invs2 := Invariants(Cl2);
printf "Cl(C2/F_3) invariants = %o\n", invs2;
J2 := J2Subgroup(Cl2, invs2);
printf "|J[2]| = %o\n\n", #J2;
printf "J[2] elements:\n";
for g in J2 do printf "  %o\n", g; end for;
printf "\n";

elt_t := FF2 ! t;
elt_u := FF2.1;

// Exhaustive search: F = x^4+y^4-z^4, find F + Q2^2 = Q1*Q3
R<X,Y,Z> := PolynomialRing(Fp, 3);
Ff := X^4 + Y^4 - Z^4;

classes_found := {};
class_info := [];
count := 0;

for a in Fp do
for b in Fp do
for c_ in Fp do
for d in Fp do
for e_ in Fp do
for ff_ in Fp do
    Q2 := a*X^2 + b*Y^2 + c_*Z^2 + d*X*Y + e_*X*Z + ff_*Y*Z;
    G := Ff + Q2^2;

    fac := Factorization(G);
    degs := Sort([<TotalDegree(f[1]), f[2]> : f in fac]);

    // Need two degree-2 factors (multiplicity 1 each)
    if degs ne [<2,1>, <2,1>] then continue; end if;

    Q1_h := fac[1][1]; Q3_h := fac[2][1];
    // Fix scalar
    prod := Q1_h * Q3_h;
    mons := Monomials(G);
    coeff_G := MonomialCoefficient(G, mons[1]);
    coeff_P := MonomialCoefficient(prod, mons[1]);
    if coeff_P eq 0 then continue; end if;
    Q1_h := (coeff_G/coeff_P) * Q1_h;
    if Q1_h*Q3_h - Q2^2 ne Ff then continue; end if;

    // Compute 2-torsion class via div(Q2/Q3)|_C
    q2_aff := Evaluate(Q2, [elt_t, elt_u, FF2!1]);
    q3_aff := Evaluate(Q3_h, [elt_t, elt_u, FF2!1]);
    if q2_aff eq 0 or q3_aff eq 0 then continue; end if;

    D := Divisor(q2_aff / q3_aff);
    cls := D @@ m2;

    if cls in J2 then
        if not (cls in classes_found) then
            Include(~classes_found, cls);
            count +:= 1;
            printf "Class #%o: %o  (Q2 = %o)\n", count, cls, Q2;
            Append(~class_info, <cls, Q2, Q1_h, Q3_h>);
        end if;
    end if;
end for;
end for;
end for;
end for;
end for;
end for;

printf "\nDistinct nonzero J[2] classes found: %o\n", #classes_found;
V_decomp := sub<Cl2 | [c : c in classes_found]> meet J2;
printf "Span in J[2]: order %o (J[2] has %o)\n", #V_decomp, #J2;
if #V_decomp eq #J2 then
    print "ALL of J[2] reached (expected: Br(F_3) = 0).";
else
    printf "Only %o/%o reached — checking if zero class was missed.\n",
        #V_decomp, #J2;
end if;

// =========================================================================
// Part 2: Q-rational bitangent analysis for C2
// C2 has Q-points: (1:0:1), (0:1:1), (1:0:-1), (0:1:-1), (-1:0:1), etc.
// What are its Q-rational bitangent lines?
//
// For C1: x^4+y^4+z^4=0, the Q-rational bitangents are x+y+z, x+y-z, x-y+z, -x+y+z.
// For C2: x^4+y^4-z^4=0, the S3-symmetry is broken (x,y are symmetric but z is special).
// The S2 symmetry x<->y remains, plus sign changes x->-x, y->-y.
//
// Search for bitangent lines of C2 over F_3:
// =========================================================================
print "\n=== BITANGENT LINES OF C2 OVER F_3 ===";
bt_count := 0;
bt_list := [];

for a0 in Fp do
for b0 in Fp do
for c0 in Fp do
    if <a0,b0,c0> eq <0,0,0> then continue; end if;
    L := a0*elt_t + b0*elt_u + c0;
    if L eq 0 then continue; end if;
    D := Divisor(L);
    supp := Support(D);
    pos_places := [pl : pl in supp | Valuation(D, pl) gt 0];
    pos_vals := [Valuation(D, pl) : pl in pos_places];
    pos_degs := [Degree(pl) : pl in pos_places];

    // Bitangent: two places of degree 1, each with val 2
    // Or one place of degree 2 with val 2 (bitangent with conjugate tangency points)
    if #pos_places eq 2 and pos_vals eq [2,2] and pos_degs eq [1,1] then
        bt_count +:= 1;
        Append(~bt_list, <a0,b0,c0>);
        printf "  Bitangent [%o:%o:%o] (two deg-1 tangencies)\n", a0,b0,c0;
    elif #pos_places eq 1 and pos_vals eq [2] and pos_degs eq [2] then
        bt_count +:= 1;
        Append(~bt_list, <a0,b0,c0>);
        printf "  Bitangent [%o:%o:%o] (one deg-2 tangency)\n", a0,b0,c0;
    end if;
end for;
end for;
end for;

printf "Total bitangent lines of C2 over F_3: %o\n\n", bt_count;

if bt_count ge 2 then
    // Compute bitangent difference classes
    ref := bt_list[1];
    ref_L := ref[1]*elt_t + ref[2]*elt_u + ref[3];
    ref_B := HalfPositive(Divisor(ref_L));
    printf "Reference bitangent: [%o:%o:%o]\n", ref[1], ref[2], ref[3];

    bt_classes := {};
    for i in [2..#bt_list] do
        info := bt_list[i];
        Li := info[1]*elt_t + info[2]*elt_u + info[3];
        Bi := HalfPositive(Divisor(Li));
        cls := (Bi - ref_B) @@ m2;
        if cls in J2 then
            Include(~bt_classes, cls);
            printf "  [%o:%o:%o]: class = %o\n", info[1], info[2], info[3], cls;
        end if;
    end for;
    V_bt := sub<Cl2 | [c : c in bt_classes]> meet J2;
    printf "V_rat from bitangents: order %o\n", #V_bt;
end if;

// =========================================================================
// Part 3: For comparison, same analysis for C1 over F_3
// =========================================================================
print "\n=== COMPARISON: C1 OVER F_3 ===";
f1 := u^4 + t^4 + 1;
// Need fresh function field
Fpt2<t2> := FunctionField(Fp);
Fptu2<u2> := PolynomialRing(Fpt2);
FF1<uu1> := FunctionField(u2^4 + t2^4 + 1);
Cl1, m1 := ClassGroup(FF1);
invs1 := Invariants(Cl1);
J2_1 := J2Subgroup(Cl1, invs1);
printf "Cl(C1/F_3) = %o, |J[2]| = %o\n", invs1, #J2_1;

elt_t1 := FF1 ! t2; elt_u1 := FF1.1;

// Q-rational bitangent lines for C1: x+y+z, x+y-z, x-y+z, -x+y+z
L1_1 := elt_t1+elt_u1+1; L2_1 := elt_t1+elt_u1-1;
L3_1 := elt_t1-elt_u1+1; L4_1 := -elt_t1+elt_u1+1;
B1 := HalfPositive(Divisor(L1_1)); B2 := HalfPositive(Divisor(L2_1));
B3 := HalfPositive(Divisor(L3_1)); B4 := HalfPositive(Divisor(L4_1));
P12 := (B1-B2) @@ m1; P13 := (B1-B3) @@ m1; P14 := (B1-B4) @@ m1;
V_rat_1 := sub<Cl1 | P12, P13> meet J2_1;
printf "V_rat(C1) order = %o (from 4 Q-rational bitangents)\n", #V_rat_1;
printf "P12=%o, P13=%o, P14=%o\n\n", P12, P13, P14;

// Non-V_rat classes
printf "J(C1)[2] \\ V_rat(C1):\n";
for g in J2_1 do
    if g ne Cl1!0 and not (g in V_rat_1) then
        printf "  %o\n", g;
    end if;
end for;

// Count bitangent lines of C1 over F_3
print "\nBitangent lines of C1 over F_3:";
bt1_count := 0;
for a0 in Fp do
for b0 in Fp do
for c0 in Fp do
    if <a0,b0,c0> eq <0,0,0> then continue; end if;
    L := a0*elt_t1 + b0*elt_u1 + c0;
    if L eq 0 then continue; end if;
    D := Divisor(L);
    supp := Support(D);
    pos_places := [pl : pl in supp | Valuation(D, pl) gt 0];
    pos_vals := [Valuation(D, pl) : pl in pos_places];
    pos_degs := [Degree(pl) : pl in pos_places];
    if #pos_places eq 2 and pos_vals eq [2,2] and pos_degs eq [1,1] then
        bt1_count +:= 1;
        printf "  [%o:%o:%o] (two deg-1 tangencies)\n", a0,b0,c0;
    elif #pos_places eq 1 and pos_vals eq [2] and pos_degs eq [2] then
        bt1_count +:= 1;
        printf "  [%o:%o:%o] (one deg-2 tangency)\n", a0,b0,c0;
    end if;
end for;
end for;
end for;
printf "Total: %o\n", bt1_count;

quit;
