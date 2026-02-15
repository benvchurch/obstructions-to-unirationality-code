/*******************************************************************************
 * compare_twists2.m
 *
 * Corrected comparison of C1: x^4+y^4+z^4=0 and C2: x^4+y^4-z^4=0.
 * Fixes: proper J[2] computation, correct 2-rank (exclude free part).
 ******************************************************************************/

// =========================================================================
// Helper: compute 2-rank of J(C)(F_p) from class group invariants
// Invariants include a 0 for the free part (degree map) — exclude it.
// =========================================================================
function TwoRank(invs)
    return #[d : d in invs | d ne 0 and d mod 2 eq 0];
end function;

// =========================================================================
// Helper: compute J[2] as subgroup of class group Cl
// J[2] = {g in Cl_tors : 2g = 0} = 2-torsion of the torsion part
// =========================================================================
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

function HalfPositive(D)
    B := D - D;
    for pl in Support(D) do
        v := Valuation(D, pl);
        if v gt 0 then B := B + (v div 2) * pl; end if;
    end for;
    return B;
end function;

// =========================================================================
// Part A: Corrected 2-rank comparison
// =========================================================================
print "=== 2-RANK OF J(C)(F_p) (corrected) ===";
printf "%-5o %-6o  %-10o %-10o  %-10o %-10o\n",
    "p", "p%8", "2rk(C1)", "J(C1)", "2rk(C2)", "J(C2)";

for p in [3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97] do
    Fp := GF(p);
    Fpt<t> := FunctionField(Fp);
    Fptu<u> := PolynomialRing(Fpt);

    f1 := u^4 + t^4 + 1;
    f2 := u^4 + t^4 - 1;

    rk1 := -1; rk2 := -1;
    s1 := ""; s2 := "";

    if IsIrreducible(f1) then
        Cl1 := ClassGroup(FunctionField(f1));
        invs1 := Invariants(Cl1);
        rk1 := TwoRank(invs1);
        for i in [1..#invs1] do
            if i gt 1 then s1 cat:= "x"; end if;
            if invs1[i] eq 0 then s1 cat:= "Z"; else s1 cat:= Sprintf("%o", invs1[i]); end if;
        end for;
    end if;

    if IsIrreducible(f2) then
        Cl2 := ClassGroup(FunctionField(f2));
        invs2 := Invariants(Cl2);
        rk2 := TwoRank(invs2);
        for i in [1..#invs2] do
            if i gt 1 then s2 cat:= "x"; end if;
            if invs2[i] eq 0 then s2 cat:= "Z"; else s2 cat:= Sprintf("%o", invs2[i]); end if;
        end for;
    end if;

    printf "%-5o %-6o  %-10o %-10o  %-10o %-10o\n", p, p mod 8, rk1, s1, rk2, s2;
end for;

// =========================================================================
// Part B: At p=13 (both sqrt(-1) and sqrt(-3) exist)
// Correctly compute J[2], V_rat, and transport eta.
// =========================================================================
print "\n=== DETAILED ANALYSIS AT p=13 ===";
p := 13; Fp := GF(p);
ii := Sqrt(Fp!(-1));
w := Sqrt(Fp!(-3));
printf "p=%o, i=%o, w=%o\n\n", p, ii, w;

Fpt<t> := FunctionField(Fp);
Fptu<u> := PolynomialRing(Fpt);

// --- C1 ---
print "--- C1: x^4+y^4+z^4=0 ---";
FF1<uu1> := FunctionField(u^4 + t^4 + 1);
Cl1, m1 := ClassGroup(FF1);
invs1 := Invariants(Cl1);
printf "Cl = %o\n", invs1;
J2_1 := J2Subgroup(Cl1, invs1);
printf "|J[2]| = %o (2-rank = %o)\n", #J2_1, TwoRank(invs1);

elt_t1 := FF1 ! t; elt_u1 := FF1.1;

// Q-rational bitangent lines: x+y+z, x+y-z, x-y+z, -x+y+z
// In affine z=1: t+u+1, t+u-1, t-u+1, -t+u+1
L1_1 := elt_t1+elt_u1+1;
L2_1 := elt_t1+elt_u1-1;
L3_1 := elt_t1-elt_u1+1;
L4_1 := -elt_t1+elt_u1+1;

B1 := HalfPositive(Divisor(L1_1));
B2 := HalfPositive(Divisor(L2_1));
B3 := HalfPositive(Divisor(L3_1));
B4 := HalfPositive(Divisor(L4_1));

P12 := (B1-B2) @@ m1; P13 := (B1-B3) @@ m1;
printf "P12=%o, P13=%o\n", P12, P13;
printf "P12 in J[2]? %o, P13 in J[2]? %o\n", P12 in J2_1, P13 in J2_1;

V_rat_1 := sub<Cl1 | P12, P13> meet J2_1;
printf "V_rat(C1) order = %o\n", #V_rat_1;

// eta from quadric Q1 = 2x^2+(1-w)y^2+(1+w)z^2
// Affine z=1: q1 = 2t^2+(1-w)u^2+(1+w)
q1_1 := 2*elt_t1^2 + (1-w)*elt_u1^2 + (1+w);
Dq1 := Divisor(q1_1);
eta_div := HalfPositive(Dq1) - HalfPositive(-Dq1);
eta_1 := eta_div @@ m1;
printf "eta = %o\n", eta_1;
printf "eta in J[2]? %o\n", eta_1 in J2_1;
printf "eta in V_rat? %o\n", eta_1 in V_rat_1;

// --- C2 ---
print "\n--- C2: x^4+y^4-z^4=0 ---";
FF2<uu2> := FunctionField(u^4 + t^4 - 1);
Cl2, m2 := ClassGroup(FF2);
invs2 := Invariants(Cl2);
printf "Cl = %o\n", invs2;
J2_2 := J2Subgroup(Cl2, invs2);
printf "|J[2]| = %o (2-rank = %o)\n", #J2_2, TwoRank(invs2);

elt_t2 := FF2 ! t; elt_u2 := FF2.1;

// The TWIST of C1's Q-rational bitangents: x+y+iz, x+y-iz, x-y+iz, -x+y+iz
// These are NOT Q-rational (involve i), so NOT in V_rat(C2).
// But let's compute them to identify where they sit in J(C2)[2].
Lt1 := elt_t2+elt_u2+ii; Lt2 := elt_t2+elt_u2-ii;
Lt3 := elt_t2-elt_u2+ii; Lt4 := -elt_t2+elt_u2+ii;

Bt1 := HalfPositive(Divisor(Lt1)); Bt2 := HalfPositive(Divisor(Lt2));
Bt3 := HalfPositive(Divisor(Lt3)); Bt4 := HalfPositive(Divisor(Lt4));

Pt12 := (Bt1-Bt2) @@ m2; Pt13 := (Bt1-Bt3) @@ m2; Pt14 := (Bt1-Bt4) @@ m2;
printf "Twisted bitangent diffs: Pt12=%o, Pt13=%o, Pt14=%o\n", Pt12, Pt13, Pt14;
printf "In J[2]? %o, %o, %o\n", Pt12 in J2_2, Pt13 in J2_2, Pt14 in J2_2;

V_twist := sub<Cl2 | Pt12, Pt13> meet J2_2;
printf "V_twist order = %o\n", #V_twist;

// Transport eta to C2 via phi: C1 -> C2, (x:y:z)->(x:y:iz)
// Inverse: (x:y:z)->(x:y:-iz) for C2->C1
// Affine: C1 point (t,u) maps to (t/i, u/i) = (-it, -iu) on C2
// So q1(t1,u1) = 2t1^2+(1-w)u1^2+(1+w) becomes
// q1(-it2, -iu2) = 2(-it2)^2 + (1-w)(-iu2)^2 + (1+w) = -2t2^2-(1-w)u2^2+(1+w)
q1_2 := -2*elt_t2^2 - (1-w)*elt_u2^2 + (1+w);
printf "\nTransported q1 on C2\n";
Dq1_2 := Divisor(q1_2);
eta_div_2 := HalfPositive(Dq1_2) - HalfPositive(-Dq1_2);
eta_2 := eta_div_2 @@ m2;
printf "eta_transported = %o\n", eta_2;
printf "In J[2]? %o\n", eta_2 in J2_2;
printf "In V_twist? %o\n", eta_2 in V_twist;

// --- What IS V_rat(C2)? ---
// C2: x^4+y^4=z^4 has Q-points: (1:0:1), (0:1:1), (1:0:-1), (0:1:-1), etc.
// But what are its Q-rational BITANGENT lines?
// Search: for each line ax+by+cz with a,b,c in F_p, check if it's bitangent to C2.
print "\n--- Searching for bitangent lines of C2 ---";
bitangent_info := [];
for a in Fp do
for b in Fp do
for c in Fp do
    if <a,b,c> eq <0,0,0> then continue; end if;
    // Normalize: first nonzero coeff = 1
    if a ne 0 then
        b := b/a; c := c/a; a := Fp!1;
    elif b ne 0 then
        c := c/b; b := Fp!1;
    else
        c := Fp!1;
    end if;

    L := a*elt_t2 + b*elt_u2 + c;
    if L eq 0 then continue; end if;
    D := Divisor(L);
    supp := Support(D);
    pos_places := [pl : pl in supp | Valuation(D, pl) gt 0];
    pos_vals := [Valuation(D, pl) : pl in pos_places];

    // Bitangent: two places of degree 1, each with valuation 2
    is_bitangent := (#pos_places eq 2) and
                    forall{v : v in pos_vals | v eq 2} and
                    forall{pl : pl in pos_places | Degree(pl) eq 1};
    if is_bitangent then
        Append(~bitangent_info, <a,b,c>);
    end if;
end for;
end for;
end for;

// Remove duplicates (from normalization)
seen := {};
unique_bt := [];
for info in bitangent_info do
    key := Sprint(info);
    if not (key in seen) then
        Include(~seen, key);
        Append(~unique_bt, info);
    end if;
end for;

printf "Bitangent lines of C2 over F_%o: %o\n", p, #unique_bt;
if #unique_bt gt 0 then
    // Compute classes
    ref_L := unique_bt[1][1]*elt_t2 + unique_bt[1][2]*elt_u2 + unique_bt[1][3];
    ref_B := HalfPositive(Divisor(ref_L));
    printf "Reference bitangent: (%o, %o, %o)\n", unique_bt[1][1], unique_bt[1][2], unique_bt[1][3];

    bt_classes := {};
    for i in [2..#unique_bt] do
        info := unique_bt[i];
        Li := info[1]*elt_t2 + info[2]*elt_u2 + info[3];
        Bi := HalfPositive(Divisor(Li));
        cls := (Bi - ref_B) @@ m2;
        if cls in J2_2 then
            Include(~bt_classes, cls);
            printf "  Bitangent (%o,%o,%o): class = %o\n", info[1], info[2], info[3], cls;
        end if;
    end for;
    printf "Distinct J[2] classes from F_%o-bitangents: %o\n", p, #bt_classes;
end if;

// --- Check conjugate-pair bitangent lines ---
// These come from (a+bi)x + ... = 0 where σ swaps the pair.
// Over F_p with p≡1 mod 4: i exists, so conjugate pairs become two F_p-lines.
// Over Q: a Q-rational conjugate pair {L, σ(L)} gives class [B_L+B_{σ(L)}-2B_ref]
// This is harder to compute systematically, so let's use the quadric approach instead.

print "\n--- Quadric decomposition approach for V_rat(C2) ---";
// For C2: x^4+y^4-z^4 = Q1*Q3 - Q2^2 over Q?
// The Q-rational bitangent classes of C1 come from Q2 with rational coefficients.
// For C2, we need x^4+y^4-z^4 = Q1*Q3 - Q2^2.
// Search over F_p for decompositions.

R<X,Y,Z> := PolynomialRing(Fp, 3);
Ff2 := X^4 + Y^4 - Z^4;
classes_C2 := {};

printf "Searching quadric decompositions of x^4+y^4-z^4 over F_%o...\n", p;
count := 0;
for a in Fp do
for b in Fp do
for c_ in Fp do
for d in Fp do
for e_ in Fp do
for f_ in Fp do
    Q2 := a*X^2 + b*Y^2 + c_*Z^2 + d*X*Y + e_*X*Z + f_*Y*Z;
    G := Ff2 + Q2^2;
    fac := Factorization(G);
    // Check if G factors into two quadratics
    degs := [TotalDegree(f[1]) : f in fac];
    mults := [f[2] : f in fac];
    if degs eq [2,2] and mults eq [1,1] then
        Q1 := fac[1][1]; Q3 := fac[2][1];
        // Adjust for scalar
        prod := Q1*Q3;
        mons := Monomials(Ff2+Q2^2);
        if #mons gt 0 then
            coeff_G := MonomialCoefficient(Ff2+Q2^2, mons[1]);
            coeff_P := MonomialCoefficient(prod, mons[1]);
            if coeff_P ne 0 then
                scalar := coeff_G / coeff_P;
                Q1 := scalar * Q1;
            end if;
        end if;
        if Q1*Q3 - Q2^2 eq Ff2 then
            // Compute torsion class via div(Q2/Q3)|_C
            q2_aff := Evaluate(Q2, [elt_t2, elt_u2, FF2!1]);
            q3_aff := Evaluate(Q3, [elt_t2, elt_u2, FF2!1]);
            if q3_aff ne 0 and q2_aff ne 0 then
                cls := Divisor(q2_aff/q3_aff) @@ m2;
                if cls in J2_2 and cls ne Cl2!0 then
                    if not (cls in classes_C2) then
                        Include(~classes_C2, cls);
                        count +:= 1;
                        if count le 10 then
                            printf "  Class: %o  (Q2=%o)\n", cls, Q2;
                        end if;
                    end if;
                end if;
            end if;
        end if;
    end if;
end for;
end for;
end for;
end for;
end for;
end for;

printf "Distinct nonzero J[2] classes from quadric decompositions: %o\n", #classes_C2;
V_quad := sub<Cl2 | [c : c in classes_C2]> meet J2_2;
printf "Span in J[2]: order %o out of %o\n", #V_quad, #J2_2;

// =========================================================================
// Summary
// =========================================================================
print "\n=== SUMMARY ===";
printf "J(C1)[2](F_%o) = (Z/2Z)^%o\n", p, TwoRank(invs1);
printf "V_rat(C1) order = %o\n", #V_rat_1;
printf "eta in V_rat(C1)? %o\n\n", eta_1 in V_rat_1;

printf "J(C2)[2](F_%o) = (Z/2Z)^%o\n", p, TwoRank(invs2);
printf "V_twist order = %o (from twisted bitangents)\n", #V_twist;
printf "eta_transported in V_twist? %o\n", eta_2 in V_twist;
printf "Quadric V_rat(C2) order = %o\n", #V_quad;
if eta_2 in J2_2 then
    printf "eta_transported in V_quad? %o\n", eta_2 in V_quad;
end if;

quit;
