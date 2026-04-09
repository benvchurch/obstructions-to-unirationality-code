/*******************************************************************************
 * compare_J2_subspaces2.m
 *
 * Compare J[2](Q) subspaces for C1 and C2 under the isomorphism φ.
 * Work over F_9 (smallest field containing ζ₈ and F_3).
 *
 * Strategy: generate J[2] from degree-1 place differences (not Cl generators),
 * compute Frobenius action, find fixed subspaces, and compare via φ.
 ******************************************************************************/

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

F9<a> := GF(9);

// Find ζ₈ in F_9
z8 := 0;
for x in F9 do
    if x ne 0 and x^4 eq F9!(-1) then z8 := x; break; end if;
end for;
printf "F_9 = F_3(%o), ζ₈ = %o\n\n", a, z8;

// =========================================================================
// C1: u^4 + t^4 + 1 = 0 over F_9
// =========================================================================
Fpt1<t1> := FunctionField(F9);
Ku1<U1> := PolynomialRing(Fpt1);
FF1<u1> := FunctionField(U1^4 + t1^4 + 1);
Cl1, m1 := ClassGroup(FF1);
invs1 := Invariants(Cl1);
J2_1 := J2Subgroup(Cl1, invs1);
printf "C1/F_9: Cl = %o, |J[2]| = %o\n", invs1, #J2_1;

// =========================================================================
// C2: v^4 + s^4 - 1 = 0 over F_9
// =========================================================================
Fpt2<s> := FunctionField(F9);
Ku2<V> := PolynomialRing(Fpt2);
FF2<v> := FunctionField(V^4 + s^4 - 1);
Cl2, m2 := ClassGroup(FF2);
invs2 := Invariants(Cl2);
J2_2 := J2Subgroup(Cl2, invs2);
printf "C2/F_9: Cl = %o, |J[2]| = %o\n\n", invs2, #J2_2;

// =========================================================================
// Enumerate affine degree-1 places
// =========================================================================
pls1 := Places(FF1, 1);
pls2 := Places(FF2, 1);

// Filter to affine places and build coordinate maps
function AffinePlaces(FF, t_var, u_var, pls, k)
    result := [];
    coords := AssociativeArray();
    for P in pls do
        if Valuation(FF!t_var, P) ge 0 and Valuation(u_var, P) ge 0 then
            tv := k!Evaluate(FF!t_var, P);
            uv := k!Evaluate(u_var, P);
            Append(~result, P);
            coords[P] := <tv, uv>;
        end if;
    end for;
    return result, coords;
end function;

aff1, coords1 := AffinePlaces(FF1, t1, u1, pls1, F9);
aff2, coords2 := AffinePlaces(FF2, s, v, pls2, F9);
printf "Affine deg-1 places: C1 has %o, C2 has %o\n", #aff1, #aff2;

// =========================================================================
// Build φ: C1 → C2 map on affine places
// φ: (t,u) → (t/ζ₈, u/ζ₈)
// =========================================================================
// Lookup for C2
lookup2 := AssociativeArray();
for P in aff2 do
    c := coords2[P];
    key := Sprint(c);
    lookup2[key] := P;
end for;

phi := AssociativeArray();
for P in aff1 do
    c := coords1[P];
    target := <c[1]/z8, c[2]/z8>;
    key := Sprint(target);
    if IsDefined(lookup2, key) then
        phi[P] := lookup2[key];
    end if;
end for;
printf "φ maps %o/%o affine places\n", #Keys(phi), #aff1;

// =========================================================================
// Build Frobenius_3 map: (t,u) → (t^3, u^3)
// =========================================================================
lookup1 := AssociativeArray();
for P in aff1 do
    c := coords1[P];
    key := Sprint(c);
    lookup1[key] := P;
end for;

frob1 := AssociativeArray();
for P in aff1 do
    c := coords1[P];
    target := <c[1]^3, c[2]^3>;
    key := Sprint(target);
    if IsDefined(lookup1, key) then
        frob1[P] := lookup1[key];
    end if;
end for;

frob2 := AssociativeArray();
for P in aff2 do
    c := coords2[P];
    target := <c[1]^3, c[2]^3>;
    key := Sprint(target);
    if IsDefined(lookup2, key) then
        frob2[P] := lookup2[key];
    end if;
end for;
printf "Frob_3 maps %o/%o places on C1, %o/%o on C2\n\n",
    #Keys(frob1), #aff1, #Keys(frob2), #aff2;

// =========================================================================
// Generate J[2] from degree-1 place differences
// Take a reference place P0, compute [P - P0] for all affine P.
// These generate a subgroup of Cl. Intersect with J2.
// =========================================================================
P0_1 := aff1[1];
P0_2 := aff2[1];

printf "=== GENERATING J[2] FROM PLACE DIFFERENCES ===\n";

// For C1
place_classes_1 := [];
for P in aff1 do
    D := 1*P - 1*P0_1;
    cls := D @@ m1;
    Append(~place_classes_1, cls);
end for;
gen_sub_1 := sub<Cl1 | place_classes_1> meet J2_1;
printf "C1: place differences generate subgroup of J[2] of order %o (need %o)\n",
    #gen_sub_1, #J2_1;

// For C2
place_classes_2 := [];
for P in aff2 do
    D := 1*P - 1*P0_2;
    cls := D @@ m2;
    Append(~place_classes_2, cls);
end for;
gen_sub_2 := sub<Cl2 | place_classes_2> meet J2_2;
printf "C2: place differences generate subgroup of J[2] of order %o (need %o)\n",
    #gen_sub_2, #J2_2;

// If we don't generate all of J[2], add more: use pairwise differences
if #gen_sub_1 lt #J2_1 then
    for i in [1..#aff1] do
    for j in [i+1..#aff1] do
        D := 1*aff1[i] - 1*aff1[j];
        cls := D @@ m1;
        gen_sub_1 := sub<Cl1 | Generators(gen_sub_1) join {cls}> meet J2_1;
    end for;
    end for;
    printf "C1: after pairwise, J[2] subgroup order = %o\n", #gen_sub_1;
end if;

if #gen_sub_2 lt #J2_2 then
    for i in [1..#aff2] do
    for j in [i+1..#aff2] do
        D := 1*aff2[i] - 1*aff2[j];
        cls := D @@ m2;
        gen_sub_2 := sub<Cl2 | Generators(gen_sub_2) join {cls}> meet J2_2;
    end for;
    end for;
    printf "C2: after pairwise, J[2] subgroup order = %o\n", #gen_sub_2;
end if;

// =========================================================================
// Compute Frobenius_3 action on J[2] elements
// For each g in J[2], express g = [P-Q] for degree-1 places, then
// Frob_3(g) = [Frob(P)-Frob(Q)].
// =========================================================================
printf "\n=== FROBENIUS_3 ON J[2] (via place representatives) ===\n";

// For each element of J[2](C2/F_9), compute Frob_3 image
printf "--- C2 ---\n";
frob3_fixed_C2 := {};
for g in J2_2 do
    // Find a representative: g = [P-P0] for some P, or more generally
    // g = sum n_i [P_i - P0]. Since g has order 2 and P-P0 generates,
    // we search for g among our computed classes.

    // Actually, let's use a different approach: for each g, find D = m2(g),
    // and manually compute Frob_3(D).
    D := m2(g);
    supp := Support(D);
    frobD := DivisorGroup(FF2) ! 0;
    ok := true;
    for P in supp do
        n := Valuation(D, P);
        if Degree(P) ne 1 or not IsDefined(frob2, P) then
            ok := false;
            break;
        end if;
        frobD := frobD + n * (1*frob2[P]);
    end for;

    if ok then
        frob_g := frobD @@ m2;
        if frob_g eq g then
            Include(~frob3_fixed_C2, g);
        end if;
    end if;
end for;
printf "|J[2](C2/F_9)^{Frob_3}| = %o (should be 8 = 2^3)\n", #frob3_fixed_C2;

// Same for C1
printf "\n--- C1 ---\n";
frob3_fixed_C1 := {};
for g in J2_1 do
    D := m1(g);
    supp := Support(D);
    frobD := DivisorGroup(FF1) ! 0;
    ok := true;
    for P in supp do
        n := Valuation(D, P);
        if Degree(P) ne 1 or not IsDefined(frob1, P) then
            ok := false;
            break;
        end if;
        frobD := frobD + n * (1*frob1[P]);
    end for;

    if ok then
        frob_g := frobD @@ m1;
        if frob_g eq g then
            Include(~frob3_fixed_C1, g);
        end if;
    end if;
end for;
printf "|J[2](C1/F_9)^{Frob_3}| = %o (should be 8 = 2^3)\n", #frob3_fixed_C1;

// =========================================================================
// Push forward fixed elements of C1 to C2 via φ
// =========================================================================
printf "\n=== PUSHFORWARD OF J[2](C1)^{Frob_3} TO C2 ===\n";
phi_fixed_images := {};
for g in frob3_fixed_C1 do
    D := m1(g);
    supp := Support(D);
    phiD := DivisorGroup(FF2) ! 0;
    ok := true;
    for P in supp do
        n := Valuation(D, P);
        if Degree(P) ne 1 or not IsDefined(phi, P) then
            ok := false;
            break;
        end if;
        phiD := phiD + n * (1*phi[P]);
    end for;

    if ok then
        phi_g := phiD @@ m2;
        printf "  %o -> %o", g, phi_g;
        in_fixed := phi_g in frob3_fixed_C2;
        printf " (in C2 fixed? %o)\n", in_fixed;
        Include(~phi_fixed_images, phi_g);
    else
        printf "  %o -> FAILED (higher-deg places in divisor)\n", g;
    end if;
end for;

phi_fixed_sub := sub<Cl2 | [g : g in phi_fixed_images]> meet J2_2;
printf "\nφ(J[2](C1)^{Frob_3}) generates subgroup of order %o in J[2](C2)\n",
    #phi_fixed_sub;
printf "J[2](C2)^{Frob_3} has order %o\n", #frob3_fixed_C2;

overlap := phi_fixed_sub meet sub<Cl2 | [g : g in frob3_fixed_C2]>;
printf "Intersection: order %o\n", #overlap;
printf "Are they equal? %o\n",
    #phi_fixed_sub eq #frob3_fixed_C2 and
    #overlap eq #frob3_fixed_C2;

quit;
