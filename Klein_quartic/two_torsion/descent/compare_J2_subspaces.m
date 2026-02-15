/*******************************************************************************
 * compare_J2_subspaces.m
 *
 * At p ≡ 1 mod 8, C1 ≅ C2 via φ: (x:y:z) → (x:y:ζ₈z) where ζ₈^4 = -1.
 * Both have J[2] = (Z/2Z)^6 over F_p.
 *
 * Question: does φ map J(C1)[2](Q) to J(C2)[2](Q)?
 * Strategy: construct φ via places, push forward J[2] generators.
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

p := 17;
Fp := GF(p);

// Find zeta_8 in F_p
// ζ₈ satisfies x^8 = 1, x^4 = -1
z8 := 0;
for a in Fp do
    if a ne 0 and a^4 eq Fp!(-1) then z8 := a; break; end if;
end for;
assert z8 ne 0;
assert z8^4 eq -1;
printf "p = %o, zeta_8 = %o (zeta_8^4 = %o)\n\n", p, z8, z8^4;

// =========================================================================
// Set up C1: u^4 + t^4 + 1 = 0
// =========================================================================
Fpt1<t1> := FunctionField(Fp);
Ku1<U1> := PolynomialRing(Fpt1);
FF1<u1> := FunctionField(U1^4 + t1^4 + 1);
Cl1, m1 := ClassGroup(FF1);
invs1 := Invariants(Cl1);
printf "C1: Cl = %o\n", invs1;
J2_1 := J2Subgroup(Cl1, invs1);
printf "|J[2](C1)| = %o\n\n", #J2_1;

// =========================================================================
// Set up C2: v^4 + s^4 - 1 = 0
// =========================================================================
Fpt2<s> := FunctionField(Fp);
Ku2<V> := PolynomialRing(Fpt2);
FF2<v> := FunctionField(V^4 + s^4 - 1);
Cl2, m2 := ClassGroup(FF2);
invs2 := Invariants(Cl2);
printf "C2: Cl = %o\n", invs2;
J2_2 := J2Subgroup(Cl2, invs2);
printf "|J[2](C2)| = %o\n\n", #J2_2;

// =========================================================================
// Enumerate degree-1 places of both curves
// =========================================================================
places1 := Places(FF1, 1);
places2 := Places(FF2, 1);
printf "#degree-1 places: C1 has %o, C2 has %o\n\n", #places1, #places2;

// =========================================================================
// Build the isomorphism φ: C1 → C2 via places
// φ: (t,u) on C1 → (t/ζ₈, u/ζ₈) on C2
// For each place P of C1, compute (t(P), u(P)), then find the place of C2
// with coordinates (t(P)/ζ₈, u(P)/ζ₈).
// =========================================================================

// Helper: evaluate affine coordinates at a degree-1 place
// Returns false if the place is at infinity (pole of t or u)
function PlaceCoords1(P)
    if Valuation(FF1!t1, P) lt 0 or Valuation(u1, P) lt 0 then
        return false, Fp!0, Fp!0;
    end if;
    return true, Fp!Evaluate(FF1!t1, P), Fp!Evaluate(u1, P);
end function;

function PlaceCoords2(P)
    if Valuation(FF2!s, P) lt 0 or Valuation(v, P) lt 0 then
        return false, Fp!0, Fp!0;
    end if;
    return true, Fp!Evaluate(FF2!s, P), Fp!Evaluate(v, P);
end function;

// Build lookup table for C2 places (affine only)
C2_lookup := AssociativeArray();
for P in places2 do
    ok, sv, vv := PlaceCoords2(P);
    if ok then
        key := Sprint(<sv, vv>);
        C2_lookup[key] := P;
    end if;
end for;

// Map each C1 place to a C2 place via φ
phi_map := AssociativeArray();
unmapped := 0;
for P in places1 do
    ok, tv, uv := PlaceCoords1(P);
    if not ok then unmapped +:= 1; continue; end if;
    // φ: (t,u) → (t/ζ₈, u/ζ₈)
    target_s := Fp!(tv / z8);
    target_v := Fp!(uv / z8);
    key := Sprint(<target_s, target_v>);
    if IsDefined(C2_lookup, key) then
        phi_map[P] := C2_lookup[key];
    else
        unmapped +:= 1;
    end if;
end for;
printf "Mapped %o places, unmapped %o\n\n", #Keys(phi_map), unmapped;

// =========================================================================
// Push forward J[2] elements from C1 to C2
// A J[2] element g ∈ Cl1 maps to divisor D = m1(g).
// Push forward: φ_*(D) = Σ n_i · φ(P_i).
// Then identify the class of φ_*(D) in Cl2.
// =========================================================================
printf "=== PUSHFORWARD OF J[2](C1) GENERATORS TO C2 ===\n";

// Get J[2] generators
j2_gens_1 := [];
for i in [1..#invs1] do
    if invs1[i] ne 0 and invs1[i] mod 2 eq 0 then
        Append(~j2_gens_1, (invs1[i] div 2) * Cl1.i);
    end if;
end for;

for idx in [1..#j2_gens_1] do
    g := j2_gens_1[idx];
    D := m1(g);
    supp := Support(D);

    // Build pushed-forward divisor
    phiD := DivisorGroup(FF2) ! 0;
    ok := true;
    for P in supp do
        n := Valuation(D, P);
        deg := Degree(P);
        if deg ne 1 then
            printf "Gen %o: involves degree-%o place, skipping\n", idx, deg;
            ok := false;
            break;
        end if;
        if IsDefined(phi_map, P) then
            phiD := phiD + n * (1*phi_map[P]);
        else
            printf "Gen %o: place not in map, skipping\n", idx;
            ok := false;
            break;
        end if;
    end for;

    if not ok then continue; end if;

    // Identify class in Cl2
    cls2 := phiD @@ m2;
    in_J2 := cls2 in J2_2;
    printf "Gen %o: %o -> %o (in J[2]? %o)\n", idx, g, cls2, in_J2;
end for;

// =========================================================================
// Now identify which elements of J[2](C1) and J[2](C2) are Q-rational.
// "Q-rational" = fixed by all Frobenii = the 3-dim subspace that persists
// at all primes.
//
// Strategy: compute J[2](F_q) for several primes q with different residue
// classes mod 8, and intersect the fixed subspaces.
// At q ≡ 3 mod 8: J[2](F_q) has 2-rank 3 for BOTH curves → this IS J[2](Q).
// So we just need to compare J[2](F_3) for both curves under the isomorphism.
// =========================================================================
printf "\n=== IDENTIFYING J[2](Q) VIA F_3 ===\n";

// Compute J[2](C1/F_3) and J[2](C2/F_3) and see if they map to each other.
// But C1 and C2 are NOT isomorphic over F_3 (no ζ₈).
// So we need to:
//   1. Compute J[2](F_3) for both (each has 8 elements = (Z/2Z)^3)
//   2. Embed each into J[2](F_{3^k}) for k such that ζ₈ ∈ F_{3^k}
//   3. Use the isomorphism there to compare

// ζ₈ ∈ F_{3^k} iff 8 | (3^k - 1). 3^1=3, 3^2=9, 3^4=81.
// 3-1=2, 9-1=8. So ζ₈ ∈ F_9. Good.

printf "Working over F_9 where ζ₈ exists...\n";
F9<a> := GF(9);
z8_9 := 0;
for x in F9 do
    if x ne 0 and x^4 eq F9!(-1) then z8_9 := x; break; end if;
end for;
printf "ζ₈ in F_9 = %o (ζ₈^4 = %o)\n", z8_9, z8_9^4;

// C1 and C2 over F_9
Fpt9_1<tt1> := FunctionField(F9);
Kuu1<UU1> := PolynomialRing(Fpt9_1);
GG1<uu1> := FunctionField(UU1^4 + tt1^4 + 1);
CCl1, mm1 := ClassGroup(GG1);
iinvs1 := Invariants(CCl1);
JJ2_1 := J2Subgroup(CCl1, iinvs1);
printf "\nC1/F_9: Cl = %o, |J[2]| = %o\n", iinvs1, #JJ2_1;

Fpt9_2<tt2> := FunctionField(F9);
Kuu2<UU2> := PolynomialRing(Fpt9_2);
GG2<uu2> := FunctionField(UU2^4 + tt2^4 - 1);
CCl2, mm2 := ClassGroup(GG2);
iinvs2 := Invariants(CCl2);
JJ2_2 := J2Subgroup(CCl2, iinvs2);
printf "C2/F_9: Cl = %o, |J[2]| = %o\n", iinvs2, #JJ2_2;

// Enumerate places over F_9
pls1_9 := Places(GG1, 1);
pls2_9 := Places(GG2, 1);
printf "#deg-1 places: C1/F_9 has %o, C2/F_9 has %o\n\n", #pls1_9, #pls2_9;

// Build φ: C1 → C2 over F_9
C2_lookup_9 := AssociativeArray();
for P in pls2_9 do
    if Valuation(GG2!tt2, P) lt 0 or Valuation(uu2, P) lt 0 then continue; end if;
    sv := F9!Evaluate(GG2!tt2, P); vv := F9!Evaluate(uu2, P);
    key := Sprint(<sv, vv>);
    C2_lookup_9[key] := P;
end for;

phi9 := AssociativeArray();
for P in pls1_9 do
    if Valuation(GG1!tt1, P) lt 0 or Valuation(uu1, P) lt 0 then continue; end if;
    tv := F9!Evaluate(GG1!tt1, P); uv := F9!Evaluate(uu1, P);
    target_s := F9!(tv / z8_9);
    target_v := F9!(uv / z8_9);
    key := Sprint(<target_s, target_v>);
    if IsDefined(C2_lookup_9, key) then
        phi9[P] := C2_lookup_9[key];
    end if;
end for;
printf "Mapped %o/%o places via φ over F_9\n", #Keys(phi9), #pls1_9;

// Push forward J[2] generators of C1/F_9 to C2/F_9
printf "\n=== PUSHFORWARD OF J[2](C1/F_9) TO C2/F_9 ===\n";
jj2_gens_1 := [];
for i in [1..#iinvs1] do
    if iinvs1[i] ne 0 and iinvs1[i] mod 2 eq 0 then
        Append(~jj2_gens_1, (iinvs1[i] div 2) * CCl1.i);
    end if;
end for;
printf "C1/F_9 has %o J[2] generators\n", #jj2_gens_1;

phi_images := [];
for idx in [1..#jj2_gens_1] do
    g := jj2_gens_1[idx];
    D := mm1(g);
    supp := Support(D);

    phiD := DivisorGroup(GG2) ! 0;
    ok := true;
    for P in supp do
        n := Valuation(D, P);
        if Degree(P) ne 1 then
            printf "Gen %o: degree-%o place\n", idx, Degree(P);
            ok := false;
            break;
        end if;
        if IsDefined(phi9, P) then
            phiD := phiD + n * (1*phi9[P]);
        else
            printf "Gen %o: unmapped place\n", idx;
            ok := false;
            break;
        end if;
    end for;

    if ok then
        cls2 := phiD @@ mm2;
        in_J2 := cls2 in JJ2_2;
        Append(~phi_images, cls2);
        printf "Gen %o: %o -> %o (in J[2]? %o)\n", idx, g, cls2, in_J2;
    else
        Append(~phi_images, CCl2!0);
    end if;
end for;

// =========================================================================
// Now the key test: Frobenius_3 on J[2]
// Over F_9 ⊃ F_3, Frobenius_3 acts on places by the 3rd power Frobenius.
// J[2](F_3) = subspace of J[2](F_9) fixed by Frob_3.
// We compute Frob_3 action on J[2] for both curves.
// =========================================================================
printf "\n=== FROBENIUS_3 ACTION ON J[2] ===\n";
printf "(Frob_3 acts on F_9 = F_3(a) by a -> a^3)\n\n";

// Frob_3 on a place P: if P corresponds to (t0, u0) in F_9,
// then Frob_3(P) corresponds to (t0^3, u0^3).

function FrobPlace(places, FF, t_var, u_var, q, lookup, k)
    frob_map := AssociativeArray();
    for P in places do
        if Valuation(FF!t_var, P) lt 0 or Valuation(u_var, P) lt 0 then
            continue;
        end if;
        tv := k!Evaluate(FF!t_var, P);
        uv := k!Evaluate(u_var, P);
        target_t := tv^q;
        target_u := uv^q;
        key := Sprint(<target_t, target_u>);
        if IsDefined(lookup, key) then
            frob_map[P] := lookup[key];
        end if;
    end for;
    return frob_map;
end function;

// Lookup for C1/F_9
C1_lookup_9 := AssociativeArray();
for P in pls1_9 do
    if Valuation(GG1!tt1, P) lt 0 or Valuation(uu1, P) lt 0 then continue; end if;
    tv := F9!Evaluate(GG1!tt1, P); uv := F9!Evaluate(uu1, P);
    key := Sprint(<tv, uv>);
    C1_lookup_9[key] := P;
end for;

frob3_C1 := FrobPlace(pls1_9, GG1, tt1, uu1, 3, C1_lookup_9, F9);
frob3_C2 := FrobPlace(pls2_9, GG2, tt2, uu2, 3, C2_lookup_9, F9);

printf "Frob_3 mapped %o/%o places on C1, %o/%o on C2\n",
    #Keys(frob3_C1), #pls1_9, #Keys(frob3_C2), #pls2_9;

// Compute Frob_3 action on J[2] generators
printf "\n--- Frob_3 on J[2](C1/F_9) ---\n";
for idx in [1..#jj2_gens_1] do
    g := jj2_gens_1[idx];
    D := mm1(g);
    supp := Support(D);

    frobD := DivisorGroup(GG1) ! 0;
    ok := true;
    for P in supp do
        n := Valuation(D, P);
        if Degree(P) ne 1 then ok := false; break; end if;
        if IsDefined(frob3_C1, P) then
            frobD := frobD + n * (1*frob3_C1[P]);
        else
            ok := false; break;
        end if;
    end for;

    if ok then
        frob_cls := frobD @@ mm1;
        fixed := (frob_cls eq g);
        printf "Gen %o: Frob_3(%o) = %o, fixed? %o\n", idx, g, frob_cls, fixed;
    else
        printf "Gen %o: could not compute Frob_3\n", idx;
    end if;
end for;

// Same for C2
printf "\n--- Frob_3 on J[2](C2/F_9) ---\n";
jj2_gens_2 := [];
for i in [1..#iinvs2] do
    if iinvs2[i] ne 0 and iinvs2[i] mod 2 eq 0 then
        Append(~jj2_gens_2, (iinvs2[i] div 2) * CCl2.i);
    end if;
end for;

for idx in [1..#jj2_gens_2] do
    g := jj2_gens_2[idx];
    D := mm2(g);
    supp := Support(D);

    frobD := DivisorGroup(GG2) ! 0;
    ok := true;
    for P in supp do
        n := Valuation(D, P);
        if Degree(P) ne 1 then ok := false; break; end if;
        if IsDefined(frob3_C2, P) then
            frobD := frobD + n * (1*frob3_C2[P]);
        else
            ok := false; break;
        end if;
    end for;

    if ok then
        frob_cls := frobD @@ mm2;
        fixed := (frob_cls eq g);
        printf "Gen %o: Frob_3(%o) = %o, fixed? %o\n", idx, g, frob_cls, fixed;
    else
        printf "Gen %o: could not compute Frob_3\n", idx;
    end if;
end for;

// =========================================================================
// Finally: compare the fixed subspaces under the isomorphism
// J[2](Q) for C1 = Frob_3-fixed subspace of J[2](C1/F_9)
// Under φ, this maps to some subspace of J[2](C2/F_9).
// Question: is this the same as J[2](Q) for C2?
// =========================================================================
printf "\n=== COMPARING J[2](Q) SUBSPACES ===\n";
printf "The Frob_3-fixed subspace of J[2](C1/F_9), pushed forward via φ,\n";
printf "should be compared to the Frob_3-fixed subspace of J[2](C2/F_9).\n";
printf "If they match, J[2](Q) is 'the same' subspace under the isomorphism.\n";

quit;
