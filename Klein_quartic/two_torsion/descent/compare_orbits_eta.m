/*******************************************************************************
 * compare_orbits_eta.m
 *
 * Unified computation: orbit structure of Aut(C) on J[2] AND identification
 * of eta from the quadric decomposition, at a single prime.
 *
 * Use p ≡ 1 mod 24 so that F_p has: 4th roots of unity, 8th roots (J[2] full),
 * and sqrt(-3) (for defining eta).
 ******************************************************************************/

p := 97; // 97 ≡ 1 mod 24
Fp := GF(p);
i_val := Sqrt(Fp!(-1));
w := Sqrt(Fp!(-3));
roots4 := [Fp!1, i_val, Fp!(-1), -i_val];

printf "Working over F_%o\n", p;
printf "i = %o, w = sqrt(-3) = %o\n\n", p, i_val, w;

// Function field of C: u^4 + t^4 + 1 = 0
Fpt<t> := FunctionField(Fp);
Ku<u> := PolynomialRing(Fpt);
FF<uu> := FunctionField(u^4 + t^4 + 1);
elt_t := FF!t;
elt_u := uu;

// ==========================================================================
// STEP 1: Class group and J[2]
// ==========================================================================
Cl, m := ClassGroup(FF);
invs := Invariants(Cl);
printf "Class group invariants: %o\n", invs;

even_idx := [i : i in [1..#invs] | invs[i] ne 0 and invs[i] mod 2 eq 0];
printf "Indices with even invariant: %o\n", even_idx;
assert #even_idx eq 6;

J2_gens := [(invs[i] div 2)*Cl.i : i in even_idx];
J2 := sub<Cl | J2_gens>;
printf "|J[2]| = %o\n\n", #J2;

F2 := GF(2);
V6 := VectorSpace(F2, 6);

function ReduceMod2(cls)
    es := Eltseq(cls);
    return V6![F2!es[even_idx[j]] : j in [1..6]];
end function;

// ==========================================================================
// STEP 2: Degree-1 places and basis
// ==========================================================================
deg1 := Places(FF, 1);
printf "Number of degree-1 places: %o\n", #deg1;

place_data := [* *];

function AffKey(a, b)
    return Sprintf("aff:%o,%o", Integers()!a, Integers()!b);
end function;

function InfKey(r)
    return Sprintf("inf:%o", Integers()!r);
end function;
place_lookup := AssociativeArray();

for P in deg1 do
    a_raw := Evaluate(elt_t, P);
    b_raw := Evaluate(elt_u, P);
    ok_a, ai := IsCoercible(Integers(), a_raw);
    ok_b, bi := IsCoercible(Integers(), b_raw);
    if ok_a and ok_b then
        a := Fp!ai; b := Fp!bi;
        place_lookup[AffKey(a, b)] := P;
        Append(~place_data, <P, a, b>);
    else
        r_raw := Evaluate(elt_u/elt_t, P);
        ok_r, ri := IsCoercible(Integers(), r_raw);
        if ok_r then
            r := Fp!ri;
            place_lookup[InfKey(r)] := P;
        end if;
    end if;
end for;
printf "Degree-1 places with finite coords: %o\n", #place_data;

ref := place_data[1];
basis_pairs := [* *];
basis_vecs := [];
span := sub<V6 | >;

for i in [2..#place_data] do
    D := 1*place_data[i][1] - 1*ref[1];
    cls := D @@ m;
    vec := ReduceMod2(cls);
    if vec ne V6!0 and vec notin span then
        Append(~basis_pairs, <place_data[i], ref>);
        Append(~basis_vecs, vec);
        span := sub<V6 | span, vec>;
        if Dimension(span) eq 6 then break; end if;
    end if;
end for;

if #basis_vecs lt 6 then
    for i in [1..#place_data] do
        for j in [i+1..#place_data] do
            D := 1*place_data[i][1] - 1*place_data[j][1];
            cls := D @@ m;
            vec := ReduceMod2(cls);
            if vec ne V6!0 and vec notin span then
                Append(~basis_pairs, <place_data[i], place_data[j]>);
                Append(~basis_vecs, vec);
                span := sub<V6 | span, vec>;
                if Dimension(span) eq 6 then break i; end if;
            end if;
        end for;
    end for;
end if;

assert #basis_vecs eq 6;
printf "Found basis of 6 independent J/2J vectors\n\n";

B_mat := Matrix(F2, [Eltseq(v) : v in basis_vecs]);
assert Determinant(B_mat) ne 0;
B_inv := B_mat^(-1);

// ==========================================================================
// STEP 3: Automorphisms and their F_2 action
// ==========================================================================
S3_perms := [
    <"id",    Matrix(Fp, 3, 3, [1,0,0, 0,1,0, 0,0,1])>,
    <"(12)",  Matrix(Fp, 3, 3, [0,1,0, 1,0,0, 0,0,1])>,
    <"(13)",  Matrix(Fp, 3, 3, [0,0,1, 0,1,0, 1,0,0])>,
    <"(23)",  Matrix(Fp, 3, 3, [1,0,0, 0,0,1, 0,1,0])>,
    <"(123)", Matrix(Fp, 3, 3, [0,0,1, 1,0,0, 0,1,0])>,
    <"(132)", Matrix(Fp, 3, 3, [0,1,0, 0,0,1, 1,0,0])>
];

aut_list := [];
for sp in S3_perms do
    for beta in roots4 do
        for gamma in roots4 do
            M := sp[2] * DiagonalMatrix(Fp, [1, beta, gamma]);
            label := Sprintf("%o * diag(1,%o,%o)", sp[1], beta, gamma);
            Append(~aut_list, <M, label>);
        end for;
    end for;
end for;
assert #aut_list eq 96;

function ApplyAutKey(M, a, b)
    v := M * Matrix(Fp, 3, 1, [a, b, 1]);
    if v[3,1] ne 0 then
        return AffKey(v[1,1] / v[3,1], v[2,1] / v[3,1]);
    end if;
    if v[1,1] ne 0 then
        return InfKey(v[2,1] / v[1,1]);
    end if;
    return InfKey(v[1,1] / v[2,1]);
end function;

aut_F2_matrices := [];
for k in [1..96] do
    M := aut_list[k][1];
    img_vecs := [];
    for j in [1..6] do
        Pdat := basis_pairs[j][1];
        Qdat := basis_pairs[j][2];
        keyP := ApplyAutKey(M, Pdat[2], Pdat[3]);
        keyQ := ApplyAutKey(M, Qdat[2], Qdat[3]);
        M_P := place_lookup[keyP];
        M_Q := place_lookup[keyQ];
        D_img := 1*M_P - 1*M_Q;
        cls_img := D_img @@ m;
        vec_img := ReduceMod2(cls_img);
        Append(~img_vecs, vec_img);
    end for;
    C_mat := Matrix(F2, [Eltseq(v) : v in img_vecs]);
    M_bar := B_inv * C_mat;
    Append(~aut_F2_matrices, M_bar);
end for;

G_image := sub<GL(6, F2) | aut_F2_matrices>;
printf "Image of Aut(C) in GL(6, F_2): order %o\n", #G_image;
printf "Kernel: %o automorphisms\n\n", #[k : k in [1..96] | aut_F2_matrices[k] eq IdentityMatrix(F2, 6)];

// ==========================================================================
// STEP 4: Compute orbits on J[2]\{0}
// ==========================================================================
printf "=== ORBIT STRUCTURE ===\n";
visited := {};
orbit_data := [];

for vec in V6 do
    if vec eq V6!0 then continue; end if;
    if vec in visited then continue; end if;
    orbit := {vec};
    stab_indices := [];
    for k in [1..96] do
        img := vec * aut_F2_matrices[k];
        Include(~orbit, img);
        if img eq vec then
            Append(~stab_indices, k);
        end if;
    end for;
    visited join:= orbit;
    stab_mats_F2 := [aut_F2_matrices[k] : k in stab_indices];
    if #stab_indices gt 0 then
        Stab := sub<GL(6, F2) | stab_mats_F2>;
        stab_name := GroupName(Stab);
    else
        stab_name := "1";
    end if;
    Append(~orbit_data, <orbit, stab_indices, stab_name>);
    printf "Orbit of size %o, |Stab| = %o, Stab ≅ %o, rep = %o\n",
        #orbit, #stab_indices, stab_name, vec;
end for;

printf "\nOrbit sizes: %o\n", [#orb[1] : orb in orbit_data];
printf "Stabilizer orders: %o\n\n", [#orb[2] : orb in orbit_data];

// ==========================================================================
// STEP 5: Compute eta from quadric decomposition
// ==========================================================================
printf "=== IDENTIFYING ETA ===\n";
printf "q1 = 2t^2 + (1-w)*u^2 + (1+w), w = sqrt(-3) = %o\n", w;

q1 := 2*elt_t^2 + (1-w)*elt_u^2 + (1+w);
printf "q1 as element of function field: computed\n";

// Compute div(q1) on C
dq1 := Divisor(q1);
printf "deg(div(q1)) = %o (should be 0)\n", Degree(dq1);

// Check all valuations are even (required for etale cover)
supp := Support(dq1);
all_even := true;
for P in supp do
    val := Valuation(q1, P);
    if val mod 2 ne 0 then
        all_even := false;
        printf "  ODD valuation %o at place of degree %o!\n", val, Degree(P);
    end if;
end for;
if all_even then
    printf "All valuations of q1 are even — cover is etale ✓\n";
else
    printf "WARNING: some valuations are odd — cover is NOT etale!\n";
end if;

// eta = (1/2) div(q1)
// Compute this as a divisor class: if div(q1) = sum 2*n_i*P_i,
// then half_div = sum n_i*P_i, and eta = class(half_div)
half_div := dq1 div 2;  // Magma should handle this for even divisors
eta_cls := half_div @@ m;
eta_vec := ReduceMod2(eta_cls);
printf "eta in J/2J coordinates: %o\n", eta_vec;
printf "eta nonzero? %o\n\n", eta_vec ne V6!0;

// Find which orbit eta belongs to
printf "=== WHICH ORBIT DOES ETA BELONG TO? ===\n";
for i in [1..#orbit_data] do
    if eta_vec in orbit_data[i][1] then
        printf "eta belongs to orbit #%o\n", i;
        printf "  Orbit size: %o\n", #orbit_data[i][1];
        printf "  |Stab(eta)| = %o\n", #orbit_data[i][2];
        printf "  Stab type: %o\n", orbit_data[i][3];
        printf "  Expected |Aut(D)| = 2 * |Stab(eta)| = %o\n\n",
            2 * #orbit_data[i][2];
        break;
    end if;
end for;

// Also compute stabilizer of eta directly (should match orbit data)
stab_eta := [k : k in [1..96] | eta_vec * aut_F2_matrices[k] eq eta_vec];
printf "Direct stabilizer computation: |Stab(eta)| = %o\n", #stab_eta;
printf "Stabilizer elements:\n";
for k in stab_eta do
    printf "  %o\n", aut_list[k][2];
end for;

// ==========================================================================
// STEP 6: Compute Aut(D) directly for comparison
// ==========================================================================
printf "\n=== COMPUTING Aut(D) DIRECTLY ===\n";
printf "D: v^2 = q1 on C\n";

Kv<v> := PolynomialRing(FF);
if not IsIrreducible(v^2 - q1) then
    printf "ERROR: D is reducible!\n";
    quit;
end if;
FD<vv> := FunctionField(v^2 - q1);
printf "Genus(D) = %o\n", Genus(FD);

printf "Computing Aut(D)...\n";
time A, mp_aut := AutomorphismGroup(FD);
phi_aut, G := CosetAction(A, sub<A | Id(A)>);
printf "|Aut(D)| = %o\n", #G;
printf "GroupName = %o\n", GroupName(G);
printf "IsAbelian = %o\n", IsAbelian(G);
printf "|Z(Aut(D))| = %o\n\n", #Center(G);

// Find deck involution
deck_found := false;
for g in G do
    if Order(g) ne 2 then continue; end if;
    a := g @@ phi_aut;
    aut := mp_aut(a);
    if aut(vv) eq -vv and aut(FD!uu) eq FD!uu and aut(FD!t) eq FD!t then
        printf "Deck involution found, central? %o\n", g in Center(G);
        deck_sub := sub<G | g>;
        printf "<iota> normal? %o\n", IsNormal(G, deck_sub);
        if IsNormal(G, deck_sub) then
            Q, _ := G / deck_sub;
            printf "Aut(D)/<iota>: order %o, structure %o\n", #Q, GroupName(Q);
        end if;
        deck_found := true;
        break;
    end if;
end for;
if not deck_found then
    printf "WARNING: deck involution not found!\n";
end if;

printf "\n=== CONSISTENCY CHECK ===\n";
printf "|Stab(eta)| = %o\n", #stab_eta;
printf "|Aut(D)| = %o\n", #G;
printf "Expected: |Aut(D)| = 2 * |Stab(eta)| = %o\n", 2 * #stab_eta;
printf "Consistent? %o\n", #G eq 2 * #stab_eta;

quit;
