/*******************************************************************************
 * fermat_quartic_aut_action.m
 *
 * Purpose:
 *   Compute the automorphism group of the Fermat quartic C: x^4+y^4+z^4=0
 *   as explicit PGL(3) matrices, and determine the action of Aut(C) on
 *   J[2] = H^1(C_Qbar, F_2) = (Z/2Z)^6.
 *
 * Method:
 *   - Work over F_p with p ≡ 1 mod 8 so that J[2](F_p) = (Z/2Z)^6 (full).
 *   - Aut(C) = (Z/4Z)^2 ⋊ S_3 of order 96: monomial maps in PGL(3).
 *   - Compute J/2J via function field class group; the natural action on
 *     J/2J agrees with the action on J[2] (both reduce to A mod 2 for the
 *     integral representation matrix A).
 *   - For each of the 63 nonzero classes, compute the stabilizer subgroup
 *     of Aut(C) and list the PGL(3) matrices.
 *
 * Mathematical background:
 *   The Fermat quartic is a canonical curve of genus 3, so all automorphisms
 *   are induced by linear maps of P^2. Its Jacobian satisfies J(C) ~ E_i^3
 *   over Q-bar, where E_i: y^2 = x^3-x has CM by Z[i]. The full 2-torsion
 *   J[2] = (Z/2Z)^6 is defined over Q(zeta_8). For p ≡ 1 mod 8, all of
 *   Q(zeta_8) embeds in F_p, so J[2](F_p) = (Z/2Z)^6.
 ******************************************************************************/

// ==========================================================================
// STEP 0: Setup
// ==========================================================================
p := 89; // p ≡ 1 mod 8
Fp := GF(p);
i_val := Sqrt(Fp!(-1));
roots4 := [Fp!1, i_val, Fp!(-1), -i_val];

printf "Working over F_%o\n", p;
printf "i = %o, roots of unity: %o\n\n", i_val, roots4;

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

// Identify the even-invariant indices (these contribute to J[2])
even_idx := [i : i in [1..#invs] | invs[i] ne 0 and invs[i] mod 2 eq 0];
printf "Indices with even invariant: %o (should have 6)\n", even_idx;
assert #even_idx eq 6;

// J[2] as a subgroup of Cl
J2_gens := [(invs[i] div 2)*Cl.i : i in even_idx];
J2 := sub<Cl | J2_gens>;
printf "|J[2]| = %o (should be 64)\n\n", #J2;

// Reduction map: Cl -> J/2J = F_2^6
// For cls = sum a_i Cl.i, reduce to (a_{even_idx[1]} mod 2, ..., a_{even_idx[6]} mod 2)
F2 := GF(2);
V6 := VectorSpace(F2, 6);

function ReduceMod2(cls)
    es := Eltseq(cls);
    return V6![F2!es[even_idx[j]] : j in [1..6]];
end function;

// ==========================================================================
// STEP 2: Degree-1 places and basis for J/2J
// ==========================================================================
deg1 := Places(FF, 1);
printf "Number of degree-1 places: %o\n", #deg1;

// Store coordinates for each place; filter to those with t,u both nonzero
// (so that no automorphism sends them to infinity in the z=1 chart)
place_data := []; // list of <place, t-val, u-val>
for P in deg1 do
    a := Evaluate(elt_t, P);
    b := Evaluate(elt_u, P);
    if a ne 0 and b ne 0 then
        Append(~place_data, <P, a, b>);
    end if;
end for;
printf "Degree-1 places with nonzero coords: %o\n", #place_data;

// Build lookup: (a,b) -> place
place_lookup := AssociativeArray();
for dat in place_data do
    place_lookup[<dat[2], dat[3]>] := dat[1];
end for;

// Also store ALL degree-1 places in lookup (including zero-coord ones)
for P in deg1 do
    a := Evaluate(elt_t, P);
    b := Evaluate(elt_u, P);
    place_lookup[<a, b>] := P;
end for;

// Find 6 linearly independent vectors in J/2J from place differences.
// Each basis element is a pair <P_place, Q_place, P_coords, Q_coords>
// representing the class [P - Q] mod 2J.
ref := place_data[1]; // reference place

basis_pairs := []; // <P_data, Q_data> where each is <place, a, b>
basis_vecs := [];
span := sub<V6 | >;

// First try: all [P_i - ref] for i > 1
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

// Fallback: try all pairs if needed
if #basis_vecs lt 6 then
    printf "Warning: only found %o independent vectors from single ref, trying all pairs\n", #basis_vecs;
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
printf "Found basis of 6 independent J/2J vectors\n";
printf "Basis vectors: %o\n\n", basis_vecs;

// Build the change-of-basis matrix B: rows are basis_vecs
B_mat := Matrix(F2, [Eltseq(v) : v in basis_vecs]);
assert Determinant(B_mat) ne 0;
B_inv := B_mat^(-1);

// ==========================================================================
// STEP 3: Enumerate all 96 automorphisms as PGL(3) matrices
// ==========================================================================
// Aut(C) for x^4+y^4+z^4=0 in PGL(3):
//   M = P_sigma * diag(1, beta, gamma)
// where sigma in S_3 (permutation of coords), beta^4 = gamma^4 = 1.
// |Aut| = 6 * 4 * 4 = 96.

print "=== AUTOMORPHISM GROUP ===";
print "Aut(C) = (Z/4Z)^2 ⋊ S_3, order 96";
print "Elements: P_sigma * diag(1, beta, gamma), sigma in S_3, beta^4 = gamma^4 = 1\n";

// Permutation matrices for S_3
S3_perms := [
    <"id",    Matrix(Fp, 3, 3, [1,0,0, 0,1,0, 0,0,1])>,
    <"(12)",  Matrix(Fp, 3, 3, [0,1,0, 1,0,0, 0,0,1])>,
    <"(13)",  Matrix(Fp, 3, 3, [0,0,1, 0,1,0, 1,0,0])>,
    <"(23)",  Matrix(Fp, 3, 3, [1,0,0, 0,0,1, 0,1,0])>,
    <"(123)", Matrix(Fp, 3, 3, [0,0,1, 1,0,0, 0,1,0])>,
    <"(132)", Matrix(Fp, 3, 3, [0,1,0, 0,0,1, 1,0,0])>
];

aut_list := []; // list of <matrix, label>
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

// Verify each M preserves the curve: f(Mv) should be proportional to f(v)
// f = x^4+y^4+z^4; f(Mv) = (Mv)_1^4 + (Mv)_2^4 + (Mv)_3^4
// For M = P*D with D=diag(1,b,c): f(Mv) = 1^4*x_{s1}^4 + b^4*x_{s2}^4 + c^4*x_{s3}^4
// = x_{s1}^4 + x_{s2}^4 + x_{s3}^4 (since b^4=c^4=1) = x^4+y^4+z^4.
// So f(Mv) = f(v). Good.

// ==========================================================================
// STEP 4: Compute the 6x6 action matrix for each automorphism
// ==========================================================================

// For each automorphism M and each basis pair (P_j, Q_j),
// compute M(P_j), M(Q_j), form [M(P_j)-M(Q_j)] mod 2J.
// Then: basis_vecs[j] * M_bar = img_vecs[j], so M_bar = B^{-1} * C.

// Helper: apply a PGL(3) matrix to an affine point, return new affine coords
function ApplyAut(M, a, b)
    v := M * Matrix(Fp, 3, 1, [a, b, 1]);
    return v[1,1] / v[3,1], v[2,1] / v[3,1];
end function;

aut_F2_matrices := [];

for k in [1..96] do
    M := aut_list[k][1];

    img_vecs := [];
    for j in [1..6] do
        // Basis pair j: class [P_j - Q_j] mod 2J
        Pdat := basis_pairs[j][1]; // <place, a, b>
        Qdat := basis_pairs[j][2];

        // Apply M to both points
        aP2, bP2 := ApplyAut(M, Pdat[2], Pdat[3]);
        aQ2, bQ2 := ApplyAut(M, Qdat[2], Qdat[3]);

        M_P := place_lookup[<aP2, bP2>];
        M_Q := place_lookup[<aQ2, bQ2>];

        // Divisor: M(P_j) - M(Q_j)
        D_img := 1*M_P - 1*M_Q;
        cls_img := D_img @@ m;
        vec_img := ReduceMod2(cls_img);
        Append(~img_vecs, vec_img);
    end for;

    // basis_vecs[j] * M_bar = img_vecs[j] (right action of M_bar on row vectors)
    // B_mat * M_bar = C_mat => M_bar = B_mat^{-1} * C_mat
    C_mat := Matrix(F2, [Eltseq(v) : v in img_vecs]);
    M_bar := B_inv * C_mat;
    Append(~aut_F2_matrices, M_bar);
end for;

// Verify all matrices are invertible
for k in [1..96] do
    assert Determinant(aut_F2_matrices[k]) ne 0;
end for;
print "All 96 action matrices on J[2] are invertible.\n";

// Build the image group in GL(6, F_2)
G_image := sub<GL(6, F2) | aut_F2_matrices>;
printf "Image of Aut(C) in GL(6, F_2): order %o\n", #G_image;
printf "Isomorphism type: %o\n\n", GroupName(G_image);

// ==========================================================================
// STEP 5: Verify the representation
// ==========================================================================
// The F2 matrices should form a group. The identity automorphism (k=1)
// should give the identity matrix, and the group generated should have
// order dividing 96. If |G_image| = 96, the map is injective.
assert aut_F2_matrices[1] eq IdentityMatrix(F2, 6);
print "Identity automorphism maps to identity matrix. ✓";

// Check the kernel: which automorphisms act trivially on J[2]?
kernel := [k : k in [1..96] | aut_F2_matrices[k] eq IdentityMatrix(F2, 6)];
printf "Kernel of action on J[2]: %o automorphisms\n", #kernel;
if #kernel gt 1 then
    print "Kernel elements:";
    for k in kernel do
        printf "  %o\n", aut_list[k][2];
    end for;
end if;
printf "\n";

// ==========================================================================
// STEP 6: Print all 96 PGL(3) matrices and their F_2 action matrices
// ==========================================================================
print "=== ALL 96 AUTOMORPHISMS AND THEIR J[2] ACTIONS ===\n";
for k in [1..96] do
    printf "Aut #%o: %o\n", k, aut_list[k][2];
    printf "  PGL(3) matrix: %o\n", Eltseq(aut_list[k][1]);
    printf "  J[2] matrix:   %o\n\n", Eltseq(aut_F2_matrices[k]);
end for;

// ==========================================================================
// STEP 7: For each of the 63 nonzero classes, compute the stabilizer
// ==========================================================================
print "=== STABILIZERS OF THE 63 NONZERO CLASSES IN J[2] ===\n";

// Group the 63 classes by orbit under Aut(C)
// First compute all orbits
visited := {};
orbit_data := []; // list of <orbit, stab_size, stab_structure>

for vec in V6 do
    if vec eq V6!0 then continue; end if;
    if vec in visited then continue; end if;

    // Compute orbit and stabilizer of vec
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

    // Build the stabilizer as a matrix group
    stab_mats_F2 := [aut_F2_matrices[k] : k in stab_indices];
    stab_mats_PGL := [aut_list[k][1] : k in stab_indices];

    if #stab_indices gt 0 then
        Stab := sub<GL(6, F2) | stab_mats_F2>;
        stab_name := GroupName(Stab);
    else
        stab_name := "trivial";
    end if;

    Append(~orbit_data, <orbit, stab_indices, stab_name>);

    printf "Orbit of size %o, |Stab| = %o, Stab ≅ %o\n", #orbit, #stab_indices, stab_name;
    printf "  Representative: %o\n", vec;
    printf "  Stabilizer PGL(3) matrices:\n";
    for k in stab_indices do
        printf "    %o  [%o]\n", Eltseq(aut_list[k][1]), aut_list[k][2];
    end for;
    printf "\n";
end for;

printf "\n=== SUMMARY ===\n";
printf "Number of orbits on nonzero J[2] classes: %o\n", #orbit_data;
printf "Orbit sizes: %o\n", [#orb[1] : orb in orbit_data];
printf "Stabilizer orders: %o\n", [#orb[2] : orb in orbit_data];
printf "Stabilizer types: %o\n", [orb[3] : orb in orbit_data];

// Verify orbit-stabilizer theorem: |orbit| * |stab| = |Aut| = 96
for orb in orbit_data do
    assert #orb[1] * #orb[2] eq 96;
end for;
print "Orbit-stabilizer theorem verified for all orbits.";

// ==========================================================================
// STEP 8: Also list the stabilizer for each individual class
// ==========================================================================
print "\n=== INDIVIDUAL CLASS STABILIZERS ===\n";
printf "%-25o  %-6o  %-15o\n", "Class (F_2^6)", "|Stab|", "Stab type";
printf "%-25o  %-6o  %-15o\n", "-------------", "------", "---------";

for vec in V6 do
    if vec eq V6!0 then continue; end if;
    stab_idx := [k : k in [1..96] | vec * aut_F2_matrices[k] eq vec];
    if #stab_idx gt 0 then
        S := sub<GL(6, F2) | [aut_F2_matrices[k] : k in stab_idx]>;
        sname := GroupName(S);
    else
        sname := "1";
    end if;
    printf "%-25o  %-6o  %-15o\n", vec, #stab_idx, sname;
end for;

quit;
