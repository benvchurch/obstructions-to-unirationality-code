/*
 * bitangent_j2_orbits.m
 *
 * For the Klein quartic twist over F_29, compute:
 *   1. The 4 orbits of PSL(2,7) on J[2]\{0} (sizes 7,7,21,28)
 *   2. The J[2] class of each bitangent difference L_i - L_0
 *   3. Which J[2] orbit each difference lands in
 *   4. Whether the two 28-element PSL(2,7)-sets (bitangents vs J[2] orbit)
 *      are isomorphic as permutation representations
 */

SetColumns(0);
F2 := GF(2);

Fq := GF(29);
P2<x,y,z> := ProjectiveSpace(Fq, 2);
F := x^4 + y^4 + z^4 + 6*(x*y^3 + y*z^3 + z*x^3)
     - 3*(x^2*y^2 + y^2*z^2 + z^2*x^2) + 3*x*y*z*(x+y+z);
C := Curve(P2, F);

// --- Bitangent finder ---
function FindBitangents(F, Fq)
    P2 := Parent(F);
    x := P2.1; y := P2.2; z := P2.3;
    bits := [];
    Pt<t> := PolynomialRing(Fq);
    for a in Fq do
        for b in Fq do
            f_line := Evaluate(F, [t, 1, a*t + b]);
            if Degree(f_line) lt 0 or f_line eq 0 then continue; end if;
            lc := LeadingCoefficient(f_line);
            is_sq, _ := IsSquare(f_line / lc);
            if is_sq then Append(~bits, [Fq | -a, -b, 1]); end if;
        end for;
    end for;
    for c in Fq do
        f_line := Evaluate(F, [1, c, t]);
        if Degree(f_line) lt 0 or f_line eq 0 then continue; end if;
        lc := LeadingCoefficient(f_line);
        is_sq, _ := IsSquare(f_line / lc);
        if is_sq then Append(~bits, [Fq | c, -1, 0]); end if;
    end for;
    f_line := Evaluate(F, [0, 1, t]);
    if Degree(f_line) ge 0 and f_line ne 0 then
        lc := LeadingCoefficient(f_line);
        is_sq, _ := IsSquare(f_line / lc);
        if is_sq then Append(~bits, [Fq | 1, 0, 0]); end if;
    end if;
    bits_norm := [];
    for L in bits do
        for k in [1..3] do
            if L[k] ne 0 then
                Append(~bits_norm, [L[i]/L[k] : i in [1..3]]);
                break;
            end if;
        end for;
    end for;
    bits_uniq := [];
    for L in bits_norm do
        if not (L in bits_uniq) then Append(~bits_uniq, L); end if;
    end for;
    return bits_uniq;
end function;

// --- PGL(3) recovery helpers ---
function NormalizeLine(L)
    for k in [1..3] do
        if L[k] ne 0 then return [L[i]/L[k] : i in [1..3]]; end if;
    end for;
    return L;
end function;

function LinePermutation(M, bits)
    Minv := M^(-1);
    perm := [];
    for i in [1..#bits] do
        L := bits[i];
        img := [&+[L[c] * Minv[c, r] : c in [1..3]] : r in [1..3]];
        img_n := NormalizeLine(img);
        found := 0;
        for j in [1..#bits] do
            if NormalizeLine(bits[j]) eq img_n then found := j; break; end if;
        end for;
        if found eq 0 then error "image not found"; end if;
        Append(~perm, found);
    end for;
    return perm;
end function;

function NoThreeColinear(pts, Fq)
    n := #pts;
    for i in [1..n-2] do
        for j in [i+1..n-1] do
            for k in [j+1..n] do
                Mc := Matrix(Fq, 3, 3, pts[i] cat pts[j] cat pts[k]);
                if Determinant(Mc) eq 0 then return false; end if;
            end for;
        end for;
    end for;
    return true;
end function;

function PGL3FromImages(Pin, Pout, Fq)
    M1 := Matrix(Fq, 3, 3,
        [Pin[1][1], Pin[2][1], Pin[3][1],
         Pin[1][2], Pin[2][2], Pin[3][2],
         Pin[1][3], Pin[2][3], Pin[3][3]]);
    sol := Solution(Transpose(M1), Vector(Fq, Pin[4]));
    A := M1 * DiagonalMatrix(Fq, [sol[1], sol[2], sol[3]]);
    M2 := Matrix(Fq, 3, 3,
        [Pout[1][1], Pout[2][1], Pout[3][1],
         Pout[1][2], Pout[2][2], Pout[3][2],
         Pout[1][3], Pout[2][3], Pout[3][3]]);
    sol2 := Solution(Transpose(M2), Vector(Fq, Pout[4]));
    B := M2 * DiagonalMatrix(Fq, [sol2[1], sol2[2], sol2[3]]);
    return B * A^(-1);
end function;

function AutToMatrix(g, Cpts, Fq)
    eqs := DefiningEquations(g);
    Pin := []; Pout := [];
    for v in Cpts do
        if #Pin eq 4 then break; end if;
        img := [Evaluate(e, v) : e in eqs];
        if img[1] eq 0 and img[2] eq 0 and img[3] eq 0 then continue; end if;
        new_pts := Pin cat [v];
        if NoThreeColinear(new_pts, Fq) then
            Append(~Pin, v);
            Append(~Pout, [Fq | c : c in img]);
        end if;
    end for;
    if #Pin lt 4 then error "too few points"; end if;
    return PGL3FromImages(Pin, Pout, Fq);
end function;

// =====================================================================
// STEP 1: Find bitangents and build permutation action
// =====================================================================
printf "=== STEP 1: Bitangents and automorphism action ===\n";
bits := FindBitangents(F, Fq);
printf "Found %o bitangents.\n", #bits;
assert #bits eq 28;

auts := Automorphisms(C);
printf "|Aut(C)| = %o\n", #auts;

Cpts := [];
for pt in Points(C) do
    v := Eltseq(pt);
    if &and[IsCoercible(Fq, c) : c in v] then
        Append(~Cpts, [Fq | c : c in v]);
    end if;
end for;

perm_elts := [];
for g in auts do
    M := AutToMatrix(g, Cpts, Fq);
    p := LinePermutation(M, bits);
    Append(~perm_elts, Sym(28) ! p);
end for;
G_bit := sub<Sym(28) | perm_elts>;
printf "Bitangent permutation group: order %o, %o\n", #G_bit, GroupName(G_bit);

// =====================================================================
// STEP 2: Build function field, class group, J[2]
// =====================================================================
printf "\n=== STEP 2: J[2] computation ===\n";
Rxyz<X,Y,Z> := PolynomialRing(Fq, 3);
F_XYZ := Evaluate(F, [X, Y, Z]);
Fpt<t_var> := FunctionField(Fq);
Ku<u_var> := PolynomialRing(Fpt);
f_u := Ku ! 0;
for j in [0..4] do
    coeff_j := Fpt ! 0;
    for i in [0..4-j] do
        k := 4 - i - j;
        c := MonomialCoefficient(F_XYZ, X^i * Y^j * Z^k);
        if c ne 0 then coeff_j +:= (Fpt ! c) * t_var^i; end if;
    end for;
    f_u +:= coeff_j * u_var^j;
end for;
FF<uu> := FunctionField(f_u);
elt_t := FF ! t_var;
Cl, mp := ClassGroup(FF);
invs := Invariants(Cl);
printf "Cl invariants = %o\n", invs;

even_idx := [i : i in [1..#invs] | invs[i] ne 0 and invs[i] mod 2 eq 0];
dim := #even_idx;
printf "J[2] dimension = %o\n", dim;
assert dim eq 6;

function ClassJ2(D)
    cl := D @@ mp;
    coords := Eltseq(cl);
    j2 := [];
    for k in [1..#invs] do
        if invs[k] eq 0 then continue; end if;
        if invs[k] mod 2 ne 0 then continue; end if;
        Append(~j2, (2 * coords[k] div invs[k]) mod 2);
    end for;
    return j2;
end function;

// =====================================================================
// STEP 3: Compute J[2] vectors for all 28 bitangents
// =====================================================================
printf "\n=== STEP 3: J[2] vectors of bitangent differences ===\n";
line_fns := [];
for i in [1..28] do
    A := Fq ! bits[i][1];
    B := Fq ! bits[i][2];
    CC := Fq ! bits[i][3];
    Append(~line_fns, A * elt_t + B * uu + (FF ! CC));
end for;

ref := 1;
half_divs := [* *];
for i in [1..28] do
    if i eq ref then
        Append(~half_divs, Zero(DivisorGroup(FF)));
        continue;
    end if;
    ratio := line_fns[i] / line_fns[ref];
    D_ratio := Divisor(ratio);
    D_half := D_ratio div 2;
    Append(~half_divs, D_half);
end for;

J2_vec := [];
for i in [1..28] do
    if i eq ref then
        Append(~J2_vec, [F2 ! 0 : k in [1..dim]]);
    else
        v := ClassJ2(half_divs[i]);
        Append(~J2_vec, [F2 ! Integers() ! s : s in v]);
    end if;
end for;

// Pick a J[2] basis
basis_idx := [];
Bmat_rows := [];
for i in [1..28] do
    if i eq ref then continue; end if;
    if #basis_idx ge dim then break; end if;
    v := J2_vec[i];
    test_seq := &cat (Bmat_rows cat [v]);
    test := Matrix(F2, #Bmat_rows + 1, dim, test_seq);
    if Rank(test) eq #Bmat_rows + 1 then
        Append(~basis_idx, i);
        Append(~Bmat_rows, v);
    end if;
end for;
assert #basis_idx eq dim;
Bmat := Matrix(F2, dim, dim, &cat Bmat_rows);
printf "J[2] basis from bitangent indices: %o (ref = #%o)\n", basis_idx, ref;

// Express all 28 bitangent J[2] vectors in this basis
J2_coords := [];
for i in [1..28] do
    sol := Solution(Bmat, Vector(F2, J2_vec[i]));
    Append(~J2_coords, [sol[j] : j in [1..dim]]);
end for;

// =====================================================================
// STEP 4: Build F_2 matrices for each automorphism on J[2]
// =====================================================================
printf "\n=== STEP 4: PSL(2,7) action on J[2] ===\n";
gen_matrices_f2 := [];
for gi in [1..#perm_elts] do
    perm := [k ^ perm_elts[gi] : k in [1..28]];
    rows := [];
    for k in [1..dim] do
        i := basis_idx[k];
        v_pi := J2_vec[perm[i]];
        v_pref := J2_vec[perm[ref]];
        target := [v_pi[s] + v_pref[s] : s in [1..dim]];
        sol := Solution(Bmat, Vector(F2, target));
        Append(~rows, [sol[j] : j in [1..dim]]);
    end for;
    Mg := Matrix(F2, dim, dim, &cat rows);
    Append(~gen_matrices_f2, Mg);
end for;

G_j2 := sub<GL(dim, F2) | gen_matrices_f2>;
printf "F_2 matrix group: order %o, name %o\n", #G_j2, GroupName(G_j2);

// =====================================================================
// STEP 5: Orbits of PSL(2,7) on J[2]\{0}
// =====================================================================
printf "\n=== STEP 5: Orbits on J[2]\\{0} ===\n";

// Enumerate all 63 nonzero vectors
V := VectorSpace(F2, dim);
nonzero := [v : v in V | v ne Zero(V)];
printf "%o nonzero vectors in J[2].\n", #nonzero;

// For each nonzero vector, compute its orbit under G_j2
orbit_labels := [0 : i in [1..63]];
orbit_count := 0;
orbit_reps := [];
orbit_sizes := [];

for idx in [1..63] do
    if orbit_labels[idx] ne 0 then continue; end if;
    orbit_count +:= 1;
    orb := {nonzero[idx]};
    for M in G_j2 do
        Include(~orb, nonzero[idx] * M);
    end for;
    orb_list := SetToSequence(orb);
    Append(~orbit_reps, nonzero[idx]);
    Append(~orbit_sizes, #orb_list);
    for v in orb_list do
        for j in [1..63] do
            if nonzero[j] eq v then
                orbit_labels[j] := orbit_count;
                break;
            end if;
        end for;
    end for;
end for;

printf "%o orbits on J[2]\\{0}:\n", orbit_count;
for i in [1..orbit_count] do
    printf "  Orbit %o: size %o, representative = %o\n", i, orbit_sizes[i], orbit_reps[i];
end for;

// =====================================================================
// STEP 6: Where do bitangent differences land?
// =====================================================================
printf "\n=== STEP 6: Bitangent differences → J[2] orbits ===\n";

// For the base bitangent L_ref, the differences L_i - L_ref give
// 27 nonzero elements of J[2]. Which orbits do they hit?
printf "Base bitangent: #%o, coeffs %o\n", ref, bits[ref];
printf "\nBitangent differences L_i - L_%o:\n", ref;
orbit_hit_count := [0 : i in [1..orbit_count]];

for i in [1..28] do
    if i eq ref then continue; end if;
    v := Vector(F2, J2_coords[i]);
    // Find which orbit this vector belongs to
    orb_id := 0;
    for j in [1..63] do
        if nonzero[j] eq v then
            orb_id := orbit_labels[j];
            break;
        end if;
    end for;
    if orb_id eq 0 then
        printf "  L_%o - L_%o = %o  -> NOT FOUND (error!)\n", i, ref, v;
    else
        orbit_hit_count[orb_id] +:= 1;
    end if;
end for;

printf "\nDistribution of 27 bitangent differences among J[2] orbits:\n";
for i in [1..orbit_count] do
    printf "  Orbit %o (size %o): %o differences land here\n",
        i, orbit_sizes[i], orbit_hit_count[i];
end for;

// =====================================================================
// STEP 7: Also try ALL pairwise bitangent differences (not just from L_ref)
// =====================================================================
printf "\n=== STEP 7: All pairwise bitangent differences ===\n";
pair_orbit_count := [0 : i in [1..orbit_count]];
for i in [1..28] do
    for j in [i+1..28] do
        // L_i - L_j = (L_i - L_ref) - (L_j - L_ref) = J2_coords[i] + J2_coords[j]
        dd := Vector(F2, J2_coords[i]) + Vector(F2, J2_coords[j]);
        if dd eq Zero(V) then continue; end if;
        orb_id := 0;
        for k in [1..63] do
            if nonzero[k] eq dd then
                orb_id := orbit_labels[k];
                break;
            end if;
        end for;
        if orb_id ne 0 then
            pair_orbit_count[orb_id] +:= 1;
        end if;
    end for;
end for;

printf "Distribution of C(28,2) = %o pairwise bitangent differences:\n", 28*27 div 2;
for i in [1..orbit_count] do
    printf "  Orbit %o (size %o): %o pairwise differences\n",
        i, orbit_sizes[i], pair_orbit_count[i];
end for;

// =====================================================================
// STEP 8: Check if bitangent and J[2] 28-orbit are isomorphic as
//         permutation representations
// =====================================================================
printf "\n=== STEP 8: Permutation representation comparison ===\n";

// Build permutation action of G on the size-28 orbit
orb28_id := 0;
for i in [1..orbit_count] do
    if orbit_sizes[i] eq 28 then orb28_id := i; break; end if;
end for;

if orb28_id eq 0 then
    printf "No orbit of size 28 found!\n";
else
    orb28_vecs := [nonzero[j] : j in [1..63] | orbit_labels[j] eq orb28_id];
    printf "Size-28 orbit (orbit #%o): %o vectors.\n", orb28_id, #orb28_vecs;

    // Build permutations of G_j2 on these 28 vectors
    j2_perm_elts := [];
    for M in Generators(G_j2) do
        perm := [];
        for k in [1..28] do
            img := orb28_vecs[k] * M;
            found := 0;
            for l in [1..28] do
                if orb28_vecs[l] eq img then found := l; break; end if;
            end for;
            if found eq 0 then error "orbit not closed"; end if;
            Append(~perm, found);
        end for;
        Append(~j2_perm_elts, Sym(28) ! perm);
    end for;
    G_j2_perm := sub<Sym(28) | j2_perm_elts>;
    printf "J[2] 28-orbit permutation group: order %o\n", #G_j2_perm;

    is_iso, phi := IsIsomorphic(G_bit, G_j2_perm);
    printf "Are G_bit and G_j2_perm isomorphic as abstract groups? %o\n", is_iso;

    // Check if conjugate in Sym(28) (= isomorphic as permutation representations)
    is_conj := IsConjugate(Sym(28), G_bit, G_j2_perm);
    printf "Are they conjugate in Sym(28) (= isomorphic perm reps)? %o\n", is_conj;

    // Compare cycle types
    printf "\nCycle index comparison:\n";
    bit_cycles := {* CycleStructure(g) : g in G_bit *};
    j2_cycles := {* CycleStructure(g) : g in G_j2_perm *};
    printf "Same multiset of cycle structures? %o\n", bit_cycles eq j2_cycles;

    // Stabilizer structure in both representations
    stab_bit := Stabiliser(G_bit, 1);
    stab_j2 := Stabiliser(G_j2_perm, 1);
    printf "\nBitangent stabiliser: order %o, name %o\n", #stab_bit, GroupName(stab_bit);
    printf "J[2] 28-orbit stabiliser: order %o, name %o\n", #stab_j2, GroupName(stab_j2);
end if;

quit;
