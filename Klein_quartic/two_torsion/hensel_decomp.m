/*******************************************************************************
 * hensel_decomp.m
 *
 * Given a smooth plane quartic F over Q, find quadric decompositions
 *   F = Q1*Q3 - Q2^2
 * by:
 *   1. Exhaustive search over F_p (finding Q2 s.t. F+Q2^2 factors as Q1*Q3)
 *   2. Classify each decomposition by Aut(C)-orbit on J[2]\{0}
 *   3. Hensel-lift from F_p to mod p^k
 *   4. (Optional) LLL recognition of lifted coefficients
 *
 * INPUT: Set F_input below and choose a prime p.
 *
 * The classification uses the function field of C over F_p to compute J/2J
 * and the action of Aut(C) on J[2].
 ******************************************************************************/

// =====================================================================
// INPUT
// =====================================================================

QQ := Rationals();
RQ<x,y,z> := PolynomialRing(QQ, 3);

// Klein quartic
F_input := x^3*y + y^3*z + z^3*x;

// Prime for reduction (must give smooth C/F_p; 7 | p-1 helps for Klein)
p := 29;

// Hensel lift precision
target_precision := 5;

// =====================================================================
// STEP 1: Setup over F_p
// =====================================================================

Fp := GF(p);
Rp<X,Y,Z> := PolynomialRing(Fp, 3);
FKp := Evaluate(F_input, [X, Y, Z]);

// Verify smoothness
P2p<xp,yp,zp> := ProjectiveSpace(Fp, 2);
fp_proj := Evaluate(F_input, [xp, yp, zp]);
Cp := Curve(P2p, fp_proj);
assert IsNonsingular(Cp);
printf "Curve is smooth over F_%o.\n", p;

// =====================================================================
// STEP 2: Function field and J/2J setup
// =====================================================================

print "\n=== Setting up function field and J/2J ===";

// Build function field of C in affine chart z=1: F(t, u, 1) = 0
Fpt<t> := FunctionField(Fp);
Ku<u> := PolynomialRing(Fpt);
// The quartic F(t, u, 1) as a polynomial in u with coefficients in F_p(t)
f_affine := Evaluate(FKp, [Rp!1, Rp!1, Rp!1]);  // dummy
// Actually build it properly
Rtemp<T,U,W> := PolynomialRing(Fp, 3);
Ftemp := Evaluate(F_input, [T, U, W]);
// Specialize W=1, get polynomial in T, U
f_TU := Evaluate(Ftemp, [T, U, Rtemp!1]);
// Convert to univariate in u over F_p(t)
fu_coeffs := [];
for deg in [0..4] do
    coeff_poly := Fp!0 * t;
    // Extract coefficient of U^deg from f_TU
    for mon in Monomials(f_TU) do
        c := MonomialCoefficient(f_TU, mon);
        dU := Degree(mon, U);
        dT := Degree(mon, T);
        if dU eq deg then
            coeff_poly +:= c * t^dT;
        end if;
    end for;
    Append(~fu_coeffs, Fpt!coeff_poly);
end for;
f_u := &+[fu_coeffs[i+1]*u^i : i in [0..4]];
printf "Curve polynomial in u: %o\n", f_u;

// Check it's irreducible (need degree 3 for genus 3)
assert Degree(f_u) ge 3;
FF<uu> := FunctionField(f_u);
elt_t := FF!t; elt_u := uu;
Cl, m := ClassGroup(FF);
invs := Invariants(Cl);
printf "Class group invariants: %o\n", invs;

// J/2J basis
even_idx := [i : i in [1..#invs] | invs[i] ne 0 and invs[i] mod 2 eq 0];
genus := #even_idx div 2;  // should be 3 for a quartic
F2 := GF(2);
dim := #even_idx;
V := VectorSpace(F2, dim);

function ReduceMod2(cls)
    es := Eltseq(cls);
    return V![F2!es[even_idx[j]] : j in [1..dim]];
end function;

// Map class group element to J[2] coordinates: for Z/nZ factor (n even),
// a 2-torsion element a maps to (2*a div n) mod 2.
function ReduceJ2(cls)
    es := Eltseq(cls);
    return V![F2!((2 * es[even_idx[j]]) div invs[even_idx[j]]) : j in [1..dim]];
end function;

printf "J/2J dimension: %o\n", dim;

// =====================================================================
// STEP 3: Automorphism group action on J[2]
// =====================================================================

print "\n=== Computing Aut(C) action on J[2] ===";

// Build place lookup for automorphism action (affine places only)
deg1 := Places(FF, 1);
all_deg1 := [deg1[i] : i in [1..#deg1]];
place_data := [* *];
place_lookup := AssociativeArray();

function AffKey(a, b) return Sprintf("a%o,%o", Integers()!a, Integers()!b); end function;

for P in all_deg1 do
    vt := Valuation(elt_t, P);
    vu := Valuation(elt_u, P);
    if vt lt 0 or vu lt 0 then continue; end if;
    ai := Evaluate(elt_t, P);
    bi := Evaluate(elt_u, P);
    ok_a, aii := IsCoercible(Integers(), ai);
    ok_b, bii := IsCoercible(Integers(), bi);
    if ok_a and ok_b then
        Append(~place_data, <P, Fp!aii, Fp!bii>);
        place_lookup[AffKey(Fp!aii, Fp!bii)] := P;
    end if;
end for;
printf "%o affine degree-1 places found.\n", #place_data;

// Build J/2J basis: prefer affine places (for aut action tracking), then all places
basis_pairs := [* *]; basis_vecs := []; span := sub<V | >;

// First pass: use only affine places
if #place_data ge 1 then
    ref_place := place_data[1][1];
    for i in [2..#place_data] do
        vec := ReduceMod2((1*place_data[i][1] - 1*ref_place) @@ m);
        if vec ne V!0 and vec notin span then
            Append(~basis_pairs, <place_data[i], place_data[1]>);
            Append(~basis_vecs, vec);
            span := sub<V | span, vec>;
            if Dimension(span) eq dim then break; end if;
        end if;
    end for;
end if;

// Second pass: supplement with non-affine places if needed
if #basis_vecs lt dim then
    if not assigned ref_place then ref_place := all_deg1[1]; end if;
    for i in [1..#all_deg1] do
        if Dimension(span) eq dim then break; end if;
        vec := ReduceMod2((1*all_deg1[i] - 1*ref_place) @@ m);
        if vec ne V!0 and vec notin span then
            Append(~basis_pairs, <[* all_deg1[i] *], [* ref_place *]>);
            Append(~basis_vecs, vec);
            span := sub<V | span, vec>;
        end if;
    end for;
end if;

basis_ok := #basis_vecs eq dim;
if not basis_ok then
    printf "WARNING: only found %o / %o basis vectors from degree-1 places.\n",
        #basis_vecs, dim;
    printf "Orbit classification will be incomplete.\n";
else
    printf "Full J/2J basis found.\n";
end if;

B_inv := basis_ok select Matrix(F2, [Eltseq(v) : v in basis_vecs])^(-1)
         else ZeroMatrix(F2, dim, dim);

// Compute Aut(C) action on J[2] via function field automorphisms
// Strategy: for each generator g of Aut(FF), apply g to the coordinates
// (t, u) of each basis place, look up the image place, and build the
// F_2-linear map on J/2J.

aut_mats_F2 := [];

function SafeEvalKey(f_t, f_u, P)
    // Evaluate automorphism image at a place, return key or "FAIL"
    vt := Valuation(f_t, P);
    vu := Valuation(f_u, P);
    if vt lt 0 or vu lt 0 then return "INF"; end if;
    a := Evaluate(f_t, P);
    b := Evaluate(f_u, P);
    return AffKey(a, b);
end function;

aut_ok := basis_ok;
if aut_ok then
    try
        aut_grp, aut_map := AutomorphismGroup(FF);
        printf "|Aut(FF)| = %o\n", #aut_grp;
    catch e
        print "Could not compute function field automorphisms. Using identity only.";
        aut_ok := false;
        aut_mats_F2 := [IdentityMatrix(F2, dim)];
    end try;
end if;

if not aut_ok then
    aut_mats_F2 := [IdentityMatrix(F2, dim)];
end if;

if aut_ok then
    aut_gens := SetToSequence(Generators(aut_grp));
    for gi in [1..#aut_gens] do
        g := aut_gens[gi];
        phi := aut_map(g);
        img_t := Image(phi, elt_t);
        img_u := Image(phi, uu);
        img_vecs := [];
        ok := true;
        for j in [1..dim] do
            bp := basis_pairs[j];
            // Affine basis pairs: <place_data_tuple, place_data_tuple> where tuple = <P, a, b>
            // Non-affine basis pairs: <[* P *], [* Q *]>
            P_place := Type(bp[1]) eq Tup select bp[1][1] else bp[1][1];
            Q_place := Type(bp[2]) eq Tup select bp[2][1] else bp[2][1];
            kP := SafeEvalKey(img_t, img_u, P_place);
            kQ := SafeEvalKey(img_t, img_u, Q_place);
            if kP eq "INF" or kQ eq "INF" or
               not IsDefined(place_lookup, kP) or not IsDefined(place_lookup, kQ) then
                ok := false; break;
            end if;
            Append(~img_vecs, ReduceMod2((1*place_lookup[kP] - 1*place_lookup[kQ]) @@ m));
        end for;
        if ok then
            mat := B_inv * Matrix(F2, [Eltseq(v) : v in img_vecs]);
            Append(~aut_mats_F2, mat);
        end if;
    end for;
end if;

// Generate full automorphism group in GL(dim, F_2)
G_F2 := sub<GL(dim, F2) | aut_mats_F2>;
printf "Aut(C) image in GL(%o, F_2): order %o\n", dim, #G_F2;

// Compute orbits on J[2]\{0}
visited := {}; orbit_data := [];
for vec in V do
    if vec eq V!0 or vec in visited then continue; end if;
    orb := {vec};
    for g in G_F2 do Include(~orb, vec * Matrix(F2, dim, dim, [g[i,j] : i in [1..dim], j in [1..dim]])); end for;
    visited join:= orb; Append(~orbit_data, orb);
end for;
Sort(~orbit_data, func<a,b | #a - #b>);
printf "Orbits on J[2]\\{0}: %o (sizes %o)\n", #orbit_data, [#orb : orb in orbit_data];

function OrbitOf(v)
    for i in [1..#orbit_data] do if v in orbit_data[i] then return i; end if; end for;
    return 0;
end function;

// Map a conic Q (degree-2 form) to its J/2J class via the function field
function ConicToFF(Q)
    cQ := [MonomialCoefficient(Q, X^2), MonomialCoefficient(Q, Y^2),
           MonomialCoefficient(Q, Z^2), MonomialCoefficient(Q, X*Y),
           MonomialCoefficient(Q, X*Z), MonomialCoefficient(Q, Y*Z)];
    return cQ[1]*elt_t^2 + cQ[2]*elt_u^2 + FF!(cQ[3])
         + cQ[4]*elt_t*elt_u + cQ[5]*elt_t + cQ[6]*elt_u;
end function;

function ClassOfQ(Q)
    q_ff := ConicToFF(Q);
    if q_ff eq 0 then return false, V!0, 0; end if;
    dq := Divisor(q_ff);
    ok := &and[Valuation(q_ff, P) mod 2 eq 0 : P in Support(dq)];
    if not ok then return false, V!0, 0; end if;
    vec := ReduceJ2((dq div 2) @@ m);
    return true, vec, OrbitOf(vec);
end function;

// =====================================================================
// STEP 4: Exhaustive search for F_p decompositions
// =====================================================================

print "\n=== Exhaustive search for F_p decompositions ===";
printf "Searching Q2 with coefficient of X^2 = 0 over F_%o...\n", p;

orbit_reps := AssociativeArray();  // orbit -> <Q2, Q1, Q3>
orbits_found := {};

for c2 in [0..p-1] do
for c3 in [0..p-1] do
for c4 in [0..p-1] do
for c5 in [0..p-1] do
for c6 in [0..p-1] do
    Q2 := Fp!c2*Y^2 + Fp!c3*Z^2 + Fp!c4*X*Y + Fp!c5*X*Z + Fp!c6*Y*Z;
    G := FKp + Q2^2;
    fac := Factorization(G);
    if #fac ne 2 then continue; end if;
    if TotalDegree(fac[1][1]) ne 2 or TotalDegree(fac[2][1]) ne 2 then continue; end if;
    if fac[1][2] ne 1 or fac[2][2] ne 1 then continue; end if;

    ok, vec, orb := ClassOfQ(fac[1][1]);
    if not ok then continue; end if;
    if orb eq 0 then
        // Orbit not identified (incomplete J/2J basis) — store by vector
        vec_key := -Integers()!&+[Integers()!vec[i]*2^(i-1) : i in [1..dim]];
        if vec_key notin orbits_found then
            Include(~orbits_found, vec_key);
            orbit_reps[vec_key] := <Q2, fac[1][1], fac[2][1]>;
            printf "J[2] class %o (orbit unknown): Q2 = %o\n", vec, Q2;
            printf "  Q1 = %o\n  Q3 = %o\n\n", fac[1][1], fac[2][1];
            if #orbits_found ge 63 then break c2; end if;
        end if;
    elif orb notin orbits_found then
        Include(~orbits_found, orb);
        orbit_reps[orb] := <Q2, fac[1][1], fac[2][1]>;
        printf "ORBIT %o (size %o): Q2 = %o\n", orb, #orbit_data[orb], Q2;
        printf "  Q1 = %o\n  Q3 = %o\n\n", fac[1][1], fac[2][1];
        if #orbits_found eq #orbit_data then break c2; end if;
    end if;
end for;
end for;
end for;
end for;
end for;

printf "Found reps for %o / %o orbits.\n\n", #orbits_found, #orbit_data;

// =====================================================================
// STEP 5: Hensel lifting
// =====================================================================

printf "=== HENSEL LIFTING (mod %o^%o) ===\n\n", p, target_precision;

RZ<XX,YY,ZZ> := PolynomialRing(Integers(), 3);
FKZ := Evaluate(F_input, [XX, YY, ZZ]);
monsZ := [XX^2, YY^2, ZZ^2, XX*YY, XX*ZZ, YY*ZZ];

deg4 := [XX^4, YY^4, ZZ^4, XX^3*YY, XX^3*ZZ, XX*YY^3, YY^3*ZZ,
         XX*ZZ^3, YY*ZZ^3, XX^2*YY^2, XX^2*ZZ^2, YY^2*ZZ^2,
         XX^2*YY*ZZ, XX*YY^2*ZZ, XX*YY*ZZ^2];

function LiftFp(x)
    v := Integers()!x;
    if v gt (p-1) div 2 then v -:= p; end if;
    return v;
end function;

// Hensel step: solve Q1*delta3 + delta1*Q3 - 2*Q2*delta2 = E/p^k (mod p)
function HenselStep(Q1c, Q2c, Q3c, pk)
    Q1poly := &+[Q1c[i]*monsZ[i] : i in [1..6]];
    Q2poly := &+[Q2c[i]*monsZ[i] : i in [1..6]];
    Q3poly := &+[Q3c[i]*monsZ[i] : i in [1..6]];
    errZ := FKZ - Q1poly*Q3poly + Q2poly^2;

    rhs := [];
    for d4 in deg4 do
        c := MonomialCoefficient(errZ, d4);
        assert c mod pk eq 0;
        Append(~rhs, Fp!(c div pk));
    end for;

    mat := ZeroMatrix(Fp, #deg4, 18);
    for j in [1..6] do
        prod1 := monsZ[j] * Q3poly;
        prod2 := monsZ[j] * Q1poly;
        prod3 := 2 * monsZ[j] * Q2poly;
        for i in [1..#deg4] do
            mat[i, j]    := Fp!MonomialCoefficient(prod1, deg4[i]);
            mat[i, 6+j]  := -Fp!MonomialCoefficient(prod3, deg4[i]);
            mat[i, 12+j] := Fp!MonomialCoefficient(prod2, deg4[i]);
        end for;
    end for;

    rhs_vec := Vector(Fp, rhs);
    sol := Solution(Transpose(mat), rhs_vec);
    d1 := [Integers()!sol[j] : j in [1..6]];
    d2 := [Integers()!sol[6+j] : j in [1..6]];
    d3 := [Integers()!sol[12+j] : j in [1..6]];
    return d1, d2, d3;
end function;

for orb_idx in Sort(Setseq(Keys(orbit_reps))) do
    if orb_idx ge 1 and orb_idx le #orbit_data then
        printf "--- Orbit %o (size %o) ---\n", orb_idx, #orbit_data[orb_idx];
    else
        printf "--- J[2] class (key %o, orbit unknown) ---\n", orb_idx;
    end if;
    dat := orbit_reps[orb_idx];
    Q2_fp := dat[1]; Q1_fp := dat[2]; Q3_fp := dat[3];

    mons_names := ["X^2","Y^2","Z^2","XY","XZ","YZ"];
    mons_fp := [X^2, Y^2, Z^2, X*Y, X*Z, Y*Z];

    q2c := [LiftFp(MonomialCoefficient(Q2_fp, mons_fp[i])) : i in [1..6]];
    q1c := [LiftFp(MonomialCoefficient(Q1_fp, mons_fp[i])) : i in [1..6]];
    q3c := [LiftFp(MonomialCoefficient(Q3_fp, mons_fp[i])) : i in [1..6]];

    // Verify mod p
    Q1t := &+[q1c[i]*monsZ[i] : i in [1..6]];
    Q2t := &+[q2c[i]*monsZ[i] : i in [1..6]];
    Q3t := &+[q3c[i]*monsZ[i] : i in [1..6]];
    errZ := FKZ - Q1t*Q3t + Q2t^2;
    assert &and[MonomialCoefficient(errZ, d4) mod p eq 0 : d4 in deg4];

    // Iteratively Hensel lift
    pk := p;
    lift_ok := true;
    for step in [1..target_precision-1] do
        try
            d1, d2, d3 := HenselStep(q1c, q2c, q3c, pk);
            q1c := [q1c[i] + pk*d1[i] : i in [1..6]];
            q2c := [q2c[i] + pk*d2[i] : i in [1..6]];
            q3c := [q3c[i] + pk*d3[i] : i in [1..6]];
            pk *:= p;
            // Verify
            Q1t := &+[q1c[i]*monsZ[i] : i in [1..6]];
            Q2t := &+[q2c[i]*monsZ[i] : i in [1..6]];
            Q3t := &+[q3c[i]*monsZ[i] : i in [1..6]];
            errZ := FKZ - Q1t*Q3t + Q2t^2;
            ok := &and[MonomialCoefficient(errZ, d4) mod pk eq 0 : d4 in deg4];
            if not ok then
                printf "  Step %o: VERIFICATION FAILED\n", step;
                lift_ok := false;
                break;
            end if;
        catch e
            printf "  Step %o: Hensel step failed (singular system)\n", step;
            lift_ok := false;
            break;
        end try;
    end for;

    modulus := p^target_precision;
    if lift_ok then
        printf "  Lifted to mod %o^%o = %o\n", p, target_precision, modulus;
    end if;

    // Display lifted coefficients
    printf "  Q1 (mod %o): %o\n", modulus, [c mod modulus : c in q1c];
    printf "  Q2 (mod %o): %o\n", modulus, [c mod modulus : c in q2c];
    printf "  Q3 (mod %o): %o\n", modulus, [c mod modulus : c in q3c];

    printf "\n";
end for;

// =====================================================================
// STEP 6: LLL recognition of number field coefficients
// =====================================================================

print "=== LLL RECOGNITION ===\n";

// Cyclotomic order for the coefficient field.
// Klein quartic: coefficients in Z[zeta_7], so n=7
// Fermat quartic: coefficients in Z[i], so n=4
// Set n here based on your curve:
n := 7;  // cyclotomic order (change as needed)

printf "Attempting LLL recognition in Z[zeta_%o]...\n", n;

// Lift a primitive n-th root of unity mod p^k via Newton iteration
function LiftZeta(p_val, prec, n_val)
    Fpx := GF(p_val);
    zeta_fp := Fpx!1;
    for a in [2..p_val-1] do
        if Order(Fpx!a) mod n_val eq 0 then
            zeta_fp := (Fpx!a)^(Order(Fpx!a) div n_val); break;
        end if;
    end for;
    zeta := Integers()!zeta_fp;
    pk := p_val;
    for step in [1..prec-1] do
        pk *:= p_val;
        residue := (zeta^n_val - 1) mod pk;
        deriv := (n_val * zeta^(n_val-1)) mod pk;
        inv_ok, inv_deriv := IsInvertible(IntegerRing(pk)!deriv);
        if not inv_ok then
            printf "WARNING: derivative not invertible mod %o\n", pk;
            return zeta, pk div p_val;
        end if;
        correction := (residue * Integers()!inv_deriv) mod pk;
        zeta := (zeta - correction) mod pk;
    end for;
    return zeta, p_val^prec;
end function;

function RecognizeZeta(val, mod_val, n_val, zeta_lift)
    deg := EulerPhi(n_val);
    zeta_powers := [zeta_lift^i mod mod_val : i in [0..deg-1]];
    M := ZeroMatrix(Integers(), deg+2, deg+2);
    scale := Isqrt(mod_val) + 1;
    for i in [1..deg] do
        M[i,i] := 1;
        M[i,deg+1] := zeta_powers[i] * scale;
    end for;
    M[deg+1,deg+1] := mod_val * scale;
    M[deg+2,deg+1] := -((val mod mod_val + mod_val) mod mod_val) * scale;
    M[deg+2,deg+2] := 1;
    Mred := LLL(M);
    for r in [1..Nrows(Mred)] do
        if Abs(Mred[r,deg+2]) eq 1 then
            sign := Mred[r,deg+2];
            coeffs := [sign*Mred[r,j] : j in [1..deg]];
            check := &+[coeffs[i]*zeta_powers[i] : i in [1..deg]] - val;
            if check mod mod_val eq 0 then
                return true, coeffs;
            end if;
        end if;
    end for;
    return false, [0 : i in [1..deg]];
end function;

// Lift zeta_n
zeta_val, actual_mod := LiftZeta(p, target_precision, n);
printf "zeta_%o mod %o = %o\n", n, actual_mod, zeta_val;
assert (zeta_val^n - 1) mod actual_mod eq 0;
for q in PrimeDivisors(n) do
    assert (zeta_val^(n div q) - 1) mod actual_mod ne 0;
end for;
printf "Verified: primitive %o-th root of unity mod %o.\n\n", n, actual_mod;

deg := EulerPhi(n);
mons_names := ["X^2","Y^2","Z^2","XY","XZ","YZ"];

for orb_idx in Sort(Setseq(Keys(orbit_reps))) do
    if orb_idx ge 1 and orb_idx le #orbit_data then
        printf "--- LLL: Orbit %o (size %o) ---\n", orb_idx, #orbit_data[orb_idx];
    else
        printf "--- LLL: J[2] class (key %o) ---\n", orb_idx;
    end if;
    dat := orbit_reps[orb_idx];
    Q2_fp := dat[1]; Q1_fp := dat[2]; Q3_fp := dat[3];
    mons_fp := [X^2, Y^2, Z^2, X*Y, X*Z, Y*Z];

    q2c := [LiftFp(MonomialCoefficient(Q2_fp, mons_fp[i])) : i in [1..6]];
    q1c := [LiftFp(MonomialCoefficient(Q1_fp, mons_fp[i])) : i in [1..6]];
    q3c := [LiftFp(MonomialCoefficient(Q3_fp, mons_fp[i])) : i in [1..6]];

    // Re-lift
    pk := p;
    for step in [1..target_precision-1] do
        d1, d2, d3 := HenselStep(q1c, q2c, q3c, pk);
        q1c := [q1c[i] + pk*d1[i] : i in [1..6]];
        q2c := [q2c[i] + pk*d2[i] : i in [1..6]];
        q3c := [q3c[i] + pk*d3[i] : i in [1..6]];
        pk *:= p;
    end for;

    for label in ["Q1", "Q2", "Q3"] do
        coeffs := label eq "Q1" select q1c else (label eq "Q2" select q2c else q3c);
        printf "  %o:", label;
        all_ok := true;
        for j in [1..6] do
            ok, zeta_coeffs := RecognizeZeta(coeffs[j], actual_mod, n, zeta_val);
            if ok then
                printf " %o=%o", mons_names[j], zeta_coeffs;
            else
                printf " %o=? (failed)", mons_names[j];
                all_ok := false;
            end if;
        end for;
        printf "\n";
        if not all_ok then
            printf "    (Some coefficients not recognized in Z[zeta_%o])\n", n;
        end if;
    end for;
    printf "\n";
end for;

print "Done.";
quit;
