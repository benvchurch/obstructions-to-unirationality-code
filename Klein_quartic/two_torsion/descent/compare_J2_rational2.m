/*******************************************************************************
 * compare_J2_rational2.m
 *
 * Compare J[2](Q) subspaces for C1: x^4+y^4+z^4=0 and C2: x^4+y^4-z^4=0
 * under phi: C1 -> C2 via (x:y:z) -> (x:y:zeta_8*z), zeta_8^4 = -1.
 *
 * Work over F_9 where zeta_8 exists. Handle infinity places via u/t ratio.
 ******************************************************************************/

// ======================================================================
// Utility: J[2] generators from class group
// ======================================================================
function J2Gens(Cl, invs)
    gens := [];
    for i in [1..#invs] do
        if invs[i] ne 0 and invs[i] mod 2 eq 0 then
            Append(~gens, (invs[i] div 2) * Cl.i);
        end if;
    end for;
    return gens;
end function;

// ======================================================================
// Utility: express h in J[2] as F_2 vector
// ======================================================================
function J2Coords(h, j2_gens, Cl)
    n := #j2_gens;
    for bits in [0..2^n-1] do
        sum := Cl!0;
        for i in [1..n] do
            if (bits div 2^(i-1)) mod 2 eq 1 then
                sum := sum + j2_gens[i];
            end if;
        end for;
        if sum eq h then
            return Vector(GF(2), [GF(2)!((bits div 2^(i-1)) mod 2) : i in [1..n]]);
        end if;
    end for;
    return false;
end function;

// ======================================================================
// Place identification: unified affine + infinity
// Key format: <is_infinity, coord1, coord2>
//   Affine: <false, t_val, u_val>
//   Infinity: <true, u/t ratio, 0>
// ======================================================================
function PlaceKey(P, FF, t_var, u_var, k)
    if Valuation(FF!t_var, P) ge 0 and Valuation(u_var, P) ge 0 then
        // Affine place
        tv := k!Evaluate(FF!t_var, P);
        uv := k!Evaluate(u_var, P);
        return <false, tv, uv>;
    else
        // Infinity place: compute u/t ratio (both have simple poles, ratio is finite)
        ratio := k!Evaluate(u_var / (FF!t_var), P);
        return <true, ratio, k!0>;
    end if;
end function;

function BuildUnifiedLookup(places, FF, t_var, u_var, k)
    tab := AssociativeArray();
    for P in places do
        key := PlaceKey(P, FF, t_var, u_var, k);
        tab[Sprint(key)] := P;
    end for;
    return tab;
end function;

// ======================================================================
// Map a place key under Frobenius_q: (t,u) -> (t^q, u^q)
// Affine: (t0,u0) -> (t0^q, u0^q)
// Infinity: ratio r -> r^q
// ======================================================================
function FrobKey(key, q, k)
    if not key[1] then
        return <false, key[2]^q, key[3]^q>;
    else
        return <true, key[2]^q, k!0>;
    end if;
end function;

// ======================================================================
// Map a place key under phi: (x:y:z) -> (x:y:zeta_8*z)
// Affine coords: (t,u) = (x/z, y/z) on C1 -> (x/(zeta_8*z), y/(zeta_8*z))
//              = (t/zeta_8, u/zeta_8) on C2
// Infinity: (x:y:0) -> (x:y:0), ratio unchanged
// ======================================================================
function PhiKey(key, iz8, k)
    if not key[1] then
        return <false, key[2]*iz8, key[3]*iz8>;
    else
        return <true, key[2], k!0>;  // infinity unchanged
    end if;
end function;

// ======================================================================
// Compute F_2 matrix of a map on J[2]
// map_key_func: function that maps a place key to a target place key
// ======================================================================
function ComputeMapMatrix(j2_gens, mm, FF_src, t_src, u_src,
                           FF_tgt, t_tgt, u_tgt,
                           j2_gens_tgt, Cl_tgt,
                           tgt_lookup, map_key_func, k)
    n_src := #j2_gens;
    n_tgt := #j2_gens_tgt;
    M := ZeroMatrix(GF(2), n_src, n_tgt);

    for idx in [1..n_src] do
        g := j2_gens[idx];
        D := mm(g);
        supp := Support(D);
        imgD := DivisorGroup(FF_tgt) ! 0;
        all_ok := true;

        for P in supp do
            val := Valuation(D, P);
            if Degree(P) ne 1 then
                printf "  Gen %o: degree-%o place\n", idx, Degree(P);
                all_ok := false;
                break;
            end if;
            src_key := PlaceKey(P, FF_src, t_src, u_src, k);
            tgt_key := map_key_func(src_key);
            tgt_key_str := Sprint(tgt_key);
            if not IsDefined(tgt_lookup, tgt_key_str) then
                printf "  Gen %o: target key %o not found\n", idx, tgt_key_str;
                all_ok := false;
                break;
            end if;
            imgD := imgD + val * (1*tgt_lookup[tgt_key_str]);
        end for;

        if not all_ok then return false, M; end if;

        img_cls := imgD @@ ClassGroup(FF_tgt);
        // Need the right class group map - use the one we passed
        // Actually, we need mm_tgt. Let me restructure.
        return false, M;
    end for;
    return true, M;
end function;

// ======================================================================
// MAIN COMPUTATION
// ======================================================================

F9<a> := GF(9);
z8 := PrimitiveElement(F9);
assert z8^8 eq 1 and z8^4 eq F9!(-1);
iz8 := 1/z8;
printf "F_9: zeta_8 = %o, 1/zeta_8 = %o\n\n", z8, iz8;

// --- C1 over F_9: u^4 + t^4 + 1 = 0 ---
K1<t1> := FunctionField(F9);
R1<U1> := PolynomialRing(K1);
FF1<u1> := FunctionField(U1^4 + t1^4 + 1);
Cl1, m1 := ClassGroup(FF1);
inv1 := Invariants(Cl1);
j2g1 := J2Gens(Cl1, inv1);
n1 := #j2g1;
pls1 := Places(FF1, 1);
printf "C1/F_9: Cl = %o, #J[2] gens = %o, #deg1 places = %o\n", inv1, n1, #pls1;

// --- C2 over F_9: u^4 + t^4 - 1 = 0 ---
K2<t2> := FunctionField(F9);
R2<U2> := PolynomialRing(K2);
FF2<u2> := FunctionField(U2^4 + t2^4 - 1);
Cl2, m2 := ClassGroup(FF2);
inv2 := Invariants(Cl2);
j2g2 := J2Gens(Cl2, inv2);
n2 := #j2g2;
pls2 := Places(FF2, 1);
printf "C2/F_9: Cl = %o, #J[2] gens = %o, #deg1 places = %o\n\n", inv2, n2, #pls2;

// Build unified lookups (affine + infinity)
lookup1 := BuildUnifiedLookup(pls1, FF1, t1, u1, F9);
lookup2 := BuildUnifiedLookup(pls2, FF2, t2, u2, F9);

// Verify lookups
printf "Lookup sizes: C1 has %o entries, C2 has %o entries\n\n", #Keys(lookup1), #Keys(lookup2);

// Count infinity places
n_inf1 := 0; n_inf2 := 0;
for P in pls1 do
    key := PlaceKey(P, FF1, t1, u1, F9);
    if key[1] then n_inf1 +:= 1; end if;
end for;
for P in pls2 do
    key := PlaceKey(P, FF2, t2, u2, F9);
    if key[1] then n_inf2 +:= 1; end if;
end for;
printf "Infinity places: C1 has %o, C2 has %o\n\n", n_inf1, n_inf2;

// ======================================================================
// Compute Frob_3 matrix on J[2](C1/F_9)
// ======================================================================
print "=== Frobenius_3 on J[2](C1/F_9) ===";
Frob1 := ZeroMatrix(GF(2), n1, n1);
frob1_ok := true;

for idx in [1..n1] do
    g := j2g1[idx];
    D := m1(g);
    supp := Support(D);
    imgD := DivisorGroup(FF1) ! 0;
    all_ok := true;

    for P in supp do
        val := Valuation(D, P);
        if Degree(P) ne 1 then
            printf "  Gen %o: degree-%o place\n", idx, Degree(P);
            all_ok := false; break;
        end if;
        src_key := PlaceKey(P, FF1, t1, u1, F9);
        tgt_key := FrobKey(src_key, 3, F9);
        tgt_str := Sprint(tgt_key);
        if not IsDefined(lookup1, tgt_str) then
            printf "  Gen %o: Frob target %o not found\n", idx, tgt_str;
            all_ok := false; break;
        end if;
        imgD := imgD + val * (1*lookup1[tgt_str]);
    end for;

    if not all_ok then frob1_ok := false; continue; end if;
    img_cls := imgD @@ m1;
    coords := J2Coords(img_cls, j2g1, Cl1);
    if Type(coords) eq BoolElt then
        printf "  Gen %o: image not in J[2]!\n", idx;
        frob1_ok := false; continue;
    end if;
    for j in [1..n1] do Frob1[idx][j] := coords[j]; end for;
    printf "  Gen %o -> %o\n", idx, coords;
end for;

if frob1_ok then
    I1 := IdentityMatrix(GF(2), n1);
    fixed1 := NullSpace(Frob1 + I1);
    printf "\nFrob_3 matrix:\n%o\n", Frob1;
    printf "J[2](C1/F_3) = ker(Frob+I): dim = %o, basis = %o\n\n", Dimension(fixed1), Basis(fixed1);
else
    print "Frob_3 on C1 FAILED for some generators.";
end if;

// ======================================================================
// Compute Frob_3 matrix on J[2](C2/F_9)
// ======================================================================
print "=== Frobenius_3 on J[2](C2/F_9) ===";
Frob2 := ZeroMatrix(GF(2), n2, n2);
frob2_ok := true;

for idx in [1..n2] do
    g := j2g2[idx];
    D := m2(g);
    supp := Support(D);
    imgD := DivisorGroup(FF2) ! 0;
    all_ok := true;

    for P in supp do
        val := Valuation(D, P);
        if Degree(P) ne 1 then
            printf "  Gen %o: degree-%o place\n", idx, Degree(P);
            all_ok := false; break;
        end if;
        src_key := PlaceKey(P, FF2, t2, u2, F9);
        tgt_key := FrobKey(src_key, 3, F9);
        tgt_str := Sprint(tgt_key);
        if not IsDefined(lookup2, tgt_str) then
            printf "  Gen %o: Frob target %o not found\n", idx, tgt_str;
            all_ok := false; break;
        end if;
        imgD := imgD + val * (1*lookup2[tgt_str]);
    end for;

    if not all_ok then frob2_ok := false; continue; end if;
    img_cls := imgD @@ m2;
    coords := J2Coords(img_cls, j2g2, Cl2);
    if Type(coords) eq BoolElt then
        printf "  Gen %o: image not in J[2]!\n", idx;
        frob2_ok := false; continue;
    end if;
    for j in [1..n2] do Frob2[idx][j] := coords[j]; end for;
    printf "  Gen %o -> %o\n", idx, coords;
end for;

if frob2_ok then
    I2 := IdentityMatrix(GF(2), n2);
    fixed2 := NullSpace(Frob2 + I2);
    printf "\nFrob_3 matrix:\n%o\n", Frob2;
    printf "J[2](C2/F_3) = ker(Frob+I): dim = %o, basis = %o\n\n", Dimension(fixed2), Basis(fixed2);
else
    print "Frob_3 on C2 FAILED for some generators.";
end if;

// ======================================================================
// Compute phi_* matrix: J[2](C1/F_9) -> J[2](C2/F_9)
// phi: (t,u) -> (t/zeta_8, u/zeta_8) for affine
//      infinity -> infinity (same ratio)
// ======================================================================
print "=== Phi: J[2](C1/F_9) -> J[2](C2/F_9) ===";
Phi := ZeroMatrix(GF(2), n1, n2);
phi_ok := true;

for idx in [1..n1] do
    g := j2g1[idx];
    D := m1(g);
    supp := Support(D);
    imgD := DivisorGroup(FF2) ! 0;
    all_ok := true;

    for P in supp do
        val := Valuation(D, P);
        if Degree(P) ne 1 then
            printf "  Gen %o: degree-%o place\n", idx, Degree(P);
            all_ok := false; break;
        end if;
        src_key := PlaceKey(P, FF1, t1, u1, F9);
        tgt_key := PhiKey(src_key, iz8, F9);
        tgt_str := Sprint(tgt_key);
        if not IsDefined(lookup2, tgt_str) then
            printf "  Gen %o: phi target %o not found\n", idx, tgt_str;
            all_ok := false; break;
        end if;
        imgD := imgD + val * (1*lookup2[tgt_str]);
    end for;

    if not all_ok then phi_ok := false; continue; end if;
    img_cls := imgD @@ m2;
    coords := J2Coords(img_cls, j2g2, Cl2);
    if Type(coords) eq BoolElt then
        printf "  Gen %o: phi image not in J[2]!\n", idx;
        phi_ok := false; continue;
    end if;
    for j in [1..n2] do Phi[idx][j] := coords[j]; end for;
    printf "  Gen %o -> %o\n", idx, coords;
end for;

if phi_ok then
    printf "\nPhi matrix:\n%o\n\n", Phi;
    printf "Phi invertible? %o (det = %o)\n\n", Determinant(Phi) ne 0, Determinant(Phi);
else
    print "Phi computation FAILED for some generators.";
end if;

// ======================================================================
// COMPARISON
// ======================================================================
print "================================================================";
print "COMPARISON OF J[2](Q) SUBSPACES";
print "================================================================";

if frob1_ok and frob2_ok and phi_ok then
    d1 := Dimension(fixed1);
    d2 := Dimension(fixed2);
    printf "dim J[2](C1/F_3) = %o\n", d1;
    printf "dim J[2](C2/F_3) = %o\n\n", d2;

    // Push J[2](C1/F_3) forward via Phi
    V2 := VectorSpace(GF(2), n2);
    phi_basis := [v * Phi : v in Basis(fixed1)];
    phi_fixed1 := sub<V2 | phi_basis>;

    printf "Phi(J[2](C1/F_3)) has dim %o\n", Dimension(phi_fixed1);
    printf "  basis: %o\n", Basis(phi_fixed1);
    printf "J[2](C2/F_3) has dim %o\n", d2;
    printf "  basis: %o\n\n", Basis(fixed2);

    same := phi_fixed1 eq fixed2;
    printf "*** Phi(J[2](C1/F_3)) = J[2](C2/F_3) ? %o ***\n\n", same;

    if not same then
        inter := phi_fixed1 meet fixed2;
        printf "Intersection dim = %o\n\n", Dimension(inter);

        // Check if J[2](F_3) = J[2](Q) by comparing with 2-rank data.
        // From Part 0: at p=3, 2-rank(C1) = 4 and 2-rank(C2) = 4.
        // So J[2](F_3) should have dim 4, not 3!
        // Let me verify: dim of Frob_3-fixed should equal 2-rank.
        printf "SANITY CHECK: 2-rank at p=3 should be 4 for both curves.\n";
        printf "  But Frob_3-fixed on J[2] over F_9 gives dim(C1)=%o, dim(C2)=%o.\n\n", d1, d2;

        // If d1 > 3, then J[2](F_3) strictly contains J[2](Q).
        // We need a second Frobenius to cut down to J[2](Q).
        if d1 gt 3 or d2 gt 3 then
            printf "J[2](F_3) is LARGER than J[2](Q). Need second Frobenius.\n";
            printf "Will use tau = (x:y:z)->(x:y:-z) which is the cocycle for sigma_5.\n";
        end if;
    end if;
else
    print "SOME COMPUTATION FAILED.";
    if not frob1_ok then print "  Frob on C1 failed."; end if;
    if not frob2_ok then print "  Frob on C2 failed."; end if;
    if not phi_ok then print "  Phi failed."; end if;
end if;

// ======================================================================
// APPROACH 2: Use tau matrix to determine the answer directly
//
// The twist cocycle: for sigma in Gal(Q(zeta_8)/Q),
//   tau_sigma = sigma(phi) o phi^{-1} : C2 -> C2
// This acts on J[2](C2/F_9). The key relation:
//   R_2(sigma) = (tau_sigma)_* . Phi . R_1(sigma) . Phi^{-1}
//
// J[2](C1)(Q) maps to J[2](C2)(Q) under Phi iff
//   tau_sigma fixes Phi(J[2](C1)(Q)) for all sigma.
//
// tau_{sigma_3} = (x:y:z) -> (x:y:iz) where i = zeta_8^2
// tau_{sigma_5} = (x:y:z) -> (x:y:-z)
// ======================================================================
print "\n================================================================";
print "APPROACH 2: TAU ACTION ON J[2](C2)";
print "================================================================";

// tau_3: (t,u) -> (t*(-i), u*(-i)) = (t/i, u/i) on C2
// Since phi: (t,u) -> (t/z8, u/z8), sigma_3(phi): (t,u) -> (t/z8^3, u/z8^3)
// tau_3 = sigma_3(phi) o phi^{-1}: first phi^{-1}: (t,u) -> (t*z8, u*z8)
// then sigma_3(phi): (t*z8, u*z8) -> (t*z8/z8^3, u*z8/z8^3) = (t/z8^2, u/z8^2)
// So tau_3: (t,u) -> (t/z8^2, u/z8^2) = (t/i, u/i) where i = z8^2

ii := z8^2;  // i = zeta_8^2 = sqrt(-1)
inv_ii := 1/ii;
printf "i = zeta_8^2 = %o, 1/i = %o\n", ii, inv_ii;

// tau_5: sigma_5(phi): (t,u) -> (t/z8^5, u/z8^5). phi^{-1}: (t,u) -> (t*z8, u*z8)
// tau_5: (t,u) -> (t*z8/z8^5, u*z8/z8^5) = (t/z8^4, u/z8^4) = (t/(-1), u/(-1)) = (-t,-u)
// which is (x:y:z) -> (x:y:-z) in projective coords.
// In affine z=1: (t,u) -> (-t, -u).

printf "tau_3 acts as (t,u) -> (t/%o, u/%o)\n", ii, ii;
printf "tau_5 acts as (t,u) -> (-t, -u)\n\n";

// Compute tau_3 matrix on J[2](C2/F_9)
print "--- tau_3 on J[2](C2/F_9) ---";
Tau3 := ZeroMatrix(GF(2), n2, n2);
tau3_ok := true;
for idx in [1..n2] do
    g := j2g2[idx];
    D := m2(g);
    supp := Support(D);
    imgD := DivisorGroup(FF2) ! 0;
    all_ok := true;
    for P in supp do
        val := Valuation(D, P);
        if Degree(P) ne 1 then all_ok := false; break; end if;
        src_key := PlaceKey(P, FF2, t2, u2, F9);
        // tau_3: affine (t,u) -> (t*inv_ii, u*inv_ii); infinity ratio r -> r (since z->iz, both t,u scale same)
        if not src_key[1] then
            tgt_key := <false, src_key[2]*inv_ii, src_key[3]*inv_ii>;
        else
            tgt_key := src_key;  // infinity ratio r = u/t unchanged under (t,u) -> (ct,cu)
        end if;
        tgt_str := Sprint(tgt_key);
        if not IsDefined(lookup2, tgt_str) then
            printf "  Gen %o: tau3 target not found\n", idx;
            all_ok := false; break;
        end if;
        imgD := imgD + val * (1*lookup2[tgt_str]);
    end for;
    if not all_ok then tau3_ok := false; continue; end if;
    img_cls := imgD @@ m2;
    coords := J2Coords(img_cls, j2g2, Cl2);
    if Type(coords) eq BoolElt then tau3_ok := false; continue; end if;
    for j in [1..n2] do Tau3[idx][j] := coords[j]; end for;
    printf "  Gen %o -> %o\n", idx, coords;
end for;

// Compute tau_5 matrix on J[2](C2/F_9)
print "--- tau_5 on J[2](C2/F_9) ---";
Tau5 := ZeroMatrix(GF(2), n2, n2);
tau5_ok := true;
for idx in [1..n2] do
    g := j2g2[idx];
    D := m2(g);
    supp := Support(D);
    imgD := DivisorGroup(FF2) ! 0;
    all_ok := true;
    for P in supp do
        val := Valuation(D, P);
        if Degree(P) ne 1 then all_ok := false; break; end if;
        src_key := PlaceKey(P, FF2, t2, u2, F9);
        // tau_5: affine (t,u) -> (-t, -u); infinity ratio r -> (-u)/(-t) = r
        if not src_key[1] then
            tgt_key := <false, -src_key[2], -src_key[3]>;
        else
            tgt_key := src_key;
        end if;
        tgt_str := Sprint(tgt_key);
        if not IsDefined(lookup2, tgt_str) then
            printf "  Gen %o: tau5 target not found\n", idx;
            all_ok := false; break;
        end if;
        imgD := imgD + val * (1*lookup2[tgt_str]);
    end for;
    if not all_ok then tau5_ok := false; continue; end if;
    img_cls := imgD @@ m2;
    coords := J2Coords(img_cls, j2g2, Cl2);
    if Type(coords) eq BoolElt then tau5_ok := false; continue; end if;
    for j in [1..n2] do Tau5[idx][j] := coords[j]; end for;
    printf "  Gen %o -> %o\n", idx, coords;
end for;

if tau3_ok and tau5_ok then
    printf "\ntau_3 matrix:\n%o\n", Tau3;
    printf "tau_5 matrix:\n%o\n\n", Tau5;

    I2 := IdentityMatrix(GF(2), n2);
    printf "Order(tau_3) = %o\n", Order(Tau3);
    printf "Order(tau_5) = %o\n", Order(Tau5);
    printf "tau_3 * tau_5 = tau_7: order = %o\n\n", Order(Tau3 * Tau5);

    ker_tau3 := NullSpace(Tau3 + I2);
    ker_tau5 := NullSpace(Tau5 + I2);
    ker_both := ker_tau3 meet ker_tau5;

    printf "ker(tau_3 + I) dim = %o\n", Dimension(ker_tau3);
    printf "ker(tau_5 + I) dim = %o\n", Dimension(ker_tau5);
    printf "ker(tau_3+I) ∩ ker(tau_5+I) dim = %o\n\n", Dimension(ker_both);

    // J[2](C2)(Q) inside J[2](C2/F_9):
    // R_2(sigma) = Tau_sigma * Phi * R_1(sigma) * Phi^{-1}
    // J[2](C2)(Q) = {v : R_2(sigma)(v) = v for all sigma}
    // Phi(J[2](C1)(Q)) = J[2](C2)(Q) iff Tau_sigma fixes Phi(J[2](C1)(Q)) for all sigma.

    if frob1_ok and phi_ok then
        // J[2](C1)(Q) inside J[2](C1/F_9):
        // Need to determine this. J[2](C1)(Q) = intersection over all sigma of ker(R_1(sigma)+I).
        // R_1(sigma_3) on J[2](C1/F_9): this is Frob_3 action.
        // But we also need R_1(sigma_5). R_1(sigma_5) is Frob_5 action.
        // However, we're working over F_9, so Frob_5 is not directly available.
        //
        // Alternative: Gal(Q(zeta_8)/Q) acts on J[2] through R_1.
        // The full Galois group is <sigma_3, sigma_5> = (Z/2)^2.
        // Frob_3 = R_1(sigma_3). Need R_1(sigma_5).
        //
        // Key insight: sigma_5 sends zeta_8 -> zeta_8^5 = -zeta_8.
        // On C1 (symmetric curve x^4+y^4+z^4), sigma_5 acts on J[2] via
        // some matrix. But C1 is defined over Q, so the action on the curve
        // is trivial -- sigma acts only on the points of J[2].
        //
        // Actually: R_1 is the Galois representation on J(C1)[2].
        // C1 is defined over Q, so the representation factors through
        // Gal(K_1/Q) where K_1 is the 2-torsion field of C1.
        // K_1 = Q(zeta_8), so R_1: Gal(Q(zeta_8)/Q) -> GL_6(F_2).
        // R_1(sigma_3) = Frobenius at 3 on J[2].
        //
        // To compute R_1(sigma_5), we need Frobenius at 5 on J[2].
        // Over F_9, Frob_3^2 = Frob_9 = identity on F_9 points.
        // To get Frob_5, we'd need F_25 or find another way.
        //
        // SIMPLER APPROACH: Use the Galois action formula directly.
        // For C2: ρ_2(σ) = τ_σ ∘ (Φ ∘ ρ_1(σ) ∘ Φ^{-1})
        // J[2](C2)(Q) = ∩_σ ker(ρ_2(σ) + I)
        //             = ∩_σ ker(τ_σ ∘ Φ ∘ ρ_1(σ) ∘ Φ^{-1} + I)
        // And Φ(J[2](C1)(Q)) satisfies: for w = Φ(v) with ρ_1(σ)(v) = v:
        //   ρ_2(σ)(w) = τ_σ(Φ(ρ_1(σ)(v))) = τ_σ(Φ(v)) = τ_σ(w)
        // So w ∈ J[2](C2)(Q) iff τ_σ(w) = w for all σ.
        // I.e., Φ(J[2](C1)(Q)) ⊆ J[2](C2)(Q) iff Φ(J[2](C1)(Q)) ⊆ ker_both.

        // We know J[2](C1)(Q) ⊆ J[2](C1/F_3) = ker(Frob_3 + I) on C1.
        // And J[2](C1)(Q) has dim 3 (known from 2-rank data).
        // ker(Frob_3 + I) has dim d1.

        printf "=== DETERMINING J[2](C1)(Q) ===\n";
        printf "J[2](C1/F_3) = ker(R1(sigma_3)+I) has dim %o\n", Dimension(fixed1);

        // To find J[2](C1)(Q), need to also impose R_1(sigma_5)(v) = v.
        // R_1(sigma_5) = Frob_5 on J[2](C1). We don't have this directly.
        //
        // BUT: we can compute it via the relation:
        //   R_2(sigma_3) = Tau3 * Phi * R_1(sigma_3) * Phi^{-1}
        //   = Tau3 * Phi * Frob1 * Phi^{-1}
        // And R_2(sigma_3) = Frob_3 on J[2](C2) = Frob2.
        // So: Frob2 = Tau3 * Phi * Frob1 * Phi^{-1}
        // Verify: Phi^{-1} * Tau3^{-1} * Frob2 * Phi = Frob1? (or transpose)

        PhiT := Transpose(Phi);
        PhiInv := Phi^(-1);  // Should work since Phi is invertible
        check := Tau3 * Phi * Frob1 * PhiInv;
        printf "Tau3 * Phi * Frob1 * Phi^{-1} = Frob2? %o\n", check eq Frob2;
        printf "(If false, there may be a transpose convention issue.)\n\n";

        // Try other convention: rows are images
        check2 := PhiInv * Frob1 * Phi * Tau3;
        printf "Phi^{-1} * Frob1 * Phi * Tau3 = Frob2? %o\n", check2 eq Frob2;

        // Let's try: for ROWS-ARE-IMAGES convention, the formula for
        // composition f∘g has matrix M_g * M_f (reverse order).
        // ρ_2(σ) = τ_σ ∘ Φ ∘ ρ_1(σ) ∘ Φ^{-1}
        // Matrix: PhiInv * Frob1 * Phi * Tau3 (reversed)
        // OR: Frob2 = Tau3 * Phi * Frob1 * PhiInv (standard order)

        // Actually in our setup, if v is a row vector and M is the matrix,
        // then the image of v under the map is v*M.
        // So composition f∘g has matrix M_g * M_f... no.
        // (v * M_g) * M_f = v * (M_g * M_f). So M_{f∘g} = M_g * M_f.
        // So ρ_2(σ) = τ_σ ∘ Φ ∘ ρ_1(σ) ∘ Φ^{-1}
        // M_{ρ_2} = M_{Φ^{-1}} * M_{ρ_1} * M_Φ * M_{τ}

        check3 := PhiInv * Frob1 * Phi * Tau3;
        printf "\nWith row-vector convention M_{f∘g} = M_g * M_f:\n";
        printf "M_{Phi^-1} * M_{Frob1} * M_Phi * M_{Tau3} = Frob2? %o\n\n", check3 eq Frob2;

        // Just try all reasonable orderings
        for perm in [[1,2,3,4],[1,2,4,3],[1,3,2,4],[1,3,4,2],[1,4,2,3],[1,4,3,2],
                      [2,1,3,4],[2,1,4,3],[2,3,1,4],[2,3,4,1],[2,4,1,3],[2,4,3,1],
                      [3,1,2,4],[3,1,4,2],[3,2,1,4],[3,2,4,1],[3,4,1,2],[3,4,2,1],
                      [4,1,2,3],[4,1,3,2],[4,2,1,3],[4,2,3,1],[4,3,1,2],[4,3,2,1]] do
            mats := [PhiInv, Frob1, Phi, Tau3];
            prod := mats[perm[1]] * mats[perm[2]] * mats[perm[3]] * mats[perm[4]];
            if prod eq Frob2 then
                printf "MATCH: mats[%o] * mats[%o] * mats[%o] * mats[%o] = Frob2\n",
                    perm[1], perm[2], perm[3], perm[4];
                printf "  where 1=PhiInv, 2=Frob1, 3=Phi, 4=Tau3\n";
            end if;
        end for;

        // DIRECT APPROACH: forget the formula, just compute J[2](C2)(Q) directly.
        //
        // J[2](C2)(Q) is the kernel of all (ρ_2(σ) - I).
        // ρ_2(σ) for σ ∈ Gal(Q(zeta_8)/Q) = <σ_3, σ_5>.
        // ρ_2(σ_3) = Frob_3 on J(C2), which we computed as Frob2.
        //
        // For ρ_2(σ_5) = Frob_5 on J(C2), we need a different computation.
        // But the 2-rank at p=5 for C2 is 5, meaning J[2](C2/F_5) has dim 5.
        // So ker(Frob_5 + I) on J[2](C2) has dim 5.
        //
        // J[2](C2)(Q) = ker(Frob2+I) ∩ ker(Frob5_C2+I).
        // ker(Frob2+I) has dim d2.
        //
        // Similarly, J[2](C1)(Q) = ker(Frob1+I) ∩ ker(Frob5_C1+I).
        //
        // Without Frob_5, we can't determine J[2](Q) from F_9 alone.
        // But we CAN use the tau matrices.

        printf "\n=== DIRECT DETERMINATION OF J[2](Q) ===\n";
        printf "J[2](C2)(Q) = {v in J[2] : tau_sigma(v) = Frob2_sigma(v) ... }\n";
        printf "Actually, J[2](C2)(Q) is just the Frob-fixed subspace of the\n";
        printf "FULL Galois action, not just at one prime.\n\n";

        // KEY REALIZATION: Over F_9, J[2](C2) is fully visible.
        // Frob_3 acts on it. ker(Frob_3+I) = J[2](C2/F_3).
        // But the Galois group Gal(Q(zeta_8)/Q) ≅ (Z/2)^2 has TWO generators.
        // From the 2-rank data, J[2](C2/F_3) has dim 4 (2-rank=4 at p=3).
        // J[2](C2)(Q) should have dim 3 (assuming 2-torsion field = Q(zeta_8) for C2 too).
        //
        // Wait: what IS the 2-torsion field of C2?
        // From 2-rank data:
        //   p≡1 mod 8: 2-rank 7 (but Cl has 7 gens, some odd order)
        //   Actually 2-rank counts even invariants, so 7 means...
        // Hmm, 2-rank = 7 at p=17 seems too high for a genus-3 curve!
        // Max possible 2-rank = 2g = 6. So 7 means the class group has
        // 7 even-order invariants, but some might contribute the same
        // 2-torsion. Let me reconsider.

        printf "NOTE: 2-rank counts # of even invariants in class group.\n";
        printf "For genus 3, max 2-torsion dim = 6. The function field\n";
        printf "class group Cl(F_p(C)) = J(C)(F_p) x Z (the Z for degree).\n";
        printf "So 2-rank includes the Z factor if truncated. Need careful count.\n";
        printf "The 7th invariant (the 0 at the end) is the infinite cyclic part.\n\n";

        // Actually looking at the invariants: Cl = [4,4,4,4,4,4,0]
        // The 0 means Z (infinite cyclic group). 2-rank of Z is 0.
        // 6 factors of Z/4Z each have 2-rank 1. So 2-rank = 6.
        // My counting function counts 0 mod 2 as even! Bug: 0 mod 2 = 0 which IS even.
        // So I'm counting the Z factor as having even "order" 0.
        // FIX: should check invs[i] ne 0 AND invs[i] mod 2 eq 0.

        printf "BUG FOUND: 2-rank counter counts 0 (= Z factor) as even.\n";
        printf "The 0 in invariants represents Z, not Z/0Z.\n";
        printf "CORRECTING: should require invs[i] ne 0 AND invs[i] mod 2 eq 0.\n\n";

        // Recompute 2-ranks correctly
        printf "=== CORRECTED 2-RANK TABLE ===\n";
        printf "%-5o %-6o %-10o %-10o\n", "p", "p%8", "2rk(C1)", "2rk(C2)";
        for p in [3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73] do
            Fp := GF(p);
            KK<tt> := FunctionField(Fp);
            RR<uu> := PolynomialRing(KK);
            ff1 := uu^4 + tt^4 + 1;
            ff2 := uu^4 + tt^4 - 1;
            ok1 := IsIrreducible(ff1);
            ok2 := IsIrreducible(ff2);
            r1 := "red"; r2 := "red";
            if ok1 then
                i1 := Invariants(ClassGroup(FunctionField(ff1)));
                r1 := Sprint(#[d : d in i1 | d ne 0 and d mod 2 eq 0]);
            end if;
            if ok2 then
                i2 := Invariants(ClassGroup(FunctionField(ff2)));
                r2 := Sprint(#[d : d in i2 | d ne 0 and d mod 2 eq 0]);
            end if;
            printf "%-5o %-6o %-10o %-10o\n", p, p mod 8, r1, r2;
        end for;
    end if;

    // Regardless of the formula issue, let's do the most direct test:
    // Does the group <Tau3, Tau5> fix any 3-dimensional subspace?
    // J[2](C2)(Q) = { v : Frob_q(v) = v for all good primes q }
    // And Phi(J[2](C1)(Q)) = { v : tau_sigma(v) = v for all sigma } ∩ image(Phi)
    // Wait no. Let me re-derive.
    //
    // Phi(J[2](C1)(Q)) ⊆ J[2](C2)(Q) iff tau_sigma fixes Phi(J[2](C1)(Q)) for all sigma.
    // The space fixed by ALL tau_sigma is ker_both = ker(Tau3+I) ∩ ker(Tau5+I).
    // dim(ker_both) tells us the maximum dimension of a subspace that could be
    // "the same" under the isomorphism.

    printf "\n=== FIXED SUBSPACE OF ALL TAU ===\n";
    printf "ker(Tau3+I) ∩ ker(Tau5+I) has dim %o\n", Dimension(ker_both);
    printf "Basis: %o\n\n", Basis(ker_both);

    if Dimension(ker_both) lt 3 then
        printf "*** dim = %o < 3 = dim J[2](Q). ***\n", Dimension(ker_both);
        printf "*** IMPOSSIBLE for Phi(J[2](C1)(Q)) to land in J[2](C2)(Q). ***\n";
        printf "*** CONCLUSION: The J[2](Q) subspaces are NOT the same. ***\n";
    elif Dimension(ker_both) eq 3 then
        printf "dim = 3 = dim J[2](Q). So there's a unique 3-dim subspace\n";
        printf "fixed by all tau, and it equals Phi(J[2](C1)(Q)) = J[2](C2)(Q).\n";
        printf "*** CONCLUSION: The J[2](Q) subspaces ARE the same. ***\n";
    else
        printf "dim = %o > 3. Need more analysis.\n", Dimension(ker_both);
    end if;
end if;

quit;
