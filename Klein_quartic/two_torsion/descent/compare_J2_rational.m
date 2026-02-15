/*******************************************************************************
 * compare_J2_rational.m
 *
 * Compare J[2](Q) subspaces for C1: x^4+y^4+z^4=0 and C2: x^4+y^4-z^4=0
 * under the isomorphism phi: C1 -> C2 via (x:y:z) -> (x:y:zeta_8*z).
 *
 * Strategy: Work over F_9 (where zeta_8 exists) and F_25.
 * Express Frob and phi as F_2-matrices on J[2].
 * Compare the Frobenius-fixed subspaces = J[2](Q) candidates.
 ******************************************************************************/

// ======================================================================
// Utility functions
// ======================================================================

function J2Gens(Cl, invs)
    // Return generators of J[2] as a list of class group elements
    gens := [];
    for i in [1..#invs] do
        if invs[i] ne 0 and invs[i] mod 2 eq 0 then
            Append(~gens, (invs[i] div 2) * Cl.i);
        end if;
    end for;
    return gens;
end function;

function J2Coords(h, j2_gens, Cl)
    // Express h in J[2] as an F_2 vector w.r.t. j2_gens
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

function MapDivisor(D, src_FF, src_t, src_u, tgt_FF, tgt_t, tgt_u,
                     coord_map, lookup, k)
    // Map a divisor D on src to tgt using coord_map: (t0,u0) -> (t0',u0')
    // lookup maps Sprint(<t0',u0'>) -> place on tgt
    supp := Support(D);
    result := DivisorGroup(tgt_FF) ! 0;
    for P in supp do
        n := Valuation(D, P);
        if Degree(P) ne 1 then
            return false, result;
        end if;
        if Valuation(src_FF!src_t, P) lt 0 or Valuation(src_u, P) lt 0 then
            // Place at infinity - handle separately
            return false, result;
        end if;
        tv := k!Evaluate(src_FF!src_t, P);
        uv := k!Evaluate(src_u, P);
        target_t, target_u := Explode(coord_map(tv, uv));
        key := Sprint(<target_t, target_u>);
        if not IsDefined(lookup, key) then
            return false, result;
        end if;
        result := result + n * (1*lookup[key]);
    end for;
    return true, result;
end function;

function BuildLookup(places, FF, t_var, u_var, k)
    // Build affine coordinate -> place lookup
    tab := AssociativeArray();
    for P in places do
        if Valuation(FF!t_var, P) lt 0 or Valuation(u_var, P) lt 0 then
            continue;
        end if;
        tv := k!Evaluate(FF!t_var, P);
        uv := k!Evaluate(u_var, P);
        key := Sprint(<tv, uv>);
        tab[key] := P;
    end for;
    return tab;
end function;

function ComputeMatrix(j2_gens, mm, src_FF, src_t, src_u, tgt_FF, tgt_t, tgt_u,
                        tgt_j2_gens, tgt_Cl, coord_map, lookup, k)
    // Compute the F_2 matrix of coord_map on J[2]
    n := #j2_gens;
    M := ZeroMatrix(GF(2), n, n);
    for idx in [1..n] do
        g := j2_gens[idx];
        D := mm(g);
        ok, imgD := MapDivisor(D, src_FF, src_t, src_u, tgt_FF, tgt_t, tgt_u,
                                coord_map, lookup, k);
        if not ok then
            printf "  Generator %o: divisor involves non-degree-1 or infinity places\n", idx;
            return false, M;
        end if;
        // Class of imgD in target class group
        tgt_mm := ClassGroup(tgt_FF);
        _, tgt_mm_map := ClassGroup(tgt_FF);
        img_cls := imgD @@ tgt_mm_map;

        // Wait, we need to use the right class group map.
        // Let me restructure...
        return false, M;
    end for;
    return true, M;
end function;

// ======================================================================
// PART 0: 2-rank comparison to determine dim J[2](Q) for both curves
// ======================================================================
print "================================================================";
print "PART 0: 2-RANK PATTERN FOR C1 AND C2";
print "================================================================";
printf "%-5o %-6o %-10o %-10o\n", "p", "p%8", "2rk(C1)", "2rk(C2)";
printf "%-5o %-6o %-10o %-10o\n", "---", "---", "-------", "-------";

for p in [3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73] do
    Fp := GF(p);
    K<t> := FunctionField(Fp);
    R<u> := PolynomialRing(K);

    f1 := u^4 + t^4 + 1;
    f2 := u^4 + t^4 - 1;

    ok1 := IsIrreducible(f1);
    ok2 := IsIrreducible(f2);

    if not ok1 and not ok2 then
        printf "%-5o %-6o  BOTH REDUCIBLE\n", p, p mod 8;
        continue;
    end if;

    rk1_str := "red";
    rk2_str := "red";

    if ok1 then
        FF1 := FunctionField(f1);
        inv1 := Invariants(ClassGroup(FF1));
        rk1 := #[d : d in inv1 | d mod 2 eq 0];
        rk1_str := Sprint(rk1);
    end if;
    if ok2 then
        FF2 := FunctionField(f2);
        inv2 := Invariants(ClassGroup(FF2));
        rk2 := #[d : d in inv2 | d mod 2 eq 0];
        rk2_str := Sprint(rk2);
    end if;

    printf "%-5o %-6o %-10o %-10o\n", p, p mod 8, rk1_str, rk2_str;
end for;

// ======================================================================
// PART 1: Over F_9, compute J[2] and Frobenius/phi matrices
// ======================================================================
print "\n================================================================";
print "PART 1: J[2] COMPARISON OVER F_9";
print "================================================================";

F9<a> := GF(9);
// Find zeta_8 in F_9 (|F_9*| = 8, so primitive 8th root exists)
z8 := PrimitiveElement(F9);  // This has order 8
assert z8^8 eq 1 and z8^4 eq F9!(-1);
printf "F_9 = F_3(%o), zeta_8 = %o, zeta_8^4 = %o\n\n", a, z8, z8^4;

// --- C1 over F_9 ---
K1<t1> := FunctionField(F9);
R1<U1> := PolynomialRing(K1);
FF1<u1> := FunctionField(U1^4 + t1^4 + 1);
Cl1, m1 := ClassGroup(FF1);
inv1 := Invariants(Cl1);
j2g1 := J2Gens(Cl1, inv1);
printf "C1/F_9: Cl = %o, #J[2] gens = %o\n", inv1, #j2g1;

// --- C2 over F_9 ---
K2<t2> := FunctionField(F9);
R2<U2> := PolynomialRing(K2);
FF2<u2> := FunctionField(U2^4 + t2^4 - 1);
Cl2, m2 := ClassGroup(FF2);
inv2 := Invariants(Cl2);
j2g2 := J2Gens(Cl2, inv2);
printf "C2/F_9: Cl = %o, #J[2] gens = %o\n", inv2, #j2g2;

n1 := #j2g1;
n2 := #j2g2;

// Enumerate degree-1 places
pls1 := Places(FF1, 1);
pls2 := Places(FF2, 1);
printf "\n#deg-1 places: C1 has %o, C2 has %o\n\n", #pls1, #pls2;

// Build lookups
lookup1 := BuildLookup(pls1, FF1, t1, u1, F9);
lookup2 := BuildLookup(pls2, FF2, t2, u2, F9);

// ======================================================================
// Compute Frob_3 on J[2](C1/F_9) as F_2 matrix
// Frob_3: (t0, u0) -> (t0^3, u0^3)
// ======================================================================
print "--- Frobenius_3 on J[2](C1/F_9) ---";
frob_map := func<tv, uv | <tv^3, uv^3>>;

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
            printf "  Gen %o: degree-%o place in support\n", idx, Degree(P);
            all_ok := false;
            break;
        end if;
        if Valuation(FF1!t1, P) lt 0 or Valuation(u1, P) lt 0 then
            printf "  Gen %o: infinity place\n", idx;
            all_ok := false;
            break;
        end if;
        tv := F9!Evaluate(FF1!t1, P);
        uv := F9!Evaluate(u1, P);
        ft, fu := Explode(<tv^3, uv^3>);
        key := Sprint(<ft, fu>);
        if not IsDefined(lookup1, key) then
            printf "  Gen %o: Frob image (%o,%o) not found\n", idx, ft, fu;
            all_ok := false;
            break;
        end if;
        imgD := imgD + val * (1*lookup1[key]);
    end for;
    if not all_ok then frob1_ok := false; continue; end if;
    img_cls := imgD @@ m1;
    coords := J2Coords(img_cls, j2g1, Cl1);
    if Type(coords) eq BoolElt then
        printf "  Gen %o: Frob image not in J[2]!\n", idx;
        frob1_ok := false;
        continue;
    end if;
    for j in [1..n1] do Frob1[idx][j] := coords[j]; end for;
    printf "  Gen %o -> %o\n", idx, coords;
end for;

if frob1_ok then
    I1 := IdentityMatrix(GF(2), n1);
    fixed1 := NullSpace(Frob1 + I1);
    printf "Frob_3 matrix on J[2](C1/F_9):\n%o\n", Frob1;
    printf "ker(Frob+I) = J[2](C1/F_3): dim = %o\n", Dimension(fixed1);
    printf "Basis: %o\n\n", Basis(fixed1);
end if;

// ======================================================================
// Compute Frob_3 on J[2](C2/F_9) as F_2 matrix
// ======================================================================
print "--- Frobenius_3 on J[2](C2/F_9) ---";

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
            printf "  Gen %o: degree-%o place in support\n", idx, Degree(P);
            all_ok := false;
            break;
        end if;
        if Valuation(FF2!t2, P) lt 0 or Valuation(u2, P) lt 0 then
            printf "  Gen %o: infinity place\n", idx;
            all_ok := false;
            break;
        end if;
        tv := F9!Evaluate(FF2!t2, P);
        uv := F9!Evaluate(u2, P);
        ft := tv^3; fu := uv^3;
        key := Sprint(<ft, fu>);
        if not IsDefined(lookup2, key) then
            printf "  Gen %o: Frob image not found\n", idx;
            all_ok := false;
            break;
        end if;
        imgD := imgD + val * (1*lookup2[key]);
    end for;
    if not all_ok then frob2_ok := false; continue; end if;
    img_cls := imgD @@ m2;
    coords := J2Coords(img_cls, j2g2, Cl2);
    if Type(coords) eq BoolElt then
        printf "  Gen %o: Frob image not in J[2]!\n", idx;
        frob2_ok := false;
        continue;
    end if;
    for j in [1..n2] do Frob2[idx][j] := coords[j]; end for;
    printf "  Gen %o -> %o\n", idx, coords;
end for;

if frob2_ok then
    I2 := IdentityMatrix(GF(2), n2);
    fixed2 := NullSpace(Frob2 + I2);
    printf "Frob_3 matrix on J[2](C2/F_9):\n%o\n", Frob2;
    printf "ker(Frob+I) = J[2](C2/F_3): dim = %o\n", Dimension(fixed2);
    printf "Basis: %o\n\n", Basis(fixed2);
end if;

// ======================================================================
// Compute phi: C1 -> C2 on J[2]
// phi: (t, u) -> (t/zeta_8, u/zeta_8)
// ======================================================================
print "--- Isomorphism phi: J[2](C1/F_9) -> J[2](C2/F_9) ---";
iz8 := 1/z8;

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
            all_ok := false;
            break;
        end if;
        if Valuation(FF1!t1, P) lt 0 or Valuation(u1, P) lt 0 then
            printf "  Gen %o: infinity place\n", idx;
            all_ok := false;
            break;
        end if;
        tv := F9!Evaluate(FF1!t1, P);
        uv := F9!Evaluate(u1, P);
        phi_t := tv * iz8;
        phi_u := uv * iz8;
        key := Sprint(<phi_t, phi_u>);
        if not IsDefined(lookup2, key) then
            printf "  Gen %o: phi image (%o,%o) not found\n", idx, phi_t, phi_u;
            all_ok := false;
            break;
        end if;
        imgD := imgD + val * (1*lookup2[key]);
    end for;
    if not all_ok then phi_ok := false; continue; end if;
    img_cls := imgD @@ m2;
    coords := J2Coords(img_cls, j2g2, Cl2);
    if Type(coords) eq BoolElt then
        printf "  Gen %o: phi image not in J[2]!\n", idx;
        phi_ok := false;
        continue;
    end if;
    for j in [1..n2] do Phi[idx][j] := coords[j]; end for;
    printf "  Gen %o -> %o\n", idx, coords;
end for;

if phi_ok then
    printf "\nPhi matrix (phi_* on J[2]):\n%o\n\n", Phi;
end if;

// ======================================================================
// PART 2: Compare J[2](Q) subspaces
// ======================================================================
print "================================================================";
print "PART 2: COMPARISON OF J[2](Q) SUBSPACES";
print "================================================================";

if frob1_ok and frob2_ok and phi_ok then
    // J[2](C1/F_3) = ker(Frob1 + I)
    // J[2](C2/F_3) = ker(Frob2 + I)
    // Push J[2](C1/F_3) forward via Phi:
    //   Phi(J[2](C1/F_3)) = image of fixed1 under Phi

    printf "dim J[2](C1/F_3) = %o\n", Dimension(fixed1);
    printf "dim J[2](C2/F_3) = %o\n\n", Dimension(fixed2);

    // Image of fixed1 under Phi
    phi_fixed1_basis := [b * Phi : b in Basis(fixed1)];
    phi_fixed1 := sub<VectorSpace(GF(2), n2) | phi_fixed1_basis>;
    printf "Phi(J[2](C1/F_3)) has dim %o\n", Dimension(phi_fixed1);
    printf "Basis: %o\n\n", Basis(phi_fixed1);

    printf "J[2](C2/F_3) has basis: %o\n\n", Basis(fixed2);

    // Check if they're the same subspace
    same := phi_fixed1 eq fixed2;
    printf "*** Phi(J[2](C1/F_3)) = J[2](C2/F_3)? %o ***\n\n", same;

    if not same then
        inter := phi_fixed1 meet fixed2;
        printf "Intersection dim = %o\n", Dimension(inter);
        printf "So the subspaces DIFFER by at least %o dimensions\n",
            Maximum(Dimension(phi_fixed1), Dimension(fixed2)) - Dimension(inter);
    end if;
else
    print "Some matrix computations failed; cannot compare.";
    print "Will try alternative approach at a larger prime.";
end if;

// ======================================================================
// PART 3: Verification at p=5 (zeta_8 in F_25)
// ======================================================================
print "\n================================================================";
print "PART 3: VERIFICATION OVER F_25";
print "================================================================";

F25<b> := GF(25);
z8_25 := PrimitiveElement(F25);
// F_25* has order 24. zeta_8 has order 8, so zeta_8 = g^3 where g = PrimElt
z8_25 := z8_25^3;
assert z8_25^8 eq 1 and z8_25^4 eq F25!(-1);
printf "F_25 = F_5(%o), zeta_8 = %o\n\n", b, z8_25;

// C1 over F_25
K1_25<s1> := FunctionField(F25);
R1_25<V1> := PolynomialRing(K1_25);
GG1<v1> := FunctionField(V1^4 + s1^4 + 1);
CCl1, mm1 := ClassGroup(GG1);
iinv1 := Invariants(CCl1);
jj2g1 := J2Gens(CCl1, iinv1);
printf "C1/F_25: Cl = %o, #J[2] gens = %o\n", iinv1, #jj2g1;

// C2 over F_25
K2_25<s2> := FunctionField(F25);
R2_25<V2> := PolynomialRing(K2_25);
GG2<v2> := FunctionField(V2^4 + s2^4 - 1);
CCl2, mm2 := ClassGroup(GG2);
iinv2 := Invariants(CCl2);
jj2g2 := J2Gens(CCl2, iinv2);
printf "C2/F_25: Cl = %o, #J[2] gens = %o\n", iinv2, #jj2g2;

nn1 := #jj2g1;
nn2 := #jj2g2;

ppls1 := Places(GG1, 1);
ppls2 := Places(GG2, 1);
printf "#deg-1 places: C1 has %o, C2 has %o\n\n", #ppls1, #ppls2;

llookup1 := BuildLookup(ppls1, GG1, s1, v1, F25);
llookup2 := BuildLookup(ppls2, GG2, s2, v2, F25);

// Frob_5 on C1
print "--- Frobenius_5 on J[2](C1/F_25) ---";
FFrob1 := ZeroMatrix(GF(2), nn1, nn1);
ffrob1_ok := true;
for idx in [1..nn1] do
    g := jj2g1[idx];
    D := mm1(g);
    supp := Support(D);
    imgD := DivisorGroup(GG1) ! 0;
    all_ok := true;
    for P in supp do
        val := Valuation(D, P);
        if Degree(P) ne 1 then all_ok := false; break; end if;
        if Valuation(GG1!s1, P) lt 0 or Valuation(v1, P) lt 0 then
            all_ok := false; break;
        end if;
        tv := F25!Evaluate(GG1!s1, P);
        uv := F25!Evaluate(v1, P);
        key := Sprint(<tv^5, uv^5>);
        if not IsDefined(llookup1, key) then all_ok := false; break; end if;
        imgD := imgD + val * (1*llookup1[key]);
    end for;
    if not all_ok then
        printf "  Gen %o: failed\n", idx;
        ffrob1_ok := false;
        continue;
    end if;
    img_cls := imgD @@ mm1;
    coords := J2Coords(img_cls, jj2g1, CCl1);
    if Type(coords) eq BoolElt then ffrob1_ok := false; continue; end if;
    for j in [1..nn1] do FFrob1[idx][j] := coords[j]; end for;
    printf "  Gen %o -> %o\n", idx, coords;
end for;

// Frob_5 on C2
print "--- Frobenius_5 on J[2](C2/F_25) ---";
FFrob2 := ZeroMatrix(GF(2), nn2, nn2);
ffrob2_ok := true;
for idx in [1..nn2] do
    g := jj2g2[idx];
    D := mm2(g);
    supp := Support(D);
    imgD := DivisorGroup(GG2) ! 0;
    all_ok := true;
    for P in supp do
        val := Valuation(D, P);
        if Degree(P) ne 1 then all_ok := false; break; end if;
        if Valuation(GG2!s2, P) lt 0 or Valuation(v2, P) lt 0 then
            all_ok := false; break;
        end if;
        tv := F25!Evaluate(GG2!s2, P);
        uv := F25!Evaluate(v2, P);
        key := Sprint(<tv^5, uv^5>);
        if not IsDefined(llookup2, key) then all_ok := false; break; end if;
        imgD := imgD + val * (1*llookup2[key]);
    end for;
    if not all_ok then
        printf "  Gen %o: failed\n", idx;
        ffrob2_ok := false;
        continue;
    end if;
    img_cls := imgD @@ mm2;
    coords := J2Coords(img_cls, jj2g2, CCl2);
    if Type(coords) eq BoolElt then ffrob2_ok := false; continue; end if;
    for j in [1..nn2] do FFrob2[idx][j] := coords[j]; end for;
    printf "  Gen %o -> %o\n", idx, coords;
end for;

// Phi over F_25
print "--- Phi: J[2](C1/F_25) -> J[2](C2/F_25) ---";
iz8_25 := 1/z8_25;
PPhi := ZeroMatrix(GF(2), nn1, nn2);
pphi_ok := true;
for idx in [1..nn1] do
    g := jj2g1[idx];
    D := mm1(g);
    supp := Support(D);
    imgD := DivisorGroup(GG2) ! 0;
    all_ok := true;
    for P in supp do
        val := Valuation(D, P);
        if Degree(P) ne 1 then all_ok := false; break; end if;
        if Valuation(GG1!s1, P) lt 0 or Valuation(v1, P) lt 0 then
            all_ok := false; break;
        end if;
        tv := F25!Evaluate(GG1!s1, P);
        uv := F25!Evaluate(v1, P);
        key := Sprint(<tv * iz8_25, uv * iz8_25>);
        if not IsDefined(llookup2, key) then all_ok := false; break; end if;
        imgD := imgD + val * (1*llookup2[key]);
    end for;
    if not all_ok then
        printf "  Gen %o: failed\n", idx;
        pphi_ok := false;
        continue;
    end if;
    img_cls := imgD @@ mm2;
    coords := J2Coords(img_cls, jj2g2, CCl2);
    if Type(coords) eq BoolElt then pphi_ok := false; continue; end if;
    for j in [1..nn2] do PPhi[idx][j] := coords[j]; end for;
    printf "  Gen %o -> %o\n", idx, coords;
end for;

if ffrob1_ok and ffrob2_ok and pphi_ok then
    II1 := IdentityMatrix(GF(2), nn1);
    II2 := IdentityMatrix(GF(2), nn2);
    ffixed1 := NullSpace(FFrob1 + II1);
    ffixed2 := NullSpace(FFrob2 + II2);
    printf "\ndim J[2](C1/F_5) = %o\n", Dimension(ffixed1);
    printf "dim J[2](C2/F_5) = %o\n", Dimension(ffixed2);

    pphi_fixed1_basis := [bb * PPhi : bb in Basis(ffixed1)];
    pphi_fixed1 := sub<VectorSpace(GF(2), nn2) | pphi_fixed1_basis>;
    printf "Phi(J[2](C1/F_5)) has dim %o\n", Dimension(pphi_fixed1);

    same5 := pphi_fixed1 eq ffixed2;
    printf "*** Phi(J[2](C1/F_5)) = J[2](C2/F_5)? %o ***\n\n", same5;
end if;

// ======================================================================
// PART 4: Combined conclusion
// ======================================================================
print "================================================================";
print "FINAL CONCLUSION";
print "================================================================";

if frob1_ok and frob2_ok and phi_ok then
    // J[2](Q) = intersection of all J[2](F_p)
    // For C1: J[2](Q) = J[2](F_3) ∩ J[2](F_5) (inside J[2](F_9) and J[2](F_25))
    // But these are in DIFFERENT ambient spaces! We need a common ambient.
    // At p=3: J[2](C1/F_3) inside J[2](C1/F_9)
    // At p=5: J[2](C1/F_5) inside J[2](C1/F_25)
    // These are the SAME J[2] abstractly (as Galois module) but with different bases.
    //
    // If dim J[2](F_3) = 3 = dim J[2](Q), then J[2](F_3) = J[2](Q) already.

    printf "dim J[2](C1/F_3) = %o\n", Dimension(fixed1);
    printf "dim J[2](C2/F_3) = %o\n", Dimension(fixed2);

    d1 := Dimension(fixed1);
    d2 := Dimension(fixed2);

    if d1 eq 3 and d2 eq 3 then
        printf "\nBoth have 3-dim Frob_3-fixed subspaces.\n";
        printf "Since J[2](Q) has dim 3 for C1 (known) and J[2](Q) <= J[2](F_3),\n";
        printf "we get J[2](C1)(Q) = J[2](C1/F_3).\n";
        printf "If J[2](C2)(Q) also has dim 3, same holds for C2.\n\n";
        same := phi_fixed1 eq fixed2;
        if same then
            print "==> The J[2](Q) subspaces MATCH under the isomorphism phi. <==";
        else
            print "==> The J[2](Q) subspaces DO NOT MATCH under phi. <==";
            inter := phi_fixed1 meet fixed2;
            printf "Intersection has dim %o\n", Dimension(inter);
        end if;
    elif d1 gt 3 or d2 gt 3 then
        printf "\nFrob_3-fixed subspace has dim > 3 for at least one curve.\n";
        printf "Need to intersect with Frob_5-fixed to get J[2](Q).\n";
        // This case requires the F_25 data, which uses different basis
        // Need a common basis to do the intersection
        print "(See Part 3 F_25 results for further analysis)";
    end if;
end if;

quit;
