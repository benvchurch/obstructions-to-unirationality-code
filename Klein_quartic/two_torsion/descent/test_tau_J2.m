/*******************************************************************************
 * test_tau_J2.m
 *
 * Test: does the automorphism τ: (x:y:z) -> (x:y:iz) of C2: x^4+y^4-z^4=0
 * act trivially on J[2]?
 *
 * τ is the COCYCLE automorphism for the twist C1 -> C2.
 * We showed τ^2 = (z->-z) acts trivially on J[2].
 * If τ also acts trivially, then J[2](Q) for C1 and C2 are the SAME subspace.
 * If τ acts nontrivially (as an involution), they might DIFFER.
 *
 * In affine (t=x/z, u=y/z): τ sends (t,u) -> (t/i, u/i).
 * Requires i = sqrt(-1) in F_p, so we test at p ≡ 1 mod 4.
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

for p in [5, 13, 17, 29, 37, 41] do
    if p mod 4 ne 1 then continue; end if;
    printf "=== p = %o (p mod 8 = %o) ===\n", p, p mod 8;
    Fp := GF(p);

    // Find i = sqrt(-1) in F_p
    ii := Fp!0;
    for x in Fp do
        if x ne 0 and x^2 eq Fp!(-1) then ii := x; break; end if;
    end for;
    printf "  i = %o (i^2 = %o)\n", ii, ii^2;

    Fpt<tt> := FunctionField(Fp);
    Fptu<uu> := PolynomialRing(Fpt);

    f2 := uu^4 + tt^4 - 1;
    if not IsIrreducible(f2) then
        printf "  f2 reducible, skipping\n\n";
        continue;
    end if;

    FF2<vv> := FunctionField(f2);
    Cl2, mm2 := ClassGroup(FF2);
    invs2 := Invariants(Cl2);
    J2_2 := J2Subgroup(Cl2, invs2);
    printf "  Cl = %o, |J[2]| = %o\n", invs2, #J2_2;

    // Enumerate affine degree-1 places
    pls2 := Places(FF2, 1);
    aff2 := [];
    coord_lookup := AssociativeArray();
    for P in pls2 do
        if Valuation(FF2!tt, P) lt 0 or Valuation(vv, P) lt 0 then continue; end if;
        tv := Fp!Evaluate(FF2!tt, P);
        uv := Fp!Evaluate(vv, P);
        Append(~aff2, P);
        coord_lookup[Sprint(<tv, uv>)] := P;
    end for;
    printf "  Affine deg-1 places: %o\n", #aff2;

    // Build τ map: (t,u) -> (t/i, u/i) = (t*(-i), u*(-i))
    inv_i := Fp!(1/ii);  // 1/i = -i
    tau_map := AssociativeArray();
    for P in aff2 do
        tv := Fp!Evaluate(FF2!tt, P);
        uv := Fp!Evaluate(vv, P);
        target := <tv * inv_i, uv * inv_i>;
        key := Sprint(target);
        if IsDefined(coord_lookup, key) then
            tau_map[P] := coord_lookup[key];
        end if;
    end for;
    printf "  τ maps %o/%o affine places\n", #Keys(tau_map), #aff2;

    // Also build τ^2 map (= negation) for comparison
    neg_map := AssociativeArray();
    for P in aff2 do
        tv := Fp!Evaluate(FF2!tt, P);
        uv := Fp!Evaluate(vv, P);
        key := Sprint(<-tv, -uv>);
        if IsDefined(coord_lookup, key) then
            neg_map[P] := coord_lookup[key];
        end if;
    end for;

    // Test τ on each J[2] element
    tau_trivial := true;
    tested := 0;
    failed := 0;
    nontrivial_list := [];
    for g in J2_2 do
        if g eq Cl2!0 then continue; end if;
        D := mm2(g);
        supp := Support(D);

        // Try τ
        tauD := DivisorGroup(FF2) ! 0;
        ok := true;
        for P in supp do
            n := Valuation(D, P);
            if Degree(P) ne 1 or not IsDefined(tau_map, P) then
                ok := false; break;
            end if;
            tauD := tauD + n * (1*tau_map[P]);
        end for;

        if ok then
            tau_g := tauD @@ mm2;
            tested +:= 1;
            if tau_g ne g then
                tau_trivial := false;
                Append(~nontrivial_list, <g, tau_g>);
            end if;
        else
            failed +:= 1;
        end if;
    end for;

    printf "  Tested: %o, Failed: %o\n", tested, failed;
    if tested eq 0 then
        printf "  Could not test any elements\n";
    elif tau_trivial then
        printf "  τ acts TRIVIALLY on all tested J[2] elements\n";
        printf "  => CONCLUSION: J[2](Q) subspaces are the SAME\n";
    else
        printf "  τ acts NONTRIVIALLY on J[2]!\n";
        for pair in nontrivial_list do
            printf "    %o -> %o\n", pair[1], pair[2];
        end for;
        // τ^2 = negation acts trivially (already verified), so τ is an involution
        printf "  => τ is a NONTRIVIAL involution on J[2]\n";
        printf "  => J[2](Q) subspaces might DIFFER\n";
    end if;
    printf "\n";
end for;

quit;
