/*******************************************************************************
 * test_involution_J2.m
 *
 * Test: does the involution (t,u) -> (-t,-u) [i.e., (x:y:z)->(x:y:-z)]
 * act trivially on J[2](C2) over F_p?
 *
 * If YES: the twist cocycle acts trivially on J[2], so J[2](Q) subspaces
 * are the SAME under the isomorphism phi: C1 -> C2.
 *
 * We test at multiple primes for robustness.
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

for p in [3, 5, 7, 11, 13, 17, 19] do
    printf "=== p = %o (p mod 8 = %o) ===\n", p, p mod 8;
    Fp := GF(p);
    Fpt<tt> := FunctionField(Fp);
    Fptu<uu> := PolynomialRing(Fpt);

    f2 := uu^4 + tt^4 - 1;
    if not IsIrreducible(f2) then
        printf "  f2 reducible over F_%o, skipping\n\n", p;
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

    // Build involution map: (t,u) -> (-t,-u)
    inv_map := AssociativeArray();
    for P in aff2 do
        tv := Fp!Evaluate(FF2!tt, P);
        uv := Fp!Evaluate(vv, P);
        key := Sprint(<-tv, -uv>);
        if IsDefined(coord_lookup, key) then
            inv_map[P] := coord_lookup[key];
        end if;
    end for;
    printf "  Involution maps %o/%o affine places\n", #Keys(inv_map), #aff2;

    // Test involution on each J[2] element
    inv_trivial := true;
    tested := 0;
    failed := 0;
    for g in J2_2 do
        if g eq Cl2!0 then continue; end if;
        D := mm2(g);
        supp := Support(D);
        invD := DivisorGroup(FF2) ! 0;
        ok := true;
        for P in supp do
            n := Valuation(D, P);
            if Degree(P) ne 1 then
                ok := false; break;
            end if;
            // Check if P is affine
            if not IsDefined(inv_map, P) then
                // P might be at infinity or not in our affine chart
                ok := false; break;
            end if;
            invD := invD + n * (1*inv_map[P]);
        end for;

        if ok then
            inv_g := invD @@ mm2;
            tested +:= 1;
            if inv_g ne g then
                printf "  NONTRIVIAL: %o -> %o\n", g, inv_g;
                inv_trivial := false;
            end if;
        else
            failed +:= 1;
        end if;
    end for;

    printf "  Tested: %o, Failed: %o (non-deg-1 in divisor)\n", tested, failed;
    if tested eq 0 then
        printf "  Could not test any elements (all have non-deg-1 places)\n";
    elif inv_trivial then
        printf "  z->-z acts TRIVIALLY on all tested J[2] elements\n";
    else
        printf "  z->-z acts NONTRIVIALLY on J[2]\n";
    end if;
    printf "\n";
end for;

quit;
