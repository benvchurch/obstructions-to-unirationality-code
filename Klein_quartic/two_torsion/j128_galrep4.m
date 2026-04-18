/*******************************************************************************
 * j128_galrep4.m
 *
 * Find the exact image mod 16 by taking the intersection of the mod-8 lift
 * with the set of matrices having observed (tr, det) pairs.
 ******************************************************************************/

SetColumns(0);

QQ := Rationals();
E := MinimalModel(EllipticCurveWithjInvariant(QQ!128));
N_E := Conductor(E);

// Observed (tr, det) mod 16 from Frobenius up to 50000
observed_16 := {};
for q in PrimesInInterval(5, 50000) do
    if N_E mod q eq 0 then continue; end if;
    aq := TraceOfFrobenius(E, q);
    t := aq mod 16; if t lt 0 then t +:= 16; end if;
    d := q mod 16;
    Include(~observed_16, <t, d>);
end for;
printf "Observed (tr, det) mod 16: %o pairs\n", #observed_16;

R16 := Integers(16);
G16 := GL(2, R16);
R8 := Integers(8);
G8 := GL(2, R8);

// Find the matching index-2 subgroup mod 8 (we know there are 2 candidates)
// Use #3 and #5 from previous run; try both
idx2_subs := NormalSubgroups(G8 : OrderEqual := #G8 div 2);

observed_8 := {<p[1] mod 8, p[2] mod 8> : p in observed_16};

for sub_idx in [1..#idx2_subs] do
    H8 := idx2_subs[sub_idx]`subgroup;
    H8_td := {<Integers()!Trace(g), Integers()!Determinant(g)> : g in H8};
    if not (observed_8 subset H8_td) then continue; end if;

    printf "\n=== Trying index-2 subgroup #%o ===\n", sub_idx;

    // Lift to mod 16
    H8_gens_16 := [G16!Eltseq(g) : g in Generators(H8)];
    ker_gens := [
        G16![1+8, 0, 0, 1], G16![1, 8, 0, 1],
        G16![1, 0, 8, 1], G16![1, 0, 0, 1+8]
    ];
    H16_full := sub<G16 | H8_gens_16 cat ker_gens>;
    printf "|H16_full| = %o\n", #H16_full;

    // Collect all elements with observed (tr, det) pairs
    valid_elts := [g : g in H16_full |
        <Integers()!Trace(g), Integers()!Determinant(g)> in observed_16];
    printf "Elements with observed (tr,det): %o / %o\n", #valid_elts, #H16_full;

    // Check if these form a subgroup
    printf "Checking closure...\n";
    valid_set := Set(valid_elts);

    // Quick check: is the identity in the set?
    id_in := G16!1 in valid_set;
    printf "  Identity in set: %o\n", id_in;

    // Generate the subgroup from these elements
    // This is potentially expensive with many generators, so use a subset
    // Actually, let's try: generate from a small random subset and check
    H16_exact := sub<G16 | valid_elts[1..Minimum(50, #valid_elts)]>;
    printf "  From 50 generators: |H| = %o\n", #H16_exact;

    // If too small, add more
    if #H16_exact lt #valid_elts then
        // Add more generators
        for i in [51..#valid_elts by 100] do
            H16_exact := sub<G16 | H16_exact, valid_elts[i]>;
        end for;
        printf "  After adding more: |H| = %o\n", #H16_exact;
    end if;

    // Check if the generated group is contained in valid_set
    extra_elts := [g : g in H16_exact | g notin valid_set];
    if #extra_elts eq 0 then
        printf "  Generated group ⊆ valid set: YES\n";
        printf "  |generated group| = %o = |valid set|: %o\n",
            #H16_exact, #H16_exact eq #valid_elts;
        if #H16_exact eq #valid_elts then
            printf "  *** EXACT IMAGE FOUND: valid set IS a subgroup ***\n";
        end if;
    else
        printf "  Generated group has %o extra elements\n", #extra_elts;
        printf "  Valid set is NOT closed under multiplication.\n";
        printf "  The true image is smaller than the valid set.\n";

        // Try normal subgroups of H16_full contained in valid_set
        printf "\n  Looking for normal subgroups...\n";
        // Check the generated group's (tr, det) pairs
        gen_td := {<Integers()!Trace(g), Integers()!Determinant(g)> : g in H16_exact};
        extra_td := gen_td diff observed_16;
        printf "  Extra (tr,det) in generated group: %o\n", #extra_td;
        if #extra_td gt 0 and #extra_td le 10 then
            printf "    %o\n", Sort(Setseq(extra_td));
        end if;
    end if;

    // Regardless, check the KEY PROPERTY on the generated group
    printf "\n  === KEY: trace = 0 mod 16 in generated group ===\n";
    trace0_dets := {};
    for g in H16_exact do
        if Trace(g) eq R16!0 then
            Include(~trace0_dets, Integers()!Determinant(g));
        end if;
    end for;
    printf "  Det values for trace=0: %o\n", Sort(Setseq(trace0_dets));
    if trace0_dets eq {15} then
        printf "  *** VERIFIED: trace=0 mod 16 ==> det=15 mod 16 ***\n";
    end if;

    // Also check on valid_set directly (without subgroup closure)
    printf "\n  === KEY: trace = 0 mod 16 in valid set (direct check) ===\n";
    trace0_dets_v := {};
    for g in valid_elts do
        if Trace(g) eq R16!0 then
            Include(~trace0_dets_v, Integers()!Determinant(g));
        end if;
    end for;
    printf "  Det values for trace=0: %o\n", Sort(Setseq(trace0_dets_v));
end for;

quit;
