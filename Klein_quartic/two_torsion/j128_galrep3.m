/*******************************************************************************
 * j128_galrep3.m
 *
 * Find the image of Gal -> GL_2(Z/16) for E = 3200j1 (j=128).
 *
 * LMFDB: 2-adic image = 8.2.0.a.1 (level 8, index 2).
 * Strategy: enumerate all index-2 (= normal) subgroups of GL_2(Z/8),
 * find the one matching the Frobenius (trace, det) mod 8 data.
 * Then lift to mod 16.
 ******************************************************************************/

SetColumns(0);

QQ := Rationals();
E := MinimalModel(EllipticCurveWithjInvariant(QQ!128));
N_E := Conductor(E);
printf "E = 3200j1, j=128, conductor %o\n\n", N_E;

// Step 1: Collect observed (tr, det) mod 8 from Frobenius
printf "Collecting Frobenius data...\n";
observed_8 := {};
for q in PrimesInInterval(5, 50000) do
    if N_E mod q eq 0 then continue; end if;
    aq := TraceOfFrobenius(E, q);
    t := aq mod 8; if t lt 0 then t +:= 8; end if;
    d := q mod 8;
    Include(~observed_8, <t, d>);
end for;
printf "Observed (tr, det) mod 8: %o pairs\n", #observed_8;
for d in [1,3,5,7] do
    traces := Sort(Setseq({p[1] : p in observed_8 | p[2] eq d}));
    printf "  det=%o: traces = %o\n", d, traces;
end for;

observed_16 := {};
for q in PrimesInInterval(5, 50000) do
    if N_E mod q eq 0 then continue; end if;
    aq := TraceOfFrobenius(E, q);
    t := aq mod 16; if t lt 0 then t +:= 16; end if;
    d := q mod 16;
    Include(~observed_16, <t, d>);
end for;
printf "\nObserved (tr, det) mod 16: %o pairs\n", #observed_16;

// Step 2: Enumerate all index-2 subgroups of GL_2(Z/8)
R8 := Integers(8);
G8 := GL(2, R8);
printf "\n|GL_2(Z/8)| = %o\n", #G8;

// Index-2 subgroups = kernels of homomorphisms to Z/2
// = normal subgroups of index 2
// Number = number of elements of order 2 in G8^ab - 1
A8, phi8 := AbelianQuotient(G8);
printf "Abelianization of GL_2(Z/8): %o\n", A8;

// Find all index-2 subgroups
idx2_subs := NormalSubgroups(G8 : OrderEqual := #G8 div 2);
printf "Number of index-2 normal subgroups: %o\n", #idx2_subs;

// Step 3: Find which one matches the Frobenius data
printf "\nMatching against Frobenius data...\n";
for i in [1..#idx2_subs] do
    H := idx2_subs[i]`subgroup;
    // Compute (tr, det) mod 8 pairs
    H_td := {};
    for g in H do
        t := Integers()!Trace(g);
        d := Integers()!Determinant(g);
        Include(~H_td, <t, d>);
    end for;

    // Check if observed is a subset
    if observed_8 subset H_td then
        extra := H_td diff observed_8;
        printf "\n  Subgroup #%o: |H|=%o, matches observed data\n", i, #H;
        printf "  %o (tr,det) pairs in H, %o observed, %o extra\n",
            #H_td, #observed_8, #extra;
        if #extra gt 0 then
            printf "  Extra: %o\n", Sort(Setseq(extra));
        end if;
        if H_td eq observed_8 then
            printf "  *** EXACT MATCH ***\n";
        end if;

        // This is our candidate.  Lift to mod 16.
        printf "\n  Lifting to GL_2(Z/16)...\n";
        R16 := Integers(16);
        G16 := GL(2, R16);

        // Lift generators of H to GL_2(Z/16) and add kernel generators
        H_gens_16 := [G16!Eltseq(g) : g in Generators(H)];
        ker_gens := [
            G16![1+8, 0, 0, 1],
            G16![1, 8, 0, 1],
            G16![1, 0, 8, 1],
            G16![1, 0, 0, 1+8]
        ];
        H16 := sub<G16 | H_gens_16 cat ker_gens>;
        printf "  |H16| = %o (index %o in GL_2(Z/16))\n", #H16, #G16 div #H16;

        // Compute (tr, det) mod 16 pairs
        H16_td := {};
        H16_trace_by_det := AssociativeArray();
        for d in [0..15] do H16_trace_by_det[d] := {}; end for;
        for g in H16 do
            t := Integers()!Trace(g);
            d := Integers()!Determinant(g);
            Include(~H16_td, <t, d>);
            Include(~H16_trace_by_det[d], t);
        end for;
        printf "  %o (tr,det) pairs mod 16\n", #H16_td;

        // Check consistency with observed mod 16
        if observed_16 subset H16_td then
            printf "  All observed mod-16 pairs are in H16: YES\n";
            extra16 := H16_td diff observed_16;
            printf "  Extra mod-16 pairs: %o\n", #extra16;
        else
            missing16 := observed_16 diff H16_td;
            printf "  MISMATCH: %o observed pairs NOT in H16\n", #missing16;
        end if;

        // THE KEY: trace = 0 analysis
        printf "\n  === TRACE = 0 MOD 16 ANALYSIS ===\n";
        trace0_dets := {};
        trace0_count := 0;
        for g in H16 do
            if Trace(g) eq R16!0 then
                trace0_count +:= 1;
                Include(~trace0_dets, Integers()!Determinant(g));
            end if;
        end for;
        printf "  Elements with trace = 0: %o / %o\n", trace0_count, #H16;
        printf "  Det values for trace = 0: %o\n", Sort(Setseq(trace0_dets));

        if trace0_dets eq {15} then
            printf "\n  *** VERIFIED: trace = 0 mod 16  ==>  det = 15 mod 16 ***\n";
        else
            printf "\n  trace = 0 does NOT force det = 15 in this lift.\n";
            printf "  Need to check if level is really 8...\n";
        end if;

        // Full table
        printf "\n  Full (tr,det) count matrix mod 16:\n";
        printf "       ";
        for d in [1,3,5,7,9,11,13,15] do printf "%5o", d; end for;
        printf "\n";
        for t in [0..15] do
            printf "  t=%2o:", t;
            for d in [1,3,5,7,9,11,13,15] do
                if <t,d> in H16_td then
                    ct := #{g : g in H16 | Trace(g) eq R16!t
                        and Determinant(g) eq R16!d};
                    printf "%5o", ct;
                else
                    printf "    .";
                end if;
            end for;
            printf "\n";
        end for;

        // Check det -> traces
        printf "\n  det mod 16 -> traces mod 16:\n";
        for d in [1,3,5,7,9,11,13,15] do
            printf "    det=%o: %o\n", d, Sort(Setseq(H16_trace_by_det[d]));
        end for;
    end if;
end for;

quit;
