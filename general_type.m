load "invariants.m";

// ---------------------------------------------------------------------------
// Run over all pairs of sequences of elements of G whose product is 1,
// and compute K2([seq1, seq2], G) for each pair.
//
// WARNING: number of sequences of length n is |G|^(n-1), so pairs are
// |G|^(n1+n2-2). This explodes quickly.
// ---------------------------------------------------------------------------

// Return all sequences of length n with product equal to identity in G.
// We choose the first n-1 entries arbitrarily and solve for the last entry.
AllSeqsProductOne := function(G, n : include_identity := true)
    if n lt 1 then
        error "error: n must be >= 1";
    end if;

    elems := [g : g in G];
    if not include_identity then
        elems := [g : g in elems | g ne Id(G)];
    end if;

    if n eq 1 then
        return [PowerSequence(G) | [Id(G)]];
    end if;

    seqs := [PowerSequence(G) | ];

    procedure rec(prefix, prod, ~seqs)
        if #prefix eq n - 1 then
            last := prod^(-1);
            if include_identity or last ne Id(G) then
                Append(~seqs, prefix cat [PowerSequence(G) | last]);
            end if;
            return;
        end if;

        for g in elems do
            new_prefix := prefix;
            Append(~new_prefix, g);
            rec(new_prefix, prod * g, ~seqs);
        end for;
    end procedure;

    rec([PowerSequence(G) | ], Id(G), ~seqs);
    return seqs;
end function;

// ---------------------------------------------------------------------------
// Helpers to identify sequences up to cyclic permutation and overall conjugation
// ---------------------------------------------------------------------------

// Compare two sequences lexicographically via indices in elems.
LessSeq := function(seqA, seqB, elems)
    for i in [1..#seqA] do
        ia := Position(elems, seqA[i]);
        ib := Position(elems, seqB[i]);
        if ia lt ib then
            return true;
        elif ia gt ib then
            return false;
        end if;
    end for;
    return false;
end function;

// Canonical representative of a sequence under cyclic shifts and overall conjugation.
CanonicalRepSeq := function(G, seq, elems)
    n := #seq;
    best := [];
    first := true;

    for shift in [0..n-1] do
        rot := [ seq[((i + shift - 1) mod n) + 1] : i in [1..n] ];
        for g in elems do
            conj := [ g * h * g^-1 : h in rot ];
            if first then
                best := conj;
                first := false;
            elif LessSeq(conj, best, elems) then
                best := conj;
            end if;
        end for;
    end for;

    return best;
end function;

KeyForPair := function(seq1, seq2, elems)
    idxs := [ Position(elems, g) : g in seq1 cat seq2 ];
    return Sprint(idxs);
end function;

// Define record format for storing sequence pairs and K2 values
PairK2Record := recformat<
    seq1: SeqEnum,
    seq2: SeqEnum,
    K2: FldRatElt
>;

// Iterate over all pairs (seq1, seq2) with product 1 and compute K2.
// Returns a list of records with fields `seq1`, `seq2`, `K2`.
// If only_negative is true, we keep only those with K2 < 0.
AllPairsSeqsProductOneK2 := function(G, n1, n2 : include_identity := true, print_every := 0, only_negative := false)
    seqs1 := AllSeqsProductOne(G, n1 : include_identity := include_identity);
    seqs2 := AllSeqsProductOne(G, n2 : include_identity := include_identity);

    elems := [g : g in G];
    seen := AssociativeArray(MonStgElt);

    results := [];
    ctr := 0;
    for s1 in seqs1 do
        for s2 in seqs2 do
            ctr +:= 1;
            if print_every gt 0 and (ctr mod print_every) eq 0 then
                print "Processed pairs:", ctr;
            end if;

            // Reduce each sequence up to cyclic permutation and conjugation.
            can1 := CanonicalRepSeq(G, s1, elems);
            can2 := CanonicalRepSeq(G, s2, elems);
            key := KeyForPair(can1, can2, elems);

            // Skip if we have already seen an equivalent pair.
            if IsDefined(seen, key) then
                continue;
            end if;
            seen[key] := true;

            k2val := K2([s1, s2], G);
            if (not only_negative) or k2val lt 0 then
                Append(~results, rec<PairK2Record |
                    seq1 := s1,
                    seq2 := s2,
                    K2 := k2val
                >);
            end if;
        end for;
    end for;

    return results;
end function;

// -----------------------
// Parameters + run
// -----------------------

G := CyclicGroup(3);
n1 := 3;
n2 := 3;

// Collect only those pairs with K2 < 0
results := AllPairsSeqsProductOneK2(G, n1, n2 : include_identity := true, print_every := 1000, only_negative := true);
print "#pairs with K2 < 0 =", #results;

// Example: print the first few negative K2 values and their sequences
for i in [1..Minimum(10, #results)] do
    print "index:", i;
    print "seq1:", results[i]`seq1;
    print "seq2:", results[i]`seq2;
    print "K2:", results[i]`K2;
end for;