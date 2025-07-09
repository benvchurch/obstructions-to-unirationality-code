load "invariants.m";
import "intermediate_extensions.m": Genus, GenusIntermediateExtension, IntermediateMonodromy, IntermediateMonodromyTake2;

import "group_reps.m" : FindBelyiCurve, SphGensUptoConj;

// Hurwitz curve of genus 14
G := PSL(2, 13); 

// get the data of the three Galois oribts of curves 
repsA := SphGensUptoConj(G, [2,3,5]);
repsB := SphGensUptoConj(G, [2,3,6]);
repsC := SphGensUptoConj(G, [2,3,7]);

allreps := [r : r in repsA] cat [r : r in repsB] cat [r : r in repsC];

subgroup_indices := [10,13,14]; // these are the subgroups, up to conjugacy, that we consider in Theorem A

fail := false;


// fundamental group tests:

for i in subgroup_indices do
    H := (Subgroups(G)[i])`subgroup; // a different choice of representative for the conjugacy class of H will replace these elements with overall conjugates 

    rep := allreps[1];
    H_seqs, G_seq := IntermediateMonodromy(G, rep, H); // this comutes the sequence of monodromy for the subgroup H
    for H_seq in H_seqs do
        
            OrderPi1 := Order(Pi1_v2([H_seq, H_seq], H));
            print "Order of Pi1: ", OrderPi1;
            if OrderPi1 ne 1 then
                print "FAIL: Pi1 is non-trivial";
                        fail := true;
            end if; 
        print "--------------------------------";
    end for;
end for;
// DIAGONAL NUMBER TESTS:

for i in subgroup_indices do
    H := (Subgroups(G)[i])`subgroup; // a different choice of representative for the conjugacy class of H will replace these elements with overall conjugates 

    for rep1 in allreps do
        for rep2 in allreps do // here form all pairs of products of the G-Belyi curves considered up to isomorphism of G-covers
            H_seqs1, G_seq1 := IntermediateMonodromy(G, rep1, H); // this comutes the sequence of monodromy for C -> C/H and C/H -> C/G
            H_seqs2, G_seq2 := IntermediateMonodromy(G, rep2, H); 
            H_seq1 := H_seqs1[1]; // different sets of spherical generators with the same conjugacy classes do not change the baseket of singularities which is what is relevant for computing intesection  numbers
            H_seq2 := H_seqs2[1]; 
            
            diag := DiagonalFormNumber([H_seq1, H_seq2], H); // compute the intersection number (K_X - E)^2
            print "Diagonal form number: ", diag;
            if diag le 0 then
                print "FAIL: diagonal form is not positive";
                fail := true;
            end if;
            print "--------------------------------";
        end for;
    end for;

end for;


print "OVERALL FAILURE?: ", fail;