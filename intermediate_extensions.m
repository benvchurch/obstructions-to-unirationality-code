// Functions for computing properties of intermediate field extensions

import "group_reps.m": SphGensUptoConj, SphGensUptoAut, SphGensUptoHurwitz;


getRam := function(cycle)
    str := CycleStructure(cycle);
    ram := 0;
    for p in str do
        ram := ram + (p[1]-1)*p[2];
    end for;
    return ram;
end function;

GenusIntermediateExtension := function(G, seq, H)
    action := CosetAction(G, H);
    ram := &+([getRam(action(g)) : g in seq ]);
    genus := (Order(G) / Order(H) * (-2) + ram)/2 + 1;
    return genus;
end function;

Genus := function(G, seq)
    H := sub<G | Id(G)>;
    return GenusIntermediateExtension(G, seq, H);
end function;

// Given X -> X/G computes the monodromy of X -> X/H and X/H -> X / G, H_seq is the monodromy of X -> X/H as elements of H, G_seq is the permutation action of G on X/H
// only works for intermediate genus 0
IntermediateMonodromy := function(G, seq, H) // G is the group, seq is the sequence of elements, H is the subgroup
    if not GenusIntermediateExtension(G, seq, H) eq 0 then
        error "Only works for intermediate genus 0";
    end if;
    action, pi, S := CosetAction(G, H);
    G_seq := [action(g) : g in seq];
    transversal := RightTransversal(G, H);  // Get coset representatives
    H_seq_conj := [];
    for g in seq do
        perm := action(g);
        cycles := CycleDecomposition(perm);
        for cyc in cycles do
            k := #cyc;
            // Pick first element of cycle as representative
            coset_idx := cyc[1];
            t_i := transversal[coset_idx];
            // Compute h = t_i^-1 * g^k * t_i
            h := t_i * g^k * t_i^(-1);
            Append(~H_seq_conj, H ! h);
        end for;
    end for;
    H_seq_conj := [H ! h : h in H_seq_conj];
    H_seq_conj := [h : h in H_seq_conj | h ne Id(H)];
    cl := ClassMap(H);
    [cl(h) : h in H_seq_conj];
    reps := SphGensUptoConj(H, H_seq_conj : UseElements := true);
    reps := SetToSequence(reps);
    
    if not (&* G_seq) eq Id(pi) then
        error "G_seq is not spherical";
    end if;
    for H_seq in reps do
        if not (&* H_seq) eq Id(H) then
            error "H_seq is not spherical";
        end if;
        if not sub<H | H_seq> eq H then
            error "H_seq does not generate H";
        end if;
    end for;
    return reps, G_seq;
end function;

IntermediateMonodromyTake2 := function(G, seq, H) // G is the group, seq is the sequence of elements, H is the subgroup
    if not GenusIntermediateExtension(G, seq, H) eq 0 then
        error "Only works for intermediate genus 0";
    end if;
    action, pi, S := CosetAction(G, H);
    transversal := RightTransversal(G, H);  // Get coset representatives
    G_seq := [action(g) : g in seq];
    F := FreeGroup(#seq-1);
    f := hom<F -> G | [seq[i] : i in [1..#seq-1]]>;
    K := H @@ f;
    gens := FreeGenerators(K);
    K_seq_conj := [];
    F_seq := [F.i : i in [1..#seq-1]];
    Append(~F_seq, (&* F_seq)^(-1));
    for i in [1..#seq] do
        perm := action(seq[i]);
        cycles := CycleDecomposition(perm);
        for cyc in cycles do
            k := #cyc;
            // Pick first element of cycle as representative
            coset_idx := cyc[1];
            coset_idx;
            t_i := transversal[coset_idx] @@ f;
            t_i;
            // Compute h = t_i^-1 * g^k * t_i
            h := t_i * (F_seq[i])^k * t_i^(-1);
            Append(~K_seq_conj, K ! h);
        end for;
    end for;
    K_seq_conj;
    sub< K | K_seq_conj > eq K;
    H_seq := [H ! f(k) : k in gens];
    Append(~H_seq, (&* H_seq)^(-1));
    return H_seq, G_seq;
end function;

// Given an extension H < HL of subgroups of G computes the HL/H - monodromy of X/H -> X/HL 
// over the points determined by the monodromy of X/HL -> X/G
GetMonodromyIntermediateExtension := function(G, seq, H, HL)    
    HL_seq, G_HL_seq := IntermediateMonodromy(G, seq, HL);
    H_seq, G_H_seq := IntermediateMonodromy(G, seq, H);
    H := sub<HL | [HL ! g : g in Generators(H)]>;
    action := CosetAction(HL, H);
    HL_H_seq := [action(h) : h in H_seq];
    return HL_H_seq, G_HL_seq;
end function; 