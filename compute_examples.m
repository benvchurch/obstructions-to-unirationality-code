load "invariants.m";
import "intermediate_extensions.m": Genus, GenusIntermediateExtension, IntermediateMonodromy, IntermediateMonodromyTake2;

runCyclic := function(a,b)
// Get primes in range [10..20]
primes := [n : n in [a..b] | IsPrime(n)];

for n in primes do
    G := CyclicGroup(n);
    for p in primes do
        if p eq n then continue; end if;
        for q in primes do
            if q eq n or q eq p then continue; end if;
            seq1 := [ G.1 : i in [1..p] ];
            seq1 := Append(seq1, G.1^(n-p));
            seq2 := [ G.1 : i in [1..q] ];
            seq2 := Append(seq2, G.1^(n-q));
            
            if findData(G, seq1, seq2) then
                print p,q,n;
                runData(G, seq1, seq2);
            end if;
        end for;
    end for;
end for;
end function; 

analyze_sub_curves := function(G, seq1, seq2)
    for rec in Subgroups(G) do
      H := rec`subgroup;
      print H;
      action := CosetAction(G,H);
      print "Order: ", Order(H), " Genus: ", (ChiCurvePermutation(action, seq1, Order(G)/Order(H)) + 2)/2, (ChiCurvePermutation(action, seq2, Order(G)/Order(H)) + 2)/2;
    end for;
    return "";
end function;


function run_over_subgroups(G, seq)
    subgroups := [Subgroups(G)[i]`subgroup : i in [1..#Subgroups(G)]];
    for i in [1..#subgroups] do
        H := subgroups[i];
        if GenusIntermediateExtension(G, seq, H) eq 0 then
            H_seq, G_seq := IntermediateMonodromy(G, seq, H);

            Hsub := sub<G | H_seq>;
            H_seq := [Hsub !h : h in H_seq | h ne Id(G)];
            print i, H_seq;

            print "Group order: ", Order(H);
            runData(Hsub, H_seq, H_seq);
        end if;
    end for;
end function;

import "group_reps.m" : FindBelyiCurve, SphGensUptoConj;

// Hurwitz curve of genus 14
G := SmallGroups(1092)[25];
H := (Subgroups(G)[14])`subgroup; // good subgroups 10,13,14

repsA := SphGensUptoConj(G, [2,3,5]);
repsB := SphGensUptoConj(G, [2,3,6]);
repsC := SphGensUptoConj(G, [2,3,7]);

reps := [r : r in repsA] cat [r : r in repsB] cat [r : r in repsC];

for rep1 in reps do
    for rep2 in reps do
        H_seq1, G_seq1 := IntermediateMonodromy(G, rep1, H);
        H_seq2, G_seq2 := IntermediateMonodromy(G, rep2, H);
        runData(H, H_seq1[1], H_seq2[1]);
    end for;
end for;


if false then

GenusIntermediateExtension(G, seq, H);
Genus(H, H_seq);
Genus(H, [h : h in H_seq | h ne Id(H)]);


reps, G_seq := IntermediateMonodromy(G, seq, H);
# reps;

// 	Fricke-Macbeath curve

// all quotients by subgroups simply connected, except 8, but not enough symemetric forms.

// Interesting note, for 11,12 it looks like they are not general type. I wonder if this usually happens for lots of automorphisms (also happens for the full group in Hurwitz example 14).


G := SmallGroup(504,156);
seq := FindBelyiCurve(G, [2,3,4], 7);

H := (Subgroups(G)[6])`subgroup; // genus zero subgroups: 6, 8,9,10,11,12;
H_seq, G_seq := IntermediateMonodromy(G, seq, H);

runData(H, H_seq[1], H_seq[1]);


// Accola-Maclachlan curve of genus 15

G := SmallGroup(128,150);
seq := [ G.2, G.1 * G.6, G.1 * G.2 * G.4 * G.6 ];
subgroups := [Subgroups(G)[i]`subgroup : i in [1..#Subgroups(G)]];

H_seq, G_seq := IntermediateMonodromy(G, seq, subgroups[18]);

Hsub := sub<G | H_seq>;
H_seq := [Hsub ! h : h in H_seq | h ne Id(G)];
print H_seq;

print "Group order: ", Order(Hsub);
runData(Hsub, H_seq, H_seq);


// Accola-Maclachlan curve of genus 13

S := SymmetricGroup(112);

seq := [
S! (1,71) (2,77) (3,76) (4,75) (5,74) (6,73) (7,72) (8,78) (9,84) (10,83) (11,82) (12,81) (13,80) (14,79) (15,57) (16,63) (17,62) (18,61) (19,60) (20,59) (21,58) (22,64) (23,70) (24,69) (25,68) (26,67) (27,66) (28,65) (29,106) (30,112) (31,111) (32,110) (33,109) (34,108) (35,107) (36,99) (37,105) (38,104) (39,103) (40,102) (41,101) (42,100) (43,92) (44,98) (45,97) (46,96) (47,95) (48,94) (49,93) (50,85) (51,91) (52,90) (53,89) (54,88) (55,87) (56,86),
S!	(1,108,22,87) (2,107,23,86) (3,106,24,85) (4,112,25,91) (5,111,26,90) (6,110,27,89) (7,109,28,88) (8,101,15,94) (9,100,16,93) (10,99,17,92) (11,105,18,98) (12,104,19,97) (13,103,20,96) (14,102,21,95) (29,59,50,80) (30,58,51,79) (31,57,52,78) (32,63,53,84) (33,62,54,83) (34,61,55,82) (35,60,56,81) (36,66,43,73) (37,65,44,72) (38,64,45,71) (39,70,46,77) (40,69,47,76) (41,68,48,75) (42,67,49,74),
S!	(1,55,18,37,7,54,17,36,6,53,16,42,5,52,15,41,4,51,21,40,3,50,20,39,2,56,19,38) (8,48,25,30,14,47,24,29,13,46,23,35,12,45,22,34,11,44,28,33,10,43,27,32,9,49,26,31) (57,111,74,93,63,110,73,92,62,109,72,98,61,108,71,97,60,107,77,96,59,106,76,95,58,112,75,94) (64,104,81,86,70,103,80,85,69,102,79,91,68,101,78,90,67,100,84,89,66,99,83,88,65,105,82,87)
];

G := sub<S | seq>;
run_over_subgroups(G, seq);


// Max automorphisms for genus 13

G := SmallGroups(360)[121];
seq := [
    G ! (1, 2)(4, 8)(5, 6),
    G ! (1, 2, 3)(4, 5, 7),
    G ! (1, 3)(4, 7, 6, 5, 8)
];

H := (Subgroups(G)[27])`subgroup;
H_seq, G_seq := IntermediateMonodromy(G, seq, H);

H := sub<G | H_seq>;
seq := [h : h in H_seq | h ne Id(H)];
print seq;

print "Order: ", Order(H);
runData(H, seq, seq);

// Max auts for genus 10
G := SmallGroups(432)[734];
seq := [ G.1, G.2 * G.3 * G.7, G.1 * G.2 * G.4 * G.5 * G.6 * G.7 ];
H := (Subgroups(G)[35])`subgroup;

action, pi, S := CosetAction(G, H);
transversal := RightTransversal(G, H);  // Get coset representatives
H_seq := [];
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
        Append(~H_seq, h);
    end for;
end for;

H := sub<G | H_seq>;
seq := [H ! h];
seq := [h : h in H_seq | h ne Id(H)];
print seq;

print "Order: ", Order(H);

runData(H, seq, seq);


// This looks like a real example!!!
G := SmallGroups(18)[3];
seq1 := [ G.1 * G.2^2 * G.3, G.2^2, G.3, G.2^2 * G.3, G.1 ];
seq2 := [ G.1 * G.2^2 * G.3, G.2 * G.3^2, G.2^2 * G.3, G.2 * G.3, G.1 * G.3^2 ];
analyze_sub_curves(G, seq1, seq2);
runData(G, seq1, seq2);

// Diagonal forms example
seq1 := [ G.1 * G.2 * G.3^2, G.1 * G.2, G.2 * G.3, G.1, G.1 * G.3 ];
seq2 := [ G.1 * G.2^2 * G.3, G.1 * G.2^2 * G.3^2, G.2^2 * G.3, G.1 * G.3^2, G.1 ];
runData(G, seq1, seq2);

G := SmallGroups(18)[4];
seq1 := [ G.2^2 * G.3, G.2 * G.3, G.2, G.1 * G.3^2, G.1 * G.2^2 ];
seq2 := [ G.3, G.2^2 * G.3, G.2 * G.3, G.1 * G.3^2, G.1 * G.3^2 ];

runData(G, seq1, seq2);

G := AlternatingGroup(4);
x1 := G ! (1,3)(2,4);
x2 := G ! (1,2,3);
x3 := G ! (1,2,3);
x4 := G ! (2,4,3);

y1 := G ! (1,3)(2,4);
y2 := G ! (1,2)(3,4);
y3 := G ! (2,4,3);
y4 := G ! (1,2,4);

seq1 := [x1,x2,x3,x4];
seq2 := [y1,y2,y3,y4];

runData(G, seq1, seq2);

// NOT SIMPLY-CONNECTED, where did this example come from??

S8 := SymmetricGroup(8);
G := sub<S8| (3,6,7)(4,5,8), (1,8,2)(4,5,6)>;
x1 := G ! (1,8,2,4,3,7,5);
x2 := G ! (1,3,6)(2,8,4);
x3 := G ! (1,6,4)(3,5,7);

y1 := G ! (1,6,5,8,3,2,7);
y2 := G ! (1,4,7,8)(2,6,5,3);
y3 := (y1*y2)^(-1);

seq1 := [x1,x2,x3];
seq2 := [y1,y2,y3];

runData(G, seq1, seq2);


G := SL(2, GF(3));

x1 := G ! [[2,0],[0,2]]; /* monodromy around lambda */
x2 := G ! [[1,2],[0,1]]; /* monodromy around 0 */
x3 := G ! [[1,0],[1,1]]; /* monodromy around 1 */
x4 := G ! [[2,2],[1,0]]; /* monodromy around inf */

seq1 := [x1,x2,x3,x4]; 
seq2 := [x1,x2,x3,x4]; 

runData(G, seq1, seq1);


S120 := SymmetricGroup(120);

x1 := S120 ! (1,61) (2,63) (3,62) (4,64) (5,77) (6,79) (7,78) (8,80) (9,73) (10,75) (11,74) (12,76) (13,69) (14,71) (15,70) (16,72) (17,65) (18,67) (19,66) (20,68) (21,101) (22,103) (23,102) (24,104) (25,117) (26,119) (27,118) (28,120) (29,113) (30,115) (31,114) (32,116) (33,109) (34,111) (35,110) (36,112) (37,105) (38,107) (39,106) (40,108) (41,81) (42,83) (43,82) (44,84) (45,97) (46,99) (47,98) (48,100) (49,93) (50,95) (51,94) (52,96) (53,89) (54,91) (55,90) (56,92) (57,85) (58,87) (59,86) (60,88);
x2 := S120 ! (1,108,3,106) (2,105,4,107) (5,104,7,102) (6,101,8,103) (9,120,11,118) (10,117,12,119) (13,116,15,114) (14,113,16,115) (17,112,19,110) (18,109,20,111) (21,88,23,86) (22,85,24,87) (25,84,27,82) (26,81,28,83) (29,100,31,98) (30,97,32,99) (33,96,35,94) (34,93,36,95) (37,92,39,90) (38,89,40,91) (41,68,43,66) (42,65,44,67) (45,64,47,62) (46,61,48,63) (49,80,51,78) (50,77,52,79) (53,76,55,74) (54,73,56,75) (57,72,59,70) (58,69,60,71);
x3 := S120 ! (1,39,56,9,27,44,17,35,52,5,23,60,13,31,48) (2,38,54,10,26,42,18,34,50,6,22,58,14,30,46) (3,40,53,11,28,41,19,36,49,7,24,57,15,32,45) (4,37,55,12,25,43,20,33,51,8,21,59,16,29,47) (61,99,116,69,87,104,77,95,112,65,83,120,73,91,108) (62,98,114,70,86,102,78,94,110,66,82,118,74,90,106) (63,100,113,71,88,101,79,96,109,67,84,117,75,92,105) (64,97,115,72,85,103,80,93,111,68,81,119,76,89,107);

G := sub<S120 | x1,x2,x3>;

seq1 := [x1,x2,x3]; 
seq2 := [x1,x2,x3]; 

runData(G, seq1, seq1);
end if;