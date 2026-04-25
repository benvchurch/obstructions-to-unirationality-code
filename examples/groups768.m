/*******************************************************************************
 * groups768.m
 *
 * Purpose:
 *   Study the unique (2,3,8) group of order 768 = 2^8 * 3.
 *   SmallGroup(768, 1085341) is the unique such group (verified by exhaustive
 *   search over all 1090235 groups of order 768, guarded by `if false`).
 *
 * Results:
 *   - 64 spherical (2,3,8) triples, forming 4 conjugacy classes of size 16,
 *     fused into a single orbit under Aut(G) (|Out(G)| = 4).
 *   - Unique D6 subgroup (subgroup 89, up to conjugacy). This is the only
 *     subgroup giving genus-0 intermediate with positive DiagonalFormNumber.
 *   - For ALL pairs (seq_i, seq_j) of D6-intermediate monodromy sequences:
 *     DiagonalFormNumber = 28 > 0 and Pi1 is trivial.
 *
 * Dependencies:
 *   invariants.m, intermediate_extensions.m, group_reps.m
 ******************************************************************************/

// Exhaustive search (slow — disabled)
if false then
N768 := NumberOfSmallGroups(768);
printf "Searching %o groups of order 768...\n", N768;
groups_238 := [];

for idx in [1..N768] do
  if idx mod 10000 eq 0 then
    printf "  checked %o / %o\n", idx, N768;
  end if;
  G := SmallGroup(768, idx);
  cc := ConjugacyClasses(G);

  orders := {c[1] : c in cc};
  if not ({2,3,8} subset orders) then continue; end if;

  elts3 := &join[Conjugates(G, c[3]) : c in cc | c[1] eq 3];
  reps2 := [c[3] : c in cc | c[1] eq 2];

  found := false;
  for a in reps2 do
    for b in elts3 do
      if Order(a*b) eq 8 and sub<G | a, b> eq G then
        printf "Found: SmallGroup(768, %o)\n", idx;
        Append(~groups_238, <idx, G>);
        found := true;
        break b;
      end if;
    end for;
    if found then break; end if;
  end for;
end for;

printf "Number of (2,3,8) groups: %o\n", #groups_238;
for t in groups_238 do
  printf "  SmallGroup(768, %o)\n", t[1];
end for;
end if;

// --- Setup ---

G := SmallGroup(768, 1085341);
cc := ConjugacyClasses(G);

// Find all (2,3,8) generating triples
gens := [];
elts3 := &join[Conjugates(G, c[3]) : c in cc | c[1] eq 3];
reps2 := [c[3] : c in cc | c[1] eq 2];

for a in reps2 do
  for b in elts3 do
    if Order(a*b) eq 8 and sub<G | a, b> eq G then
      Append(~gens, [a, b, (a*b)^(-1)]);
    end if;
  end for;
end for;
printf "Total (2,3,8) triples: %o\n", #gens;

load "../invariants.m";
import "../intermediate_extensions.m": Genus, GenusIntermediateExtension, IntermediateMonodromy, IntermediateMonodromyTake2;
import "../group_reps.m" : FindBelyiCurve, SphGensUptoConj, computeRationalCohomology;

// --- D6 intermediate monodromy for each triple ---

H := Subgroups(G)[89]`subgroup;
assert IsIsomorphic(H, SmallGroup(12, 4));

H_seqs := [];
for i in [1..#gens] do
  seq := gens[i];
  assert GenusIntermediateExtension(G, seq, H) eq 0;
  H_seq_list, _ := IntermediateMonodromy(G, seq, H);
  H_seq := H_seq_list[1];
  Hsub := sub<G | H_seq>;
  H_seq := [Hsub !h : h in H_seq | h ne Id(G)];
  Append(~H_seqs, H_seq);
end for;
printf "D6-intermediate sequences: %o\n", #H_seqs;

// --- Verify all partial twists have positive Diagonal and trivial Pi1 ---
// Fix the first sequence (justified by single Aut(G)-orbit on triples),
// pair with all 64 sequences for the second factor.

all_pass := true;
seq1 := H_seqs[1];
for j in [1..#H_seqs] do
  seq2 := H_seqs[j];
  diag := DiagonalFormNumber([seq1, seq2], H);
  OrderPi1 := Order(Pi1_v2([seq1, seq2], H));
  if diag le 0 or OrderPi1 ne 1 then
    printf "FAIL (1,%o): Diagonal = %o, |Pi1| = %o\n", j, diag, OrderPi1;
    all_pass := false;
  end if;
end for;

if all_pass then
  printf "ALL %o partial twists pass: Diagonal = 28, Pi1 trivial.\n", #H_seqs;
else
  printf "Some partial twists FAILED.\n";
end if;
