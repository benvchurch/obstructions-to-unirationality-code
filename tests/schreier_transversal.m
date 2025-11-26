/*******************************************************************************
 * test_schreier_transversal.m
 *
 * Purpose:
 *   Compute Schreier transversal and generators for the fundamental group
 *   of a covering space. Given a monodromy representation rho: G -> S_d,
 *   finds generators of the covering space's fundamental group corresponding
 *   to punctures/branch points.
 *
 * Method:
 *   1. Define G as the fundamental group of a punctured sphere (FP group)
 *   2. Given monodromy permutations rho(g_i), compute Schreier transversal
 *   3. For each cycle in each permutation, construct a generator of H' = p_*(H)
 *   4. Generator formula: t_c * g_i^k * t_c^(-1) where k is ramification index
 *
 * Example:
 *   - Base: P^1 \ {0, 1, infinity} (3 punctures, genus 0)
 *   - Cover: Degree 2, rho(g1) = rho(g2) = (1,2), rho(g3) = id
 *   - Verifies that computed generators generate the stabilizer subgroup
 *
 * Output:
 *   - List of generators corresponding to punctures in the cover
 *   - Verification that they generate the correct subgroup H'
 *
 * Dependencies:
 *   None (standalone computation using Magma's built-in functions)
 *
 * Mathematical background:
 *   For a covering map p: Y -> X with monodromy rho, the fundamental group
 *   of Y is isomorphic to p_*(pi_1(Y)) = {g in pi_1(X) : rho(g)(1) = 1}.
 *   The Schreier transversal gives a systematic way to find generators.
 ******************************************************************************/

// Assume you have:
// n: number of punctures/generators for G
// d: degree of the cover
// permutations: A list [pi_1, ..., pi_n] of permutations in Sym(d)
//               corresponding to rho(g_1), ..., rho(g_n)

// Example Data (Genus 0, 3 punctures, Degree 2 cover)
// P1 \ {0, 1, infinity}
// g1 around 0, g2 around 1, g3 around infinity. g1*g2*g3 = 1.
// Let rho(g1)=(1,2), rho(g2)=(1,2). Then rho(g3)=rho(g1*g2)^-1 = id.
n := 3;
d := 2;
S := Sym(d);
permutations := [ S!(1,2), S!(1,2), S!(1) ]; // rho(g1), rho(g2), rho(g3)

// 1. Define the FP Group G
gen_names := [ Sprintf("g%o", i) : i in [1..n] ];
F := FreeGroup(#gen_names);
G := quo<F | &*[F.i : i in [1..n]]>;
print "Defined G:", G;

// 2. Define the homomorphism rho
// Check if the permutations satisfy the relation image
rel_image := &*[ permutations[i] : i in [1..n] ];
if rel_image ne Id(S) then
    error "Error: Provided permutations do not satisfy the relation image in S_d.";
end if;
rho := hom< G -> S | [ permutations[i] : i in [1..n] ] >;
print "Defined homomorphism rho: G -> S_d";

// 3. Compute Schreier Transversal T
// T maps point i to the word in G sending 1 to i.
// CosetTable computes more, Transversal is sufficient if Action is specified
// Need action on points {1..d}. Default action is on cosets of H=sub<G|>.
// Need to define the action explicitly for points.
GSet := GSet(G, {1..d}, rho);
// Transversal gives element t_i such that rho(t_i)(1) = i
T := Transversal(G, Stabilizer(GSet, 1), GSet); // Stabilizer defines the subgroup H'
// T should now map i -> word sending 1 to i. Let's verify.
// print "Transversal elements (mapping 1 to i):";
// for i in [1..d] do
//   printf "  %o -> %o (Action: %o)\n", i, T[i], Image(rho, T[i])(1);
// end for;

// 4. Find the desired generators
desired_generators := [];
puncture_data := []; // Optional: store <gen, base_gen_index, power>
print "\nCalculating generators corresponding to cover punctures:";

for i in [1..n] do
    pi_i := permutations[i]; // rho(G.i)
    cycles_i := CycleDecomposition(pi_i);
    // printf " Processing G.%o (rho=%o), Cycles: %o\n", i, pi_i, cycles_i;

    for C in cycles_i do
        k := #C; // Ramification index (power)
        if k eq 0 then continue; end if; // Should not happen for non-empty cycles

        // Choose a representative sheet from the cycle
        // Magma cycles are lists of points, e.g., [c1, c2, ...]
        c := Minimum(C); // Take the numerically smallest sheet in the cycle

        // Get the transversal element t_c mapping 1 to c
        // T is indexed by the points {1..d}
        t_c := T[c];

        // Construct the generator: t_c * (G.i)^k * t_c^(-1)
        gen := t_c * (G.i)^k * t_c^(-1);
        Append(~desired_generators, gen);
        Append(~puncture_data, <gen, i, k>); // Store extra info

        printf "  Found generator for puncture over p_%o (cycle %o):\n", i, C;
        printf "    Ramification index (k): %o\n", k;
        printf "    Sheet chosen (c): %o\n", c;
        printf "    Transversal elt (t_c): %o\n", t_c;
        printf "    Generator (t_c * g_%o^%o * t_c^-1): %o\n", i, k, gen;

    end for;
end for;

// 5. Result
print "\nFound %o generators corresponding to punctures in the cover:", #desired_generators;
// print desired_generators;

// Optional: Verify they generate the stabilizer
H_prime := Stabilizer(G, 1 : Action := rho); // H' = p_*(H)
K := sub< G | desired_generators >;
print "\nVerification:";
print "Index of computed stabilizer H':", Index(G, H_prime);
print "Index of subgroup K generated by found elements:", Index(G, K);
print "Are the subgroups equal? ", H_prime eq K; // Should be true

// Optional: Check if the generators are what we claimed (conjugate to g_i^k)
print "\nChecking generator forms:";
for data in puncture_data do
    gen := data[1];
    i := data[2];
    k := data[3];
    target := G.i^k;
    // IsConjugate might be slow/difficult in FP groups.
    // But we constructed them to be conjugate.
    // We can check if they belong to H'
    is_in_H_prime := Image(rho, gen)(1) eq 1;
    printf " Generator %o (should be conj to G.%o^%o). Is in H'? %o\n", gen, i, k, is_in_H_prime;
end for;
