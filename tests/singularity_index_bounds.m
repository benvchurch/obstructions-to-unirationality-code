/*******************************************************************************
 * test_singularity_index_bounds.m
 *
 * Purpose:
 *   Compute bounds on singularity indices for surfaces with signature (2,3,7).
 *   Analyzes how singularity contributions scale with the order of cyclic
 *   stabilizer groups.
 *
 * Method:
 *   1. For signature (a,b,c) = (2,3,7), compute the main term 2(1-1/a-1/b-1/c)^2
 *   2. Sum singularity contributions using continued fraction formulas
 *   3. Compute index bound as ceiling(secondary_term/main_term)
 *   4. Test asymptotic behavior for large cyclic orders (powers of 10)
 *
 * Output:
 *   - The index bound for (2,3,7) signature
 *   - Asymptotic data showing secondary_term for orders 10, 100, ..., 10^100
 *
 * Related files:
 *   - invariants.m: Provides k(), ContFrac(), l() functions
 *   - general_type.m: K^2 computations for general type surfaces
 *
 * Mathematical background:
 *   The index bound gives an upper limit on the index of subgroups that can
 *   appear in the construction of certain product-quotient surfaces.
 ******************************************************************************/

import "../invariants.m": k, ContFrac, l;

a := 2;
b := 3;
c := 7;

main_term := 2*(1 - 1/a - 1/b - 1/c)^2;
secondary_term := 0;

for o in [a,b,c] do
    for i in [1..o-1] do
        secondary_term := secondary_term + (k(i/o) + 3 * (&+ContFrac(i/o) - 2 * l(i/o)) + 2) * (1/o);
    end for;
end for;

index_bound := Ceiling(secondary_term/main_term);

Log(10,Factorial(index_bound)) * (1/2 * (Log(2, Factorial(index_bound)) + 1));

// Asymptotic analysis: how does secondary_term scale with order?
for power in [1..100] do
    o := 10^power;
    secondary_term := 0;
    for i in [1..o-1] do
        secondary_term := secondary_term + (k(i/o) + 3 * (&+ContFrac(i/o) - 2 * l(i/o)) + 2) * (1/o);
    end for;
    print o, secondary_term + 0.01;
end for;
