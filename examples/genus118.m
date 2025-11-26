/*******************************************************************************
 * genus118.m
 *
 * Purpose:
 *   Study the Hurwitz curve of genus 118 with automorphism group PSL(2,27).
 *   This is one of the larger Hurwitz curves in the "small" range.
 *
 * The curve:
 *   - Genus: 118 = (|PSL(2,27)| / 84) + 1 = (9828/84) + 1
 *   - Automorphism group: PSL(2,27) of order 9828
 *   - Ramification type: (2, 3, 7)
 *
 * Computations:
 *   - Find spherical generators of type (2,3,7)
 *   - Verify genus using Riemann-Hurwitz
 *   - Compute rational cohomology decomposition of Jac(C)
 *
 * Dependencies:
 *   - intermediate_extensions.m: Genus computation
 *   - group_reps.m: computeRationalCohomology
 *
 * Mathematical background:
 *   PSL(2,q) is a Hurwitz group when q ≡ ±1 (mod 7). For q = 27 = 3^3,
 *   we have 27 ≡ -1 (mod 7), so PSL(2,27) is a Hurwitz group.
 ******************************************************************************/

G := PSL(2, 27);

g2 := ConjugacyClasses(G)[2][3];

for g in G do
    if Order(g) eq 3 and Order(g*g2) eq 7 and sub<G | g2, g> eq G then
        g3 := g;
        g7 := (g2*g3)^(-1);
        seq := [g2, g3, g7];
        print seq;
        break;
    end if;
end for;

print &* seq;
print [Order(g) : g in seq];

import "../intermediate_extensions.m": Genus;
import "../group_reps.m": computeRationalCohomology;

Genus(G, seq);
v, mat := computeRationalCohomology(G, seq : returnMat := true);
v;
mat;
