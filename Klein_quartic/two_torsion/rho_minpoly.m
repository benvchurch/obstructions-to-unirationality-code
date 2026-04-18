/*******************************************************************************
 * rho_minpoly.m
 *
 * Compute the minimal polynomial of the Legendre parameter rho for the Z/3
 * symmetric Pryms of the Klein twist quartic.
 *
 * The chain is: 6 branch points -> Mobius to {0,1,inf,lam,1-1/lam,1/(1-lam)}
 * -> rho = (1-lam)*(lam + sqrt(lam^2 - lam + 1))^2
 * -> j = 256*(1-rho*(1-rho))^3 / (rho^2*(1-rho)^2)
 *
 * We know the j min polys. Work backwards: express rho algebraically
 * and compute its min poly.
 *
 * Actually easier: just re-run the pipeline for a few complexes and print
 * the intermediate values. But simplest: use the algebraic relation
 * j(rho) = 256*(rho^2-rho+1)^3/(rho^2*(rho-1)^2) and compute rho from j.
 ******************************************************************************/

SetColumns(0);

// The Legendre j-invariant formula:
// j(rho) = 256*(rho^2 - rho + 1)^3 / (rho^2*(rho-1)^2)
// Setting j = j0 and clearing denominators:
// j0 * rho^2*(rho-1)^2 = 256*(rho^2 - rho + 1)^3
// This is a degree-6 polynomial in rho for each j0.

PQ<rho> := PolynomialRing(Rationals());

// For class 1 (28 complexes): j min poly = t^2 + 13856t - 26578688
// j-values are roots of t^2 + 13856t - 26578688
// We need rho such that j(rho) is a root of this poly.
// Resultant approach: eliminate j from the system
//   j*rho^2*(rho-1)^2 - 256*(rho^2-rho+1)^3 = 0
//   j^2 + 13856*j - 26578688 = 0

PQ2<rho2,j2> := PolynomialRing(Rationals(), 2);
rel1 := j2*rho2^2*(rho2-1)^2 - 256*(rho2^2-rho2+1)^3;
jp_class1 := j2^2 + 13856*j2 - 26578688;

printf "=== Klein twist class 1 (j poly = t^2 + 13856t - 26578688) ===\n\n";
res1 := Resultant(rel1, jp_class1, j2);
printf "Resultant (in rho): %o\n\n", res1;
fac1 := Factorization(UnivariatePolynomial(res1));
printf "Factorization:\n";
for f in fac1 do
    printf "  %o  (degree %o, mult %o)\n", f[1], Degree(f[1]), f[2];
end for;

// For classes 3,4 (14 complexes): j min poly = t^4 - 103439t^3 + ...
jp_class34 := j2^4 - 103439*j2^3 + 6670405329*j2^2 + 31128229267744*j2 + 148381159092130048;

printf "\n=== Klein twist classes 3,4 (j poly = t^4 - 103439t^3 + ...) ===\n\n";
res34 := Resultant(rel1, jp_class34, j2);
printf "Resultant computed, factoring...\n";
fac34 := Factorization(UnivariatePolynomial(res34));
printf "Factorization:\n";
for f in fac34 do
    printf "  %o  (degree %o, mult %o)\n", f[1], Degree(f[1]), f[2];
end for;

quit;
