/*******************************************************************************
 * test_quadratic_twists.m
 *
 * Purpose:
 *   Study quadratic twists of an elliptic curve and analyze how the torsion
 *   subgroup changes under twisting. This is relevant for understanding
 *   families of elliptic curves arising from Jacobian decompositions.
 *
 * Method:
 *   1. Load previously computed elliptic curve data from "elliptic_curves_computed"
 *   2. For each integer d from 2 to 100, compute the quadratic twist E_d
 *   3. Compute the torsion subgroup of each twist
 *
 * Prerequisites:
 *   Requires the file "elliptic_curves_computed" containing saved curve data
 *   (typically E1, Kabs from previous computations).
 *
 * Output:
 *   Torsion subgroup structure for each quadratic twist.
 *
 * Related files:
 *   - test_elliptic_curve_sqrt_neg7.m: Original curve analysis
 *   - test_supersingular_primes_sqrt5.m: Related curve studies
 *
 * Mathematical background:
 *   The quadratic twist of E by d is the curve E_d: dy^2 = x^3 + ax + b.
 *   Twisting can change the Mordell-Weil group structure significantly.
 ******************************************************************************/

restore "elliptic_curves_computed";

E := E1;

for d in [2..100] do
  Ed := QuadraticTwist(E, d);
  TorsionSubgroup(Ed);
end for;
