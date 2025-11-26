/*******************************************************************************
 * supersingular_primes_congruence_Q.m
 *
 * Purpose:
 *   Analyze supersingular primes for the elliptic curve 2.2.5.1-81.1-a1
 *   defined over Q(sqrt(5)). Supersingular primes are those where the
 *   Frobenius trace is divisible by p, indicating supersingular reduction.
 *   Question: where did this example come from? It has CM by sqrt(-15)
 *
 * Method:
 *   1. Define K = Q(sqrt(5)) and the elliptic curve E over K
 *   2. For each rational prime p that is inert in K and of good reduction:
 *      - Compute the unique prime PP of K above p
 *      - Check if TraceOfFrobenius(E, PP) ≡ 0 (mod p)
 *   3. Also compute torsion over K(i)
 *
 * Output:
 *   - List of inert supersingular primes up to bound 1000
 *   - For each: the prime norm and its residue class mod 12
 *   - Torsion subgroup over K(i)
 *
 * Related files:
 *   - test_elliptic_curve_sqrt_neg7.m: Similar analysis over Q(sqrt(7))
 *   - test_supersingular_primes_Hur14.m: Elliptic curve in the isogeny decomposition of Hur14
 *
 * LMFDB reference:
 *   https://www.lmfdb.org/EllipticCurve/2.2.5.1/81.1/a/1
 ******************************************************************************/

K := Rationals();

// 3 is -1 mod 4 so there is only the supersingular constraint p = 2 mod 3

E_3CM := EllipticCurve([K!0, K!0, K!0, K!0, K!1]); // CM by Q(sqrt(-3))

// Define the curve: 
E_3tors := EllipticCurve([0, 1, 1, -9, -15]); // has 3 torsion


ZK := RingOfIntegers(K);

D := Discriminant(ZK);
Del := Integers() ! AbsoluteNorm(Discriminant(E_3CM)) * Integers() ! AbsoluteNorm(Discriminant(E_3tors));

// Find joint supersingular primes: primes p that are supersingular for both E1 and E2
function joint_supersingular_primes(E1, E2, bound)
  pps := PrimesUpTo(bound); // primes of Q
  for pp in pps do
    if (not pp eq 2) and (not Del mod pp eq 0) then // only look at primes of good reduction
        if TraceOfFrobenius(E1, pp) mod pp eq 0 and TraceOfFrobenius(E2, pp) mod pp eq 0 then
            print "Joint supersingular prime of K: ", Norm(pp), "mod 12: ", Norm(pp) mod 12, "mod 3: ", Norm(pp) mod 3;
        end if;
    end if;
  end for;
  return [];
end function;

joint_supersingular_primes(E_3CM, E_3tors, 10000);