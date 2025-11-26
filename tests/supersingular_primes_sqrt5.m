/*******************************************************************************
 * supersingular_primes_sqrt5.m
 *
 * Purpose:
 *   Analyze supersingular primes for the elliptic curve 2.2.5.1-81.1-a1
 *   defined over Q(sqrt(5)). Supersingular primes are those where the
 *   Frobenius trace is divisible by p, indicating supersingular reduction.
 *   Question: where did this example come from? It has CM by sqrt(-15). Why only inert primes?
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

// Define the base number field: Q(sqrt(5))
R<x> := PolynomialRing(Rationals()); K<a> := NumberField(R![-1, -1, 1]);

// Define the curve:
E := EllipticCurve([K![1,0],K![-1,0],K![0,1],K![0,-2],K![0,1]]);


ZK := RingOfIntegers(K);

D := Discriminant(ZK);
Del := Discriminant(E);

// Find inert supersingular primes: primes p inert in K with trace ≡ 0 (mod p)
function print_traces(E, bound)
  pps := PrimesUpTo(bound); // primes of Q
  for pp in pps do
    if (not pp eq 2) and (not Norm(ZK * Del) mod pp eq 0) and LegendreSymbol(D, pp) eq -1 then // only look at inert primes of good reduction
        PP := Factorization(pp * ZK)[1][1];
        if TraceOfFrobenius(E, PP) mod pp eq 0 then
            print "Prime of K with norm: ", Norm(PP), "Norm mod 12: ", Norm(PP) mod 12;
        end if;
    end if;
  end for;
  return true;
end function;

print_traces(E, 1000);

// Extend to K(i) and compute torsion
K_i := ext<K | PolynomialRing(K)![1, 0, 1]>;
E_i := BaseChange(E, K_i);
TorsionSubgroup(E_i);
