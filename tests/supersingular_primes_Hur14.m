/*******************************************************************************
 * test_supersingular_primes_Hur14.m
 *
 * Purpose:
 *   Find supersingular primes the elliptic curve appearing in the isogeny decomposition of the Hurwitz curve of genus 14
 *
 * Method:
 *   1. Load the field Kabs and curve data from "elliptic_curves_computed"
 *   2. Define an elliptic curve E over this larger field
 *   3. For each rational prime p of good reduction:
 *      - Factor p in the ring of integers of K
 *      - For each prime PP above p, check if trace ≡ 0 (mod p)
 *   4. Search up to bound 5000
 *
 * Prerequisites:
 *   Requires "elliptic_curves_computed" with saved field/curve data.
 *
 * Output:
 *   List of supersingular primes with their characteristics and norms.
 *
 * Related files:
 *   - supersingular_primes_sqrt5.m: Simpler case over Q(sqrt(5))
 *   - elliptic_curve_sqrt7.m: Case over Q(sqrt(7))
 *
 * Note:
 *   This computation can be slow due to the large search bound (5000) and
 *   the complexity of arithmetic in higher-degree number fields.
 ******************************************************************************/

restore "../elliptic_curves_computed";


K := Kabs;
ZK := RingOfIntegers(K);

// What elliptic curve is this? I think it is a random curve
E := E1;


// Print Frobenius traces for supersingular primes
function print_traces(E, bound)
  D := Integers() ! AbsoluteNorm(Discriminant(E));
  pps := PrimesUpTo(bound, K);
  for pp in pps do
    p := Factorization(Norm(pp))[1][1];
    if not (ZK ! D) in pp then
        if (TraceOfFrobenius(E, pp) mod p) eq 0 then
            print "Characteristic: ", p, "Norm: ", Norm(pp);
        end if;
    end if;
  end for;
  return true;
end function;

// Find supersingular primes organized by rational prime characteristic
function supersingular_primes_by_characteristic(E, bound)
  D := Integers() ! AbsoluteNorm(Discriminant(E));
  ss_primes := [];
  primes := PrimesUpTo(bound);
  for p in primes do
    if (D mod p) ne 0 then
      fact := Factorization(ZK !! p);
      for f in fact do
        pp := f[1];
        if (TraceOfFrobenius(E, pp) mod p) eq 0 then
          print "Characteristic: ", p, "Norm: ", Norm(pp), "mod 7: ", p mod 7, "mod 12: ", p mod 12, "mod 13: ", p mod 13;
          Append(~ss_primes, pp);
        end if;
      end for;
    end if;
  end for;
  return ss_primes;
end function;

supersingular_primes_by_characteristic(E, 5000);
