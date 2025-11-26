/*******************************************************************************
 * elliptic_curve_sqrt7.m
 *
 * Purpose:
 *   Study the elliptic curve 2.2.28.1-16.1-a1 from LMFDB, defined over the
 *   quadratic field Q(sqrt(7)). This curve appears as a factor in the
 *   Jacobian decomposition of certain algebraic curves.
 *
 * Computations performed:
 *   - Conductor and discriminant (including norms)
 *   - j-invariant
 *   - Test for Complex Multiplication (CM)
 *   - Mordell-Weil rank and generators
 *   - Heights and regulator
 *   - Torsion subgroup structure
 *   - Local reduction data
 *   - Frobenius traces at primes of good reduction
 *   - Supersingular prime detection
 *   - Torsion over Q(sqrt(7), i)
 *
 * Output:
 *   Detailed arithmetic invariants of the elliptic curve.
 *
 * Related files:
 *   - LMFDB_api.m: Interface for fetching LMFDB data
 *   - hilbert_modular_forms.m: Hecke eigenvalue data
 *
 * LMFDB reference:
 *   https://www.lmfdb.org/EllipticCurve/2.2.28.1/16.1/a/1
 ******************************************************************************/

// Define the base number field: Q(sqrt(7))
R<x> := PolynomialRing(Rationals()); K<a> := NumberField(R![-7, 0, 1]);

// Define the curve:
E := EllipticCurve([K![1,1],K![0,1],K![1,1],K![0,0],K![-1,0]]);

// Compute the conductor:
Conductor(E);

// Compute the norm of the conductor:
Norm(Conductor(E));

// Compute the discriminant:
Discriminant(E);

// Compute the norm of the discriminant:
Norm(Discriminant(E));

// Compute the j-invariant:
jInvariant(E);

// Test for Complex Multiplication:
HasComplexMultiplication(E);

// Compute the Mordell-Weil rank:
Rank(E);

// Compute the generators (of infinite order):
gens := [P:P in Generators(E)|Order(P) eq 0]; gens;

// Compute the heights of the generators (of infinite order):
[Height(P):P in gens];

// Compute the regulator:
Regulator(gens);

// Compute the torsion subgroup:
T,piT := TorsionSubgroup(E); Invariants(T);

// Compute the order of the torsion subgroup:
Order(T);

// Compute the generators of the torsion subgroup:
[piT(P) : P in Generators(T)];

// Compute the local reduction data at primes of bad reduction:
LocalInformation(E);

ZK := RingOfIntegers(K);
Dis := Norm(Discriminant(E));

// Print Frobenius traces at primes of good reduction up to given bound
function print_traces(E, bound)
  pps := PrimesUpTo(bound, K);
  for pp in pps do
    p := Factorization(Norm(pp))[1][1];
    if not (ZK ! Dis) in pp then
            print "Characteristic: ", p, "Norm: ", Norm(pp), "Trace: ", TraceOfFrobenius(E, pp);
    end if;
  end for;
  return true;
end function;

// Print only supersingular primes (trace ≡ 0 mod p)
function print_ss_traces(E, bound)
  pps := PrimesUpTo(bound, K);
  for pp in pps do
    p := Factorization(Norm(pp))[1][1];
    if not (ZK ! Dis) in pp then
        if (TraceOfFrobenius(E, pp) mod p) eq 0 then
            print "Characteristic: ", p, "Norm: ", Norm(pp);
        end if;
    end if;
  end for;
  return true;
end function;

// Find supersingular primes organized by characteristic
function supersingular_primes_by_characteristic(E, bound)
  D := Norm(Discriminant(E));
  ss_primes := [];
  primes := PrimesUpTo(bound);
  for p in primes do
    if D mod p ne 0 then
      fact := Factorization(ZK !! 2);
      for f in fact do
        pp := f[1];
        if (TraceOfFrobenius(E, pp) mod p) eq 0 then
          print "Characteristic: ", p, "Norm: ", Norm(pp);
          Append(~ss_primes, pp);
        end if;
      end for;
    end if;
  end for;
  return ss_primes;
end function;


print_traces(E, 100);

// Extend to Q(sqrt(7), i) and compute torsion
K_i := ext<K | PolynomialRing(K)![1, 0, 1]>;
E_i := BaseChange(E, K_i);
TorsionSubgroup(E_i);
