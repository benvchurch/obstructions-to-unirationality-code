/*******************************************************************************
 * test_psl_centralizers.m
 *
 * Purpose:
 *   Compute centralizer orders and singularity contributions for PSL(2,q)
 *   acting on a curve with signature (2, 3, 7). This is used to compute
 *   the "diagonal number" which appears in product-quotient surface
 *   invariant calculations.
 *
 * Method:
 *   1. For a prime p, determine q such that PSL(2,q) has elements of order 7
 *      (q = p if p ≡ ±1 (mod 7), otherwise q = p^3)
 *   2. Compute centralizer orders for elements of orders 2, 3, 7 in PSL(2,q)
 *   3. Calculate singularity contributions using continued fraction formulas
 *      from invariants.m
 *
 * Output:
 *   - Centralizer orders for elements of each specified order
 *   - The computed diagonal number
 *
 * Related files:
 *   - invariants.m: Provides k(), ContFrac(), l() functions
 *   - general_type.m: Uses similar singularity computations
 *
 * Mathematical background:
 *   The diagonal number counts fixed points in the diagonal action on
 *   products of curves, used in computing K^2 for product-quotient surfaces.
 ******************************************************************************/

import "../invariants.m": k, ContFrac, l;

p := 11;
if (p mod 7 eq 1) or (p mod 7 eq 6) then
    q := p;
else
    q := p^3;
end if;

// Compute orders of centralizers for elements of order 2, 3, and 7 in PSL(2,q)

G := PSL(2, q);
cl := ConjugacyClasses(G);
orders := [2, 3, 7];
orderCentralizers := AssociativeArray();

print "q =", q;

for o in orders do
    centralizerOrders := [];
    for C in cl do
        elt := C[3];
        if C[1] eq o then
            Append(~centralizerOrders, #Centralizer(G, elt));
        end if;
    end for;
    orderCentralizers[o] := Set(centralizerOrders); // distinct orders only
end for;

// Print the orders of centralizers for each specified element order
for o in orders do
    print "Orders of centralizers for elements of order", o, ":", orderCentralizers[o];
end for;

// now we compute the contribution from each singularity

diagonalNumber := 8 * (# G)/(84)^2;

for o in orders do
    for c in orderCentralizers[o] do
        for i in [1..o-1] do
            for val in orderCentralizers[o] do
                diagonalNumber := diagonalNumber - (k(i/o) + 3 * (&+ContFrac(i/o) - 2 * l(i/o)) + 2) * val;
            end for;
        end for;
    end for;
end for;

diagonalNumber;
