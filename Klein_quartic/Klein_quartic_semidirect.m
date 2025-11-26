/*******************************************************************************
 * Klein_quartic_semidirect.m
 *
 * Purpose:
 *   Study the semidirect product PSL(2,7) ⋊ C_2 where C_2 acts by the outer
 *   automorphism. Analyzes the Frobenius action on F_2-representations and
 *   which subspaces are fixed or exchanged.
 *
 * Method:
 *   1. Find the unique outer automorphism of order 2 in Aut(PSL(2,7))
 *   2. Construct the semidirect product G ⋊ C_2
 *   3. Study the 6-dimensional irreducible F_2-module
 *   4. Decompose as PSL(2,7)-module and track Frobenius action
 *   5. Determine which irreducible subspaces are fixed vs exchanged
 *
 * Output:
 *   - Description of the outer automorphism
 *   - Decomposition of F_2-representation restricted to PSL(2,7)
 *   - Which subspaces are conjugated/fixed by Frobenius
 *
 * Dependencies:
 *   None (standalone computation)
 *
 * Mathematical background:
 *   The outer automorphism of PSL(2,7) corresponds to the Galois action
 *   of Gal(Q(sqrt(-7))/Q) on the CM elliptic curve in the Jacobian.
 ******************************************************************************/

G := PSL(2,7);
A := AutomorphismGroup(G);
// Find an outer automorphism of order 2
a := Identity(A);
found := false;

// First check generators and their powers
for gen in Generators(A) do
    ord := Order(gen);
    if ord eq 2 then
        if not IsInner(gen) then
            a := gen;
            found := true;
            break;
        end if;
    elif IsEven(ord) then
        candidate := gen^(ord div 2);
        if Order(candidate) eq 2 and not IsInner(candidate) then
            a := candidate;
            found := true;
            break;
        end if;
    end if;
end for;

// If not found in generators, search all elements
if not found then
    // Build the set of all automorphisms
    AutSet := { A!1 };
    repeat
        for g1 in Generators(A) do
            for g2 in AutSet do
                Include(~AutSet, g1*g2);
            end for;
        end for;
    until #AutSet eq #A;
    
    for elt in AutSet do
        if Order(elt) eq 2 and not IsInner(elt) then
            a := elt;
            found := true;
            break;
        end if;
    end for;
end if;

if found then
    print "Found outer automorphism of order 2";
    print "IsInner:", IsInner(a);
    print "Order:", Order(a);
else
    print "No outer automorphism of order 2 found";
end if;

H := CyclicGroup(2);

phi := hom<H -> A | H.1 -> a>;
print "phi(H.1)(G.1): ", phi(H.1)(G.1);
GtH,incG,incH := SemidirectProduct(G, H, phi);

F2 := GF(2);
M := IrreducibleModules(GtH, F2)[2];
V := VectorSpace(F2, Dimension(M));  // The full 6-dimensional vector space
print "IsSemisimple: ", IsSemisimple(M);

rep := Representation(M);
// M := GModule(GtH, [rep(g) : g in Generators(GtH)]);

frob := rep(incH(H.1));
print "frob: ", frob;
Rational2Torsion := Kernel(frob - IdentityMatrix(F2, Dimension(M)));

M_triv := Restriction(M, sub<GtH | Id(GtH)>); 
M_G := Restriction(M, sub<GtH | incG(G)>);
decomp := Decomposition(M_G);
subspaces := [];
for N in decomp do
    inc := hom< N -> M_G | v :-> M_G ! v >;
    VN := sub<V | [V ! inc(v) : v in Generators(N)]>;
    Append(~subspaces, VN);
end for;

subspaces;

print "\nNumber of subspaces:", #subspaces;
print "Dimensions of subspaces:", [Dimension(W) : W in subspaces];

// Conjugate subspaces by frob and check if they get exchanged
print "\nConjugating subspaces by Frobenius:";
for i := 1 to #subspaces do
    W := subspaces[i];
    // Compute the image of W under frob: {frob * w : w in W}
    W_conj := sub<V | [w * frob : w in Basis(W)]>;
    
    print "\nSubspace", i, "(dimension", Dimension(W), "):";
    print "  Conjugated subspace dimension:", Dimension(W_conj);
    
    // Check if W_conj equals any of the original subspaces
    found_match := false;
    for j := 1 to #subspaces do
        if W_conj eq subspaces[j] then
            print "  -> Maps to subspace", j;
            found_match := true;
            if i ne j then
                print "  -> EXCHANGED with subspace", j;
            else
                print "  -> Fixed by Frobenius";
            end if;
            break;
        end if;
    end for;
    
    if not found_match then
        print "  -> Does not map to any original subspace";
    end if;
end for;

