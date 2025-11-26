/*******************************************************************************
 * Klein_quartic.m
 *
 * Purpose:
 *   Study the Klein quartic curve (genus 3 with automorphism group PSL(2,7)).
 *   Analyzes mod-2 representations, orbit structures, and rational cohomology
 *   decomposition of the Jacobian.
 *
 * Computations:
 *   - Find Belyi representation with ramification orders (2,3,7)
 *   - Compute rational cohomology decomposition (Jac ~ E_0^3 x E^14 where
 *     E_0 has CM by Q(sqrt(-7)))
 *   - Reduce 3-dimensional Q-irrep to mod 2 representation
 *   - Compute orbit structure under PSL(2,7) action on F_2^3
 *   - Analyze restrictions to S_3 subgroup
 *   - Z-basis computations for Q(sqrt(-7)) representations
 *
 * Dependencies:
 *   - invariants.m: Surface invariant functions
 *   - intermediate_extensions.m: Genus, monodromy computations
 *   - group_reps.m: FindBelyiCurveOrders, computeRationalCohomology
 *
 * Mathematical background:
 *   The Klein quartic x^3*y + y^3*z + z^3*x = 0 has automorphism group
 *   PSL(2,7) of order 168, achieving the Hurwitz bound for genus 3.
 ******************************************************************************/

load "../invariants.m";
import "../intermediate_extensions.m": Genus, GenusIntermediateExtension, IntermediateMonodromy, IntermediateMonodromyTake2;
import "../group_reps.m" : FindBelyiCurveOrders, computeRationalCohomology;


G := PSL(2,7);
seq := FindBelyiCurveOrders(G, [2,3,7]);
computeRationalCohomology(G, seq);

M := IrreducibleModules(G, Rationals())[2];
phi := Representation(M);

// After your existing code in Klein_quartic.m

// Get the dimension of the representation
dim := Dimension(M);

// Get generators of the group
gens := [G.i : i in [1..Ngens(G)]];

// Get the matrices of the representation over Q
matrices_Q := [ActionGenerator(M, i) : i in [1..Ngens(G)]];

// Reduce mod 2: convert to matrices over F2
F2 := GF(2);
matrices_F2 := [Matrix(F2, m) : m in matrices_Q];

// Create the representation over F2
// First, create a module over F2
V := VectorSpace(F2, dim);
M_F2 := GModule(G, matrices_F2);
phi_F2 := Representation(M_F2);

// compute restrictions to S3

S3 := Subgroups(G)[8]`subgroup;
M_S3 := Restriction(M_F2, S3);
Decomposition(M_S3);

Decomposition(M_F2)[1];
Decomposition(Restriction(Decomposition(M_F2)[1], S3));


// More efficient version using Magma's built-in orbit computation

// After getting M_F2 as above...

// Create the projective space
proj_space := ProjectiveSpace(F2, dim - 1);

// Use Magma's orbit computation
X := Set(V);
XxG := CartesianProduct(X, G);
f := map< XxG -> X | x :-> x[1]*phi_F2(x[2])>;
action := GSet(G, X, f);
orbits := Orbits(G, action);

print "Number of orbits:", #orbits;
print "Orbit sizes:", [#orbit : orbit in orbits];

if false then

K := NumberField(PolynomialRing(Rationals())![7, 0, 1]);
V := VectorSpace(K, 3);
a := (-1 + K.1)/2;
abar := (-1 - K.1)/2;


matricesOriginal := [[[-1,0,0],[0,0,-1],[0,-1,0]], [[0,1,0],[0,0,1],[1,0,0]],[[0,1,0],[1,0,0],[0,0,-1]],[[-1/2, 1/2, abar/2],[a/2,a/2,0],[-1/2,1/2,-abar/2]]];

// Change basis of matrices
// Create the change of basis matrix P where columns are the new basis vectors
P := Matrix(K, 3, 3, [
    [K!2, abar, a],
    [K!0, abar, K!1],
    [K!0, K!0, K!1]
]);

// Compute P^(-1)
P_inv := P^(-1);

// Transform each matrix: M_new = P^(-1) * M_old * P
matricesNewBasis := [];
for i := 1 to #matricesOriginal do
    M_old := Matrix(K, matricesOriginal[i]);
    M_new := P_inv * M_old * P;
    Append(~matricesNewBasis, M_new);
end for;

print "Original matrices:";
for i := 1 to #matricesOriginal do
    print "Matrix", i, ":";
    print Matrix(K, matricesOriginal[i]);
    print "";
end for;

print "Change of basis matrix P:";
print P;
print "";

print "Matrices in new basis:";
for i := 1 to #matricesNewBasis do
    print "Matrix", i, "in new basis:";
    print matricesNewBasis[i];
    print "";
end for;
 
 // Convert matrices to Z-basis representation
ZK := RingOfIntegers(K);
basis := Basis(ZK);
print "Z-basis for ZK:", basis;
print "";

// Function to convert a matrix over K to a matrix over Z using Z-basis
function MatrixToZBasis(M, ZK)
    n := Nrows(M);
    d := Degree(K);  // Should be 2 for Q(√(-7))
    
    // Create a matrix over Z of size (n*d) x (n*d)
    // Each entry M[i,j] becomes a d x d block representing M[i,j] in the Z-basis
    // Actually, for matrix multiplication, we need to think of it differently:
    // If M acts on a vector space V over K, and we write V as V_Z ⊗_Z ZK,
    // then M becomes a (n*d) x (n*d) matrix over Z
    
    ZM := ZeroMatrix(Integers(), n*d, n*d);
    
    for i := 1 to n do
        for j := 1 to n do
            // Get coordinates of M[i,j] in the Z-basis
            for k := 1 to d do
                coords := ZK ! (M[i,j] * basis[k]);
                for l := 1 to d do
                    ZM[d*(i-1)+k, d*(j-1)+l] := coords[l];
                end for;
            end for;
        end for;
    end for;
    
    return ZM;
end function;

// Convert all matrices to Z-basis representation
matricesZBasis := [];
for i := 1 to #matricesNewBasis do
    ZM := MatrixToZBasis(matricesNewBasis[i], ZK);
    Append(~matricesZBasis, ZM);
end for;

print "Matrices in Z-basis representation (6x6 matrices over Z):";
for i := 1 to #matricesZBasis do
    print "Matrix", i, "in Z-basis:";
    print matricesZBasis[i];
    print "";
end for;

Gmat := MatrixGroup<3,K | matricesNewBasis>;

F2 := GF(2);
matrices_F2 := [Matrix(F2, m) : m in matricesZBasis];

// Create the representation over F2
// First, create a module over F2
V := VectorSpace(F2, dim);
M_F2 := GModule(Gmat, matrices_F2);
phi_F2 := Representation(M_F2);
proj_space := ProjectiveSpace(F2, dim - 1);
X := Set(V);
XxG := CartesianProduct(X, Gmat);
f := map< XxG -> X | x :-> x[1]*phi_F2(x[2])>;
action := GSet(Gmat, X, f);
orbits := Orbits(Gmat, action);

print "Number of orbits:", #orbits;
print "Orbit sizes:", [#orbit : orbit in orbits];
end if;