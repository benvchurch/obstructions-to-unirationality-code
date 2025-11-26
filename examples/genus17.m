/*******************************************************************************
 * genus17.m
 *
 * Purpose:
 *   Detailed study of the Hurwitz curve of genus 17 with automorphism group
 *   of order 1344. Analyzes subgroup lattice, Jacobian decomposition, and
 *   intermediate quotient curves.
 *
 * The curve:
 *   - Genus 17 Hurwitz curve with Aut(C) of order 1344 = 84*(17-1)
 *   - Monodromy: P = 14-cycle, Q = 8-cycle, with U = P^2*Q, T = P^3*Q
 *   - Spherical triple: [U, T, (U*T)^(-1)]
 *
 * Computations:
 *   - Genus of all intermediate quotient curves C/H
 *   - Rational cohomology decomposition (Jac ~ E_0^? x E^? ...)
 *   - Subgroup lattice analysis
 *   - Automorphism structure of genus 5 quotient (S_4 action)
 *   - Elliptic curve factors in Jacobians of intermediate quotients
 *
 * Dependencies:
 *   - intermediate_extensions.m: Genus computations
 *   - group_reps.m: Cohomology decomposition
 *
 * Related files:
 *   - compute_examples.m: Uses this curve as a main example
 ******************************************************************************/

import "../intermediate_extensions.m": Genus, GenusIntermediateExtension, IntermediateMonodromy, IntermediateMonodromyTake2;
import "../group_reps.m" : FindBelyiCurve, FindBelyiCurveOrders, SphGensUptoConj, computeGroupRingDecomposition, computeRationalCohomology;

// Hurwitz curve of genus 17



S := SymmetricGroup(14);
P := S!(1, 13, 2, 11, 4, 5, 8)(3, 10, 6, 14, 7, 9, 12);
Q := S!(1, 7, 3, 4)(2, 11, 13, 9, 6, 14, 10, 5);

G := sub<S | P,Q>;
U := P^2*Q;
T := P^3*Q;
seq := [U,T,(U*T)^(-1)];

// check if there is a real structure

F<x,y> := FreeGroup(2);
psi := hom<F -> G | x -> T, y -> U>;
Gamma := Kernel(psi);
inv := hom< F-> F | x -> x, y -> x * y^(-1) * x >; // complex conjugation on P^1 \sm {0,1,inf}
print "Obstruction to lifting complex conjugation: ", Order(psi(inv(Gamma)));    

// if there is a real structure, does it have to lift the one where 0,1,inf are real and the real points are a geodesic? If geodesics commute with complex conjugation (meaning it is an isometry) then the real locus is a geodesic

L := SubgroupLattice(G);

subgroups := [Subgroups(G)[i]`subgroup : i in [1..#Subgroups(G)]];

for i in [1..#subgroups] do
    H := subgroups[i];
    print i, GenusIntermediateExtension(G, seq, H);
end for;

v, mat :=computeRationalCohomology(G,seq : returnMat:=true);
v;

NN := Normalizer(G, subgroups[6]);
Q, phi := quo<NN | subgroups[6]>; // (subgroup of) automorphism group of the genus 5 quotient curve
IdentifyGroup(Q);

L ! NN; // get subgroup 71 corresponding to the S4 in the automorphism of the Klein quartic
C := Center(Q) @@ phi;
L ! C;

K4 := NormalSubgroups(Q)[3]`subgroup; // the copy of the normal Klein 4 in Q
K4_pre := K4 @@ phi;
L ! K4_pre;

IdentifyGroup(quo<Q | K4>);

subsQ := [Subgroups(Q)[i]`subgroup : i in [1..#Subgroups(Q)]];
for i in [1..#subsQ] do
    H := subsQ[i];
    H_pre := H @@ phi;
    a := mat[IntegerRing() ! (L ! H_pre)][2]/2; // copies of the CM curve
    b := mat[IntegerRing() ! (L ! H_pre)][8]; // copies of the other elliptic curve
    print i, L ! H_pre, a,b, a + b, Order(NN) / Order(H_pre), IsNormal(Q, H);
end for;
