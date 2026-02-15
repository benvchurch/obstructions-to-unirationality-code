load "../invariants.m";
import "../intermediate_extensions.m": Genus, GenusIntermediateExtension, IntermediateMonodromy, IntermediateMonodromyTake2;
import "../group_reps.m" : FindBelyiCurveOrders, computeRationalCohomology;


G := SymmetricGroup(3);
A := AbelianGroup([4, 4]);
AutA := AutomorphismGroup(A);
R := Integers(4);

// Standard rep of S_3: permutation rep on (Z/4Z)^3 mod diagonal
// Basis: f_i = e_i - e_3 for i = 1,2
// sigma sends f_i to e_{sigma(i)} - e_{sigma(3)}

StdMat := function(sigma)
    M := Matrix(R, 2, 2, [0,0,0,0]);
    for i in [1..2] do
        v := [R|0, 0];
        si := i^sigma; s3 := 3^sigma;
        if si le 2 then v[si] +:= 1; end if;
        if s3 le 2 then v[s3] -:= 1; end if;
        M[i] := Vector(R, v);
    end for;
    return M;
end function;

// Lift a 2x2 matrix over Z/4 to an element of AutA
// (brute-force preimage search — fine since |Aut((Z/4)^2)| = 96)
MatToAut := function(M)
    imgs := [];
    for i in [1..2] do
        img := A!0;
        for j in [1..2] do
            coeff := Integers()!M[i][j];
            img +:= coeff * A.j;
        end for;
        Append(~imgs, img);
    end for;
    alpha := hom<A -> A | imgs>;
    if #Kernel(alpha) ne 1 or #Image(alpha) ne #A then
        error "Matrix does not give an automorphism";
    end if;
    return AutA!alpha;
end function;

// Build hom: S_3 -> Aut((Z/4)^2)
gen_imgs := [MatToAut(StdMat(g)) : g in Generators(G)];
rho := hom<G -> AutA | gen_imgs>;

// Verify
assert #Kernel(rho) eq 1;
assert #{rho(g) : g in G} eq 6;

GG := SemidirectProduct(A, G, rho);
IdentifyGroup(GG);

g2 := ConjugacyClasses(GG)[3][3]; // element of order 2
g3 := Id(GG);
for g in GG do
    if Order(g) eq 3 and Order(g*g2) eq 8 and sub<GG | g2, g> eq GG then
        print "FOUND g3 = ", g;
        g3 := g;
        break;
    end if;
end for;

seq := [g2, g3, (g2*g3)^(-1)];
print "Genus(GG, seq) = ", Genus(GG, seq);

computeRationalCohomology(GG, seq);

M := IrreducibleModules(GG, Rationals())[7];

// take the residual representation mod 2 

phi := Representation(M);
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

Decomposition(M_F2);
IsSemisimple(M_F2); // not semisimple means that the mod 2 representation is not uniquely determined, there can be other Z lattices giving different results
