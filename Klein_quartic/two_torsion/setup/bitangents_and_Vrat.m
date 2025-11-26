/*******************************************************************************
 * bitangent_2torsion2.m
 *
 * Clean computation of the Brauer obstruction for the Fermat quartic.
 * Work over F_3 where J[2](F_3) = (Z/2Z)^3 = J[2](Q) (same size).
 ******************************************************************************/

p := 3;
Fp := GF(p);
Fpt<t> := FunctionField(Fp);
Fptu<u> := PolynomialRing(Fpt);
f := u^4 + t^4 + 1;
assert IsIrreducible(f);
FF := FunctionField(f);
Cl, m := ClassGroup(FF);
invs := Invariants(Cl);
printf "Cl(C/F_%o) = ", p;
for i in [1..#invs] do
    if i gt 1 then printf " x "; end if;
    printf "Z/%oZ", invs[i];
end for;
printf "\n\n";

// Identify J[2] = degree-0 2-torsion
// Cl = Z/4Z x Z/4Z x Z/4Z x Z (gens Cl.1, Cl.2, Cl.3, Cl.4)
// Torsion part = Z/4Z^3, free part = Z (degree).
// J = Pic^0 = torsion part.
// J[2] = <2*Cl.1, 2*Cl.2, 2*Cl.3> = (Z/2Z)^3.

e1 := 2*Cl.1;
e2 := 2*Cl.2;
e3 := 2*Cl.3;
J2 := sub<Cl | e1, e2, e3>;
printf "J[2](F_%o) = (Z/2Z)^3, order %o\n", p, #J2;
printf "Generators: e1=%o, e2=%o, e3=%o\n\n", e1, e2, e3;

// Degree of the free generator
deg_free := Degree(m(Cl.4));
printf "Free generator Cl.4 has degree %o\n\n", deg_free;

// =========================================================================
// Q-rational bitangent classes (degree 0 by construction)
// =========================================================================
elt_t := FF ! t;
elt_u := FF.1;

L1 := elt_t + elt_u + 1;  // (x+y+z)/z
L2 := elt_t + elt_u - 1;  // (x+y-z)/z
L3 := elt_t - elt_u + 1;  // (x-y+z)/z
L4 := -elt_t + elt_u + 1; // (-x+y+z)/z

function HalfPositive(D)
    B := D - D;
    for pl in Support(D) do
        v := Valuation(D, pl);
        if v gt 0 then
            B := B + (v div 2) * pl;
        end if;
    end for;
    return B;
end function;

B1 := HalfPositive(Divisor(L1));
B2 := HalfPositive(Divisor(L2));
B3 := HalfPositive(Divisor(L3));
B4 := HalfPositive(Divisor(L4));

P12 := (B1-B2) @@ m;
P13 := (B1-B3) @@ m;
P14 := (B1-B4) @@ m;

print "=== Q-RATIONAL BITANGENT CLASSES ===";
printf "P12 = [B1-B2] = %o\n", P12;
printf "P13 = [B1-B3] = %o\n", P13;
printf "P14 = [B1-B4] = %o (= P12+P13)\n", P14;
printf "Check: P12+P13+P14 = %o\n\n", P12+P13+P14;

V_rat := sub<Cl | P12, P13>;
printf "Subspace from Q-rat bitangents: order %o (should be 4)\n", #V_rat;
printf "Elements: ";
for g in V_rat do printf "%o, ", g; end for;
printf "\n\n";

// Express in terms of J[2] basis
printf "In J[2] basis {e1,e2,e3}:\n";
printf "  P12 = %o  -> in J[2]? %o\n", P12, P12 in J2;
printf "  P13 = %o  -> in J[2]? %o\n", P13, P13 in J2;

// =========================================================================
// Conjugate-pair classes (degree 4, need to project to degree 0)
// =========================================================================
print "";
print "=== CONJUGATE-PAIR BITANGENT CLASSES ===";

// g = (x+z)^2+y^2 comes from bitangent pair {x+iy+z, x-iy+z}
// div(g) = 2*(B_ell + B_sigma(ell)), so B_ell+B_sigma(ell) = HalfPositive(div(g))
// has degree 4. To get a degree-0 class, subtract a reference degree-4 divisor.
// Use 2*B1 ~ K_C (hyperplane section) as reference.

// But more directly: the DEGREE-0 2-torsion class from the conjugate pair is
// [B_ell + B_sigma(ell) - 2*B1] = [B_ell + B_sigma(ell)] - [2*B1]
// = [B_ell - B1] + [B_sigma(ell) - B1]

ref := 2*B1;  // degree-4 reference divisor

// Function g1 = (x+z)^2+y^2 = (t+1)^2+u^2
g1 := (elt_t+1)^2 + elt_u^2;
Bg1 := HalfPositive(Divisor(g1));
Q1 := (Bg1 - ref) @@ m;
printf "Q1 = [(x+z)^2+y^2 tangency - 2B1]: %o, degree 0? %o, in J[2]? %o\n",
       Q1, Degree(m(Q1)), Q1 in J2;

// g2 = (x-z)^2+y^2 = (t-1)^2+u^2
g2 := (elt_t-1)^2 + elt_u^2;
Bg2 := HalfPositive(Divisor(g2));
Q2 := (Bg2 - ref) @@ m;
printf "Q2 = [(x-z)^2+y^2 tangency - 2B1]: %o, in J[2]? %o\n", Q2, Q2 in J2;

// g3 = x^2+(y+z)^2 = t^2+(u+1)^2
g3 := elt_t^2 + (elt_u+1)^2;
Bg3 := HalfPositive(Divisor(g3));
Q3 := (Bg3 - ref) @@ m;
printf "Q3 = [x^2+(y+z)^2 tangency - 2B1]: %o, in J[2]? %o\n", Q3, Q3 in J2;

// g4 = x^2+(y-z)^2 = t^2+(u-1)^2
g4 := elt_t^2 + (elt_u-1)^2;
Bg4 := HalfPositive(Divisor(g4));
Q4 := (Bg4 - ref) @@ m;
printf "Q4 = [x^2+(y-z)^2 tangency - 2B1]: %o, in J[2]? %o\n", Q4, Q4 in J2;

// g5 = (x+y)^2+z^2 = (t+u)^2+1 (z=1)
g5 := (elt_t+elt_u)^2 + 1;
Bg5 := HalfPositive(Divisor(g5));
Q5 := (Bg5 - ref) @@ m;
printf "Q5 = [(x+y)^2+z^2 tangency - 2B1]: %o, in J[2]? %o\n", Q5, Q5 in J2;

// g6 = (x-y)^2+z^2 = (t-u)^2+1
g6 := (elt_t-elt_u)^2 + 1;
Bg6 := HalfPositive(Divisor(g6));
Q6 := (Bg6 - ref) @@ m;
printf "Q6 = [(x-y)^2+z^2 tangency - 2B1]: %o, in J[2]? %o\n", Q6, Q6 in J2;

print "";
print "=== WHICH CLASSES ARE IN V_rat? ===";
printf "Q1 in V_rat? %o  (Q1 = %o)\n", Q1 in V_rat, Q1;
printf "Q2 in V_rat? %o  (Q2 = %o)\n", Q2 in V_rat, Q2;
printf "Q3 in V_rat? %o  (Q3 = %o)\n", Q3 in V_rat, Q3;
printf "Q4 in V_rat? %o  (Q4 = %o)\n", Q4 in V_rat, Q4;
printf "Q5 in V_rat? %o  (Q5 = %o)\n", Q5 in V_rat, Q5;
printf "Q6 in V_rat? %o  (Q6 = %o)\n", Q6 in V_rat, Q6;

// Full subgroup from ALL constructions (projected to J[2])
V_all := sub<Cl | P12, P13, Q1, Q2, Q3, Q4, Q5, Q6>;
V_all_J2 := V_all meet J2;
printf "\nAll Q-descending classes generate subgroup of J[2] of order %o\n", #V_all_J2;
printf "J[2] has order %o\n", #J2;

if #V_all_J2 eq #J2 then
    print "=> ALL of J[2](Q) is in ker(ob). BRAUER OBSTRUCTION = 0.";
else
    printf "=> Only %o/%o of J[2](Q) accounted for.\n", #V_all_J2, #J2;
    print "=> The remaining direction MAY have nonzero Brauer obstruction.";
    // Find a representative of the missing direction
    for g in J2 do
        if not (g in V_all_J2) then
            printf "Missing class example: %o\n", g;
            break;
        end if;
    end for;
end if;

quit;
