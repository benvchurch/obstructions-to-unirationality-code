/*******************************************************************************
 * brauer_obstruction3.m
 *
 * For the Fermat quartic C: x^4+y^4+z^4 = 0, detect the Brauer obstruction
 * by comparing Pic(C)(Q)[2] with J[2](Q) = Pic^0(C_Qbar)^{Gal}[2].
 *
 * Approach: over each F_p, the unramified Z/2Z-covers of C correspond to
 * elements of J(F_p)[2]. If a cover descends to Q, it gives a genus 5 curve
 * D/Q, and #D(F_p) is determined by which F_p-points of C split in D.
 *
 * Key observation: if L ∈ J[2](Q) but L ∉ Pic(C)(Q), then the Z/2Z-cover
 * classified by L does NOT exist as a Q-curve. We can detect this by
 * examining the function field: an unramified quadratic extension of Q(C)
 * exists iff the corresponding 2-torsion line bundle descends.
 ******************************************************************************/

// =============================================================================
// STEP 1: Compute Pic^0(C)(Q) using Magma's Jacobian machinery
// For smooth plane quartics, Magma can sometimes compute the rational points
// of the Jacobian directly.
// =============================================================================
print "=== FERMAT QUARTIC JACOBIAN ===";
Q := Rationals();
P2<x,y,z> := ProjectiveSpace(Q, 2);
C := Curve(P2, x^4 + y^4 + z^4);
print "C:", DefiningPolynomial(C);
print "Genus:", Genus(C);
print "Is smooth:", IsNonSingular(C);

// Try to compute the Jacobian and its rational torsion
// For plane quartics, we may need the function field approach
print "\n--- Function field approach ---";

// Affine model: set z=1, get x^4 + y^4 + 1 = 0
// Function field: Q(t)[u]/(u^4 + t^4 + 1)
Qt<t> := FunctionField(Q);
Qtu<u> := PolynomialRing(Qt);
f := u^4 + t^4 + 1;
print "Affine equation: u^4 + t^4 + 1 = 0";
print "Irreducible over Q(t)?", IsIrreducible(f);

// =============================================================================
// STEP 2: Over finite fields, compute the unramified quadratic extensions
// of the function field of C. These correspond to Pic^0(C/F_p)[2].
// =============================================================================
print "\n=== UNRAMIFIED QUADRATIC EXTENSIONS OVER F_p ===";
print "For each p, count elements of function field class group of order 2.";
print "These are the 2-torsion line bundles that EXIST over F_p.";
print "Compare with J(F_p)[2] (Galois-invariant geometric 2-torsion).";
print "";

printf "%-5o %-8o %-10o %-10o\n", "p", "p%8", "#J[2]", "2-rank";
for p in [3, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43] do
    Fp := GF(p);
    Fpt<tp> := FunctionField(Fp);
    Fptu<up> := PolynomialRing(Fpt);
    fp := up^4 + tp^4 + 1;

    if not IsIrreducible(fp) then
        printf "%-5o REDUCIBLE\n", p;
        continue;
    end if;

    FF := FunctionField(fp);
    Cl, m := ClassGroup(FF);
    invs := Invariants(Cl);

    // Count 2-torsion elements (excluding Z/0Z factor)
    two_tors := 0;
    for i in [1..#invs] do
        if invs[i] gt 0 and invs[i] mod 2 eq 0 then
            two_tors +:= 1;
        end if;
    end for;
    n_two_tors := 2^two_tors - 1;

    printf "%-5o %-8o %-10o %-10o\n", p, p mod 8, n_two_tors, two_tors;
end for;

// =============================================================================
// STEP 3: Try to detect the obstruction via the Picard group
// Over Q, try to find elements of Pic^0(C)(Q)[2] directly.
//
// A degree-0 divisor of order 2 on C/Q: D with 2D ~ 0 (linearly equivalent
// to 0). This means D = div(f) for some rational function f on C with f^2
// constant (up to scaling).
//
// For the Fermat quartic: try specific rational functions.
// =============================================================================
print "\n=== SEARCHING FOR RATIONAL 2-TORSION LINE BUNDLES ===";
print "A 2-torsion element of Pic^0(C)(Q) is a rational function f on C";
print "such that div(f) has degree 0 and 2*div(f) ~ 0, i.e., f^2 = c*g^2";
print "for some rational function g and constant c.";
print "";

// The obvious rational functions on C are restrictions of polynomials in x,y,z.
// Consider the function x/y (well-defined away from y=0):
// div(x/y) on C: zeros where x=0, poles where y=0.
// x=0 on C: y^4+z^4=0, so (y/z)^4 = -1. Over Q, this has no rational roots.
// The divisor of x/y has degree 0 (4 zeros, 4 poles).
// Is 2*div(x/y) ~ 0? That would mean (x/y)^2 = x^2/y^2 is a square of a
// rational function times a constant, which is trivially true.
// Wait, that means div(x/y) is NOT 2-torsion in general.

// Let me think about this differently.
// On C: x^4+y^4+z^4=0, consider the divisor D = (x=0)∩C - (y=0)∩C.
// This has degree 0. Is 2D ~ 0?
// 2D = 2(x=0)∩C - 2(y=0)∩C = div(x^2/y^2).
// So 2D = div(x^2/y^2) ~ 0. Yes! D is 2-torsion.
// And D = div(x/y) which is a principal divisor, so D ~ 0.
// Hmm, that means D = 0 in Pic(C).

// Actually: div(x/y) = (x=0)∩C - (y=0)∩C, which IS a principal divisor.
// So this is the trivial class.

// Let me try: D = (x=0)∩C. This has degree 4 (intersection of line with quartic).
// Over Q, x=0 meets C in y^4+z^4=0, which is a single degree-4 closed point.
// So D is a degree-4 effective divisor defined over Q.
// D - 4*(something) would give degree 0, but we need a degree-4 reference.

// The canonical divisor K_C = O_C(1) has degree 4.
// So D - K_C ∈ Pic^0(C)(Q). Is this 2-torsion?
// 2(D - K_C) = 2D - 2K_C = (x=0)^2∩C - 2K_C.
// (x=0)^2∩C = div(x^2/z^2) + 2K_C? Hmm, not sure.

// Let me try a more computational approach.
// Use the symmetries of C to find 2-torsion.

// C has S_3 symmetry: permuting x,y,z.
// And (x:y:z) -> (ix:y:z) etc. over Q(i).
// Over Q: (x:y:z) -> (-x:y:z) is an involution.
// The fixed locus of (-x:y:z): x=0, giving y^4+z^4=0.

// Consider the involutions sigma_1: (x:y:z) -> (-x:y:z) and
// sigma_2: (x:y:z) -> (x:-y:z).
// The quotient C/sigma_1 is a curve of genus... let me compute.

print "--- Involutions of the Fermat quartic ---";
print "sigma_1: (x:y:z) -> (-x:y:z)";
print "sigma_2: (x:y:z) -> (x:-y:z)";
print "sigma_3: (x:y:z) -> (x:y:-z)";
print "";
print "These are defined over Q (since -1 ∈ Q).";
print "sigma_1*sigma_2 = (x:y:z) -> (-x:-y:z) (also an involution)";
print "sigma_1*sigma_3 = (x:y:z) -> (-x:y:-z)";
print "sigma_2*sigma_3 = (x:y:z) -> (x:-y:-z)";
print "";
print "The group generated by sigma_1, sigma_2, sigma_3 modulo";
print "the relation sigma_1*sigma_2*sigma_3 = id (in PGL_3) is (Z/2Z)^2.";
print "";

// Actually, in PGL_3: (-x:y:z) = (x:-y:-z) (multiply by -1).
// So sigma_1 = sigma_2*sigma_3 in PGL_3!
// The group of sign changes modulo scalars is (Z/2Z)^2,
// generated by sigma_1 and sigma_2 (with sigma_3 = sigma_1*sigma_2).

// Fixed points of sigma_1 = (-x:y:z): either x=0 or (y,z)=(0,0).
// On C: x=0 gives y^4+z^4=0 (4 points over Q(zeta_8)).
// (y,z)=(0,0) gives (1:0:0), check: 1+0+0=1≠0, not on C.
// So sigma_1 has no fixed points on C(Q̄)... wait, x=0 gives 4 points
// where y^4+z^4=0, so (y/z)^4=-1, giving 4 points. These ARE fixed by sigma_1.
// Hmm wait: sigma_1(0:y:z) = (0:y:z) = (0:y:z). Yes, these are fixed.

// Actually, for an involution with 4 fixed points on a genus 3 curve:
// Hurwitz: 2*3-2 = 2(2g'-2) + 4, so 4 = 4g'-4+4 = 4g', g'=1.
// So C/sigma_1 has genus 1!

print "C/sigma_1 has genus 1 (Hurwitz: 4 fixed points on genus 3).";
print "C/sigma_2 has genus 1 similarly.";
print "These give 2-isogenies J(C) -> J(C/sigma_i) x ...";

// =============================================================================
// STEP 4: Compute the quotient curves
// C/sigma_1 where sigma_1: (x:y:z) -> (-x:y:z).
// Invariant functions: x^2, y, z (and xy, xz).
// Set u = x^2/z^2, v = y/z: then u^2 + v^4 + 1 = 0... wait:
// x^4/z^4 + y^4/z^4 + 1 = 0, so (x^2/z^2)^2 + (y/z)^4 + 1 = 0.
// Setting u = x^2/z^2, w = y/z: u^2 + w^4 + 1 = 0.
// This is a genus 1 curve (quartic in weighted P(2,1,1)... or affine genus 1).
// =============================================================================
print "\n--- Quotient curve C/sigma_1 ---";
print "Invariants: u = x^2, v = y, w = z (in suitable coords)";
print "Equation: u^2 + v^4 + w^4 = 0 in weighted P(2,1,1)";
print "Affine: u^2 + v^4 + 1 = 0  (set w=1)";
print "";

// Can also write this as: u^2 = -(v^4+1)
// This is a hyperelliptic curve of genus 1 (degree 4 in v, double cover via u)
// Points: need u^2 = -(v^4+1). Over R: RHS < 0 always, so u^2 < 0. No real points.
// Hence E1 = C/sigma_1 also has no real points.
print "E1: u^2 = -(v^4+1)";
print "E1(R) = empty (RHS always negative). So E1 is a genus 1 curve with no real points.";
print "E1 is a torsor under its Jacobian.";
print "";

// Similarly for sigma_2:
// Invariants: x, y^2, z -> u = x/z, w = y^2/z^2
// u^4 + w^2 + 1 = 0, i.e., w^2 = -(u^4+1)
// Same equation! So C/sigma_2 ≅ C/sigma_1 = E1.

print "C/sigma_2: same equation w^2 = -(u^4+1). So C/sigma_2 ≅ E1.";
print "";

// For sigma_1*sigma_2 = (-x:-y:z) = (x:y:-z) = sigma_3:
// Invariants: x, y, z^2 -> u=x/y, w=z^2/y^2 (or similar)
// (x/y)^4 + 1 + (z/y)^4 = 0, with w = z^2/y^2:
// (x/y)^4 + 1 + w^2 = 0, so w^2 = -((x/y)^4 + 1)
// Same equation again!

print "C/sigma_3: also w^2 = -(u^4+1). All three quotients are isomorphic.";

// =============================================================================
// STEP 5: Identify the Jacobian of E1: u^2 = -(v^4+1)
// This is a genus 1 curve. Find its Jacobian (= the elliptic curve it's a torsor of).
// Substitute: u^2 = -v^4 - 1. Let V = v^2, U = u:
// U^2 = -V^2 - 1 (a conic, genus 0). Not helpful.
// Instead: u^2 + v^4 + 1 = 0 is a double cover of P^1 branched at v^4+1=0.
// The branch points are the roots of v^4 = -1, i.e., v = zeta_8 * (-1)^{1/4}.
// The j-invariant and the Jacobian can be computed from the branch points.
// =============================================================================
print "\n=== JACOBIAN OF E1: u^2 = -(v^4+1) ===";

// Write as y^2 = -(x^4+1) = -x^4-1
// This is a genus 1 curve. Magma can compute the Jacobian.
A2<xx,yy> := AffineSpace(Q, 2);
E1_aff := Curve(A2, yy^2 + xx^4 + 1);
print "E1 affine:", DefiningPolynomial(E1_aff);
print "Genus:", Genus(E1_aff);

// Try to find the elliptic curve
// y^2 = -x^4 - 1. Substituting x = 1/t, y = s/t^2:
// s^2/t^4 = -1/t^4 - 1, so s^2 = -1 - t^4.
// Same curve. Let me try Magma's built-in.
try
    P1<X,Z> := ProjectiveSpace(Q, 1);
    HC := HyperellipticCurve(-Polynomial([1,0,0,0,1]));
    // y^2 = -(x^4+1)
    print "Hyperelliptic model:", HC;
    J1 := Jacobian(HC);
    print "Jacobian:", J1;
catch e
    print "Error with hyperelliptic:", e`Object;
end try;

// Alternative: use the quartic model
// y^2 = f(x) with f = -x^4-1 (degree 4, leading coeff negative)
// Standard form: y^2 = x^4+1 (twist by -1)
try
    HC2 := HyperellipticCurve(Polynomial([-1,0,0,0,-1]));
    print "HC2:", HC2;
    J2 := Jacobian(HC2);
    print "Jacobian of y^2 = -x^4-1:", J2;

    // Try to get the elliptic curve from this genus 1 curve
    // The Jacobian of a genus 1 hyperelliptic curve is an elliptic curve
    E_jac := EllipticCurve(J2);
    print "Elliptic curve:", E_jac;
    print "a-invariants:", aInvariants(E_jac);
    cm, d := HasComplexMultiplication(E_jac);
    if cm then printf "CM discriminant: %o\n", d; end if;
catch e
    print "Error:", e`Object;
end try;

// =============================================================================
// STEP 6: Check the index of C (smallest degree of a rational divisor)
// If index = 4, all rational divisors have degree divisible by 4.
// If index = 2, there's a degree-2 divisor (C has a degree-2 closed point).
// =============================================================================
print "\n=== INDEX OF C ===";
print "The canonical class K_C = O_C(1) has degree 4 = 2g-2.";
print "Any line meets C in degree 4. Any conic meets C in degree 8.";
print "Index divides gcd(4, 8, ...) = 4.";
print "";
print "Does C have degree-2 closed points?";
print "A degree-2 point = a quadratic extension K with C(K) ≠ empty.";

// Check C over quadratic fields Q(sqrt(d)) for small d
print "\nChecking C over Q(sqrt(d)):";
for d in [-1, -2, -3, 2, 3, 5, -5, -7, 6, -6, 7, 10, -10, 13, -13, -15, 17] do
    K<w> := QuadraticField(d);
    P2K<xK,yK,zK> := ProjectiveSpace(K, 2);
    CK := Curve(P2K, xK^4 + yK^4 + zK^4);

    // Try to find points with small coordinates
    found := false;
    for a in [0..5] do
        for b in [0..5] do
            for c in [0..5] do
                for e in [-5..5] do
                    for f in [-5..5] do
                        for g in [-5..5] do
                            xx := a + e*w;
                            yx := b + f*w;
                            zx := c + g*w;
                            if not (xx eq 0 and yx eq 0 and zx eq 0) then
                                if xx^4 + yx^4 + zx^4 eq 0 then
                                    printf "  d=%o: FOUND (%o : %o : %o)\n", d, xx, yx, zx;
                                    found := true;
                                    break e;
                                end if;
                            end if;
                        end for;
                        if found then break f; end if;
                    end for;
                    if found then break; end if;
                end for;
                if found then break; end if;
            end for;
            if found then break; end if;
        end for;
        if found then break; end if;
    end for;

    if not found then
        printf "  d=%o: no small points found\n", d;
    end if;
end for;

quit;
