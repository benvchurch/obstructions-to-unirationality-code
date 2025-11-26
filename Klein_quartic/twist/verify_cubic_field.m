/* Verify that 7t^3 - 21t^2 + 14t - 1 defines Q(cos(2pi/7))
   and check isomorphism of C and C_twist over that field.
*/

Q := Rationals();
Qx<t> := PolynomialRing(Q);

// Our polynomial from the Groebner basis analysis
f := 7*t^3 - 21*t^2 + 14*t - 1;
print "=== POLYNOMIAL ANALYSIS ===";
print "f =", f;
print "Discriminant of f:", Discriminant(f);
print "Is f irreducible?", IsIrreducible(f);

// The standard minimal polynomial of cos(2pi/7)
// cos(2pi/7) satisfies 8x^3 + 4x^2 - 4x - 1 = 0
g := 8*t^3 + 4*t^2 - 4*t - 1;
print "\nMinimal polynomial of cos(2pi/7): g =", g;
print "Discriminant of g:", Discriminant(g);

// Define the number fields
K1<a> := NumberField(f);
K2<b> := NumberField(g);

print "\n=== NUMBER FIELD COMPARISON ===";
print "K1 = Q[t]/(f):  discriminant =", Discriminant(K1);
print "K2 = Q[t]/(g):  discriminant =", Discriminant(K2);

iso, mp := IsIsomorphic(K1, K2);
print "Are K1 and K2 isomorphic?", iso;
if iso then
    print "Isomorphism: a maps to", mp(a);
end if;

// Also check: is K1 contained in Q(zeta_7)?
print "\n=== EMBEDDING IN Q(zeta_7) ===";
Qz<z> := CyclotomicField(7);
print "Q(zeta_7) has degree", Degree(Qz);
hasroot, r := HasRoot(f, Qz);
print "Does f have a root in Q(zeta_7)?", hasroot;
if hasroot then
    print "Root:", r;
    // Express in terms of zeta_7
    print "Check: this root should equal something like (zeta + zeta^-1 + c)/d";
    // cos(2pi/7) = (zeta_7 + zeta_7^6)/2 = (z + z^(-1))/2
    cos_val := (z + z^6)/2;  // z^6 = z^(-1) in Z/7Z
    print "cos(2pi/7) =", cos_val;
    print "g(cos(2pi/7)) =", 8*cos_val^3 + 4*cos_val^2 - 4*cos_val - 1;
    print "f(root) =", 7*r^3 - 21*r^2 + 14*r - 1;
end if;

// Now define the curves over K1 and check isomorphism
print "\n=== CURVES OVER THE CUBIC FIELD ===";
P2K<x,y,z> := ProjectiveSpace(K1, 2);
C := Curve(P2K, x^3*y + y^3*z + z^3*x);
C_tw := Curve(P2K, x^4 + y^4 + z^4 + 6*(x*y^3 + y*z^3 + z*x^3)
               - 3*(x^2*y^2 + y^2*z^2 + z^2*x^2) + 3*x*y*z*(x+y+z));

print "C:", C;
print "C_tw:", C_tw;
print "Genus of C:", Genus(C);
print "Genus of C_tw:", Genus(C_tw);

// Try IsIsomorphic for plane curves
print "\nTrying IsIsomorphic...";
try
    iso_curves, phi := IsIsomorphic(C, C_tw);
    print "IsIsomorphic result:", iso_curves;
    if iso_curves then
        print "Isomorphism:", phi;
    end if;
catch e
    print "IsIsomorphic failed:", e`Object;
    print "Will try via function fields or Jacobians instead.";
end try;

// Alternative: compare via hyperelliptic models or function fields
print "\n=== TRYING VIA FUNCTION FIELDS ===";
try
    FC := FunctionField(C);
    FCtw := FunctionField(C_tw);
    iso_ff, phi_ff := IsIsomorphic(FC, FCtw);
    print "Function fields isomorphic?", iso_ff;
    if iso_ff then
        print "Isomorphism:", phi_ff;
    end if;
catch e
    print "Function field approach failed:", e`Object;
end try;

// =====================================================
// STEP 3: Construct the transformation explicitly
// Use the circulant matrix M with entries from K1
// and solve f_tw(Mv) = lambda * f_C(v)
// =====================================================
print "\n=== EXPLICIT CIRCULANT TRANSFORMATION OVER K1 ===";

// From GB analysis: the key relation is 7*t^3 - 21*t^2 + 14*t - 1 = 0
// where t = a2^4/lam. So we can parametrize by a2.
// Set a2 = 1 (scaling freedom), then lam satisfies 7 - 21*lam + 14*lam^2 - lam^3 = 0
// Wait, let me re-derive. If t = a2^4/lam, then lam = a2^4/t.
// With a2=1, lam = 1/t = 1/a where a is a root of f.

// Actually let's just solve the system over K1 directly.
R4<a0,a1,a2,lam> := PolynomialRing(K1, 4);
S3<X,Y,Z> := PolynomialRing(R4, 3);

u := a0*X + a1*Y + a2*Z;
v := a2*X + a0*Y + a1*Z;
w := a1*X + a2*Y + a0*Z;

LHS := u^4 + v^4 + w^4 + 6*(u*v^3 + v*w^3 + w*u^3)
       - 3*(u^2*v^2 + v^2*w^2 + w^2*u^2) + 3*u*v*w*(u+v+w);
RHS := lam * (X^3*Y + Y^3*Z + Z^3*X);
FF := LHS - RHS;

coeffs_eq := Coefficients(FF);
I := ideal<R4 | coeffs_eq>;

// Try to specialize: set a2=1 and use the relation a = root of 7t^3-21t^2+14t-1
// From the GB, lam should be 1/a (up to scaling)
// Let's try a0 and a1 as functions of a (the generator of K1)
// and solve the linear system

print "Setting up specialized system with a2=1...";
R3<b0,b1,mu> := PolynomialRing(K1, 3);
S3b<X2,Y2,Z2> := PolynomialRing(R3, 3);

u2 := b0*X2 + b1*Y2 + 1*Z2;
v2 := 1*X2 + b0*Y2 + b1*Z2;
w2 := b1*X2 + 1*Y2 + b0*Z2;

LHS2 := u2^4 + v2^4 + w2^4 + 6*(u2*v2^3 + v2*w2^3 + w2*u2^3)
       - 3*(u2^2*v2^2 + v2^2*w2^2 + w2^2*u2^2) + 3*u2*v2*w2*(u2+v2+w2);
RHS2 := mu * (X2^3*Y2 + Y2^3*Z2 + Z2^3*X2);
FF2 := LHS2 - RHS2;

coeffs2, mons2 := CoefficientsAndMonomials(FF2);
print "Number of equations with a2=1:", #coeffs2;

I2 := ideal<R3 | coeffs2>;
print "Computing Groebner basis over K1...";
time GB2 := GroebnerBasis(I2);
print "GB has", #GB2, "elements";
for g in GB2 do
    print "  ", g;
end for;

quit;
