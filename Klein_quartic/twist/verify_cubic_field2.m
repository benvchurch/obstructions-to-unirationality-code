/* Further analysis:
   1. Check that C and C_twist are NOT isomorphic over Q
   2. Verify the isomorphism is not defined over any quadratic subfield
   3. Factor the mu polynomial over K1
   4. Understand the degree-4 map (is it a linear change of coords times something?)
*/

Q := Rationals();
Qx<t> := PolynomialRing(Q);
f := 7*t^3 - 21*t^2 + 14*t - 1;
K1<a> := NumberField(f);

// 1. Are C and C_twist isomorphic over Q?
print "=== ISOMORPHISM OVER Q ===";
P2Q<x,y,z> := ProjectiveSpace(Q, 2);
CQ := Curve(P2Q, x^3*y + y^3*z + z^3*x);
CtwQ := Curve(P2Q, x^4 + y^4 + z^4 + 6*(x*y^3 + y*z^3 + z*x^3)
               - 3*(x^2*y^2 + y^2*z^2 + z^2*x^2) + 3*x*y*z*(x+y+z));

try
    iso_Q, phi_Q := IsIsomorphic(CQ, CtwQ);
    print "Isomorphic over Q?", iso_Q;
catch e
    print "IsIsomorphic over Q failed:", e`Object;
end try;

// 2. Check over quadratic fields Q(sqrt(-7)), Q(sqrt(-3)), Q(sqrt(7))
print "\n=== ISOMORPHISM OVER QUADRATIC FIELDS ===";
quads := [<-7, "Q(sqrt(-7))">, <-3, "Q(sqrt(-3))">, <7, "Q(sqrt(7))">,
          <-1, "Q(i)">, <21, "Q(sqrt(21))">, <-21, "Q(sqrt(-21))">];
for pair in quads do
    d := pair[1]; name := pair[2];
    Kq<s> := QuadraticField(d);
    P2K<x,y,z> := ProjectiveSpace(Kq, 2);
    Cq := Curve(P2K, x^3*y + y^3*z + z^3*x);
    Ctwq := Curve(P2K, x^4 + y^4 + z^4 + 6*(x*y^3 + y*z^3 + z*x^3)
                   - 3*(x^2*y^2 + y^2*z^2 + z^2*x^2) + 3*x*y*z*(x+y+z));
    try
        iso_q, _ := IsIsomorphic(Cq, Ctwq);
        printf "%o: isomorphic? %o\n", name, iso_q;
    catch e
        printf "%o: error — %o\n", name, e`Object;
    end try;
end for;

// 3. Factor the mu polynomial over K1
print "\n=== MU POLYNOMIAL OVER K1 ===";
R<mu> := PolynomialRing(K1);
h := mu^4 - 686*mu^3 + 50421*mu^2 - 823543*mu;
print "h =", h;
fac := Factorization(h);
print "Factorization:";
for pair in fac do
    print "  ", pair[1], "  (multiplicity", pair[2], ")";
end for;

// 4. Understand the nature of the isomorphism
print "\n=== DETAILED ISOMORPHISM ANALYSIS ===";
P2K<x,y,z> := ProjectiveSpace(K1, 2);
C := Curve(P2K, x^3*y + y^3*z + z^3*x);
C_tw := Curve(P2K, x^4 + y^4 + z^4 + 6*(x*y^3 + y*z^3 + z*x^3)
               - 3*(x^2*y^2 + y^2*z^2 + z^2*x^2) + 3*x*y*z*(x+y+z));

iso, phi := IsIsomorphic(C, C_tw);
print "Isomorphism equations:";
eqs := DefiningEquations(phi);
for i in [1..#eqs] do
    printf "  Component %o: %o\n", i, eqs[i];
end for;

// Check: is the isomorphism a 4-uple embedding composed with projection?
// For plane curves of the SAME degree, an isomorphism should be a projective
// linear transformation (degree 1). But C has degree 3 and C_tw has degree 4!
// Actually wait — both are plane quartics? No: C is degree 3 (Klein quartic is
// degree 3+1=4? Let me check).
print "\nDegree of C:", Degree(C);
print "Degree of C_tw:", Degree(C_tw);

// Ah right — C: x^3*y + y^3*z + z^3*x is degree 4, and C_tw is degree 4.
// So both are plane quartics and an isomorphism of plane quartics should come
// from a projective linear transformation (PGL_3) IF they're generic.
// But the map Magma returned has degree 4 components — this means Magma is
// giving a map C → P^2 of higher degree, not the simple linear one.
// Let's try to find a linear isomorphism directly.

print "\n=== SEARCHING FOR LINEAR ISOMORPHISM ===";
// A linear change of variables [x,y,z] -> M[x,y,z] sending C to C_tw
// means f_tw(Mx) = lambda * f_C(x) for some scalar lambda
// Let's solve this over K1 without the circulant restriction

R9<m11,m12,m13,m21,m22,m23,m31,m32,m33> := PolynomialRing(K1, 9);
S3<X,Y,Z> := PolynomialRing(R9, 3);

u := m11*X + m12*Y + m13*Z;
v := m21*X + m22*Y + m23*Z;
w := m31*X + m32*Y + m33*Z;

// f_C(u,v,w) should be proportional to f_tw(X,Y,Z)
// Klein quartic: u^3*v + v^3*w + w^3*u
// Actually, this is degree 4 in X,Y,Z. f_tw is also degree 4 in X,Y,Z.
// So we want f_C(Mv) = lambda * f_tw(v), i.e. (u^3*v + v^3*w + w^3*u) = lambda * f_tw(X,Y,Z)
// Actually degree: f_C is degree 4 (quartic), f_tw is degree 4. Both correct.

// Let's just try: can we use Magma's Automorphisms or some scheme-theoretic approach?
// Actually, let me try computing the automorphism group of C first.
print "Automorphism group of C over K1:";
try
    aut := AutomorphismGroup(C);
    print "  Order:", #aut;
catch e
    print "  Failed:", e`Object;
end try;

// Let's try the other direction: find the linear map more carefully
// using the circulant GB solution
print "\n=== SOLVING THE CIRCULANT GB OVER K1 ===";
// From the GB: mu^3 - 686*mu^2 + 50421*mu - 823543 factors over K1
// Let's get a root and back-solve for b0, b1
R1<mu> := PolynomialRing(K1);
cubic_mu := mu^3 - 686*mu^2 + 50421*mu - 823543;
print "cubic_mu =", cubic_mu;
fac_mu := Factorization(cubic_mu);
print "Factorization:", fac_mu;

// Pick a linear factor (root of mu)
if exists(i){i : i in [1..#fac_mu] | Degree(fac_mu[i][1]) eq 1} then
    lin := fac_mu[i][1];
    mu_val := -Coefficient(lin, 0) / Coefficient(lin, 1);
    print "mu_val =", mu_val;

    // From GB: b1*mu + 3/31213*mu^3 - 37/637*mu^2 + 23/13*mu = 0
    // => b1 = -(3/31213*mu^2 - 37/637*mu + 23/13)
    b1_val := -(3/31213*mu_val^2 - 37/637*mu_val + 23/13);
    print "b1 =", b1_val;

    // From GB: b0 + b1 - 2/1529437*mu^3 + 29/31213*mu^2 - 50/637*mu + 1 = 0
    // => b0 = -b1 + 2/1529437*mu^3 - 29/31213*mu^2 + 50/637*mu - 1
    b0_val := -b1_val + 2/1529437*mu_val^3 - 29/31213*mu_val^2 + 50/637*mu_val - 1;
    print "b0 =", b0_val;

    // The circulant matrix M = [[b0, b1, 1], [1, b0, b1], [b1, 1, b0]]
    M := Matrix(K1, 3, 3, [b0_val, b1_val, 1, 1, b0_val, b1_val, b1_val, 1, b0_val]);
    print "\nCirculant matrix M:";
    print M;
    print "det(M) =", Determinant(M);

    // Verify: f_tw(Mv) should equal mu_val * f_C(v)
    print "\n=== VERIFICATION ===";
    SK<X,Y,Z> := PolynomialRing(K1, 3);
    u := b0_val*X + b1_val*Y + 1*Z;
    v := 1*X + b0_val*Y + b1_val*Z;
    w := b1_val*X + 1*Y + b0_val*Z;

    f_tw_Mv := u^4 + v^4 + w^4 + 6*(u*v^3 + v*w^3 + w*u^3)
               - 3*(u^2*v^2 + v^2*w^2 + w^2*u^2) + 3*u*v*w*(u+v+w);
    f_C := X^3*Y + Y^3*Z + Z^3*X;

    check := f_tw_Mv - mu_val * f_C;
    print "f_tw(Mv) - mu*f_C(v) = 0?", check eq 0;

    if check ne 0 then
        print "Nonzero — trying other direction: f_C(Mv) = mu*f_tw(v)";
        f_C_Mv := u^3*v + v^3*w + w^3*u;
        f_tw_v := X^4 + Y^4 + Z^4 + 6*(X*Y^3 + Y*Z^3 + Z*X^3)
                   - 3*(X^2*Y^2 + Y^2*Z^2 + Z^2*X^2) + 3*X*Y*Z*(X+Y+Z);
        check2 := f_C_Mv - mu_val * f_tw_v;
        print "f_C(Mv) - mu*f_tw(v) = 0?", check2 eq 0;
    end if;
end if;

quit;
