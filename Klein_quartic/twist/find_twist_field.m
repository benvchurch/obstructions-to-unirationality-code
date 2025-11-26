/*  Find the field over which C_twist becomes isomorphic to the Klein quartic C.
    Strategy:
      1. Compare L-polynomials to identify the twist character (Chebotarev)
      2. Solve for the transformation matrix (circulant ansatz + Groebner basis)
*/

Q := Rationals();
P2<x,y,z> := ProjectiveSpace(Q, 2);
C := Curve(P2, x^3*y + y^3*z + z^3*x);
C_tw := Curve(P2, x^4 + y^4 + z^4 + 6*(x*y^3 + y*z^3 + z*x^3)
               - 3*(x^2*y^2 + y^2*z^2 + z^2*x^2) + 3*x*y*z*(x+y+z));

// =====================================================
// STEP 1: L-polynomial comparison  (Chebotarev density)
// =====================================================
print "=== L-POLYNOMIAL COMPARISON ===";
same := [];
notsame := [];
for p in PrimesInInterval(5, 200) do
    try
        Cp := ChangeRing(C, GF(p));
        Ctp := ChangeRing(C_tw, GF(p));
        Lp := Numerator(ZetaFunction(Cp));
        Ltp := Numerator(ZetaFunction(Ctp));
        if Lp eq Ltp then Append(~same, p); else Append(~notsame, p); end if;
    catch e
        printf "p=%o: skipped (bad reduction)\n", p;
    end try;
end for;
print "Same L-poly:", same;
print "Diff L-poly:", notsame;

print "\nSAME primes — Kronecker symbols:";
for p in same do
    printf "  p=%3o: (-3/p)=%2o  (-7/p)=%2o  (-21/p)=%2o  mod7=%o  mod3=%o  mod21=%o\n",
        p, KroneckerSymbol(-3,p), KroneckerSymbol(-7,p), KroneckerSymbol(-21,p),
        p mod 7, p mod 3, p mod 21;
end for;
print "\nDIFF primes — Kronecker symbols:";
for p in notsame do
    printf "  p=%3o: (-3/p)=%2o  (-7/p)=%2o  (-21/p)=%2o  mod7=%o  mod3=%o  mod21=%o\n",
        p, KroneckerSymbol(-3,p), KroneckerSymbol(-7,p), KroneckerSymbol(-21,p),
        p mod 7, p mod 3, p mod 21;
end for;

// Check specific characters
print "\n=== CHARACTER ANALYSIS ===";
print "Does same L-poly <=> (-3/p)=1 ?";
ok := true;
for p in same do
    if KroneckerSymbol(-3,p) ne 1 then
        printf "  COUNTEREXAMPLE: p=%o has same L-poly but (-3/p)=%o\n", p, KroneckerSymbol(-3,p);
        ok := false;
    end if;
end for;
for p in notsame do
    if KroneckerSymbol(-3,p) ne -1 then
        printf "  COUNTEREXAMPLE: p=%o has diff L-poly but (-3/p)=%o\n", p, KroneckerSymbol(-3,p);
        ok := false;
    end if;
end for;
if ok then print "  YES — perfect match! Splitting field = Q(sqrt(-3))"; end if;

print "Does same L-poly <=> (-7/p)=1 ?";
ok := true;
for p in same do
    if KroneckerSymbol(-7,p) ne 1 then
        printf "  COUNTEREXAMPLE: p=%o has same L-poly but (-7/p)=%o\n", p, KroneckerSymbol(-7,p);
        ok := false;
    end if;
end for;
for p in notsame do
    if KroneckerSymbol(-7,p) ne -1 then
        printf "  COUNTEREXAMPLE: p=%o has diff L-poly but (-7/p)=%o\n", p, KroneckerSymbol(-7,p);
        ok := false;
    end if;
end for;
if ok then print "  YES — perfect match! Splitting field = Q(sqrt(-7))"; end if;

print "Does same L-poly <=> (-21/p)=1 ?";
ok := true;
for p in same do
    if KroneckerSymbol(-21,p) ne 1 then
        printf "  COUNTEREXAMPLE: p=%o has same L-poly but (-21/p)=%o\n", p, KroneckerSymbol(-21,p);
        ok := false;
    end if;
end for;
for p in notsame do
    if KroneckerSymbol(-21,p) ne -1 then
        printf "  COUNTEREXAMPLE: p=%o has diff L-poly but (-21/p)=%o\n", p, KroneckerSymbol(-21,p);
        ok := false;
    end if;
end for;
if ok then print "  YES — perfect match! Splitting field = Q(sqrt(-21))"; end if;

// Check p mod 7 pattern (cubic character)
print "\nDoes same L-poly <=> p is a cube mod 7 (i.e. p^2 ≡ 1 mod 7) ?";
ok := true;
for p in same do
    if (p mod 7 ne 0) and ((p^2 mod 7) ne 1) then
        printf "  COUNTEREXAMPLE: p=%o, p mod 7 = %o\n", p, p mod 7;
        ok := false;
    end if;
end for;
for p in notsame do
    if (p mod 7 ne 0) and ((p^2 mod 7) eq 1) then
        printf "  COUNTEREXAMPLE: p=%o, p mod 7 = %o\n", p, p mod 7;
        ok := false;
    end if;
end for;
if ok then print "  YES — perfect match! Twist involves cubic character mod 7"; end if;

// =====================================================
// STEP 2: Groebner basis — circulant transformation
// =====================================================
print "\n=== GROEBNER BASIS: f_tw(Mv) = lam*f_C(v), M circulant ===";
R<a0,a1,a2,lam> := PolynomialRing(Q, 4);
S<X,Y,Z> := PolynomialRing(R, 3);

u := a0*X + a1*Y + a2*Z;
v := a2*X + a0*Y + a1*Z;
w := a1*X + a2*Y + a0*Z;

LHS := u^4 + v^4 + w^4 + 6*(u*v^3 + v*w^3 + w*u^3)
       - 3*(u^2*v^2 + v^2*w^2 + w^2*u^2) + 3*u*v*w*(u+v+w);
RHS := lam * (X^3*Y + Y^3*Z + Z^3*X);
FF := LHS - RHS;

coeffs, mons := CoefficientsAndMonomials(FF);
print "Number of equations:", #coeffs;

I := ideal<R | coeffs>;
print "Computing Groebner basis...";
time GB := GroebnerBasis(I);
print "Groebner basis has", #GB, "elements:";
for g in GB do
    print "  ", g;
end for;

// Factor elements to find the splitting field
print "\nFactorizations of GB elements:";
for g in GB do
    facs := Factorization(g);
    print "  ", facs;
end for;

// =====================================================
// STEP 2b: Try the other direction: f_C(Mv) = lam*f_tw(v)
// =====================================================
print "\n=== GROEBNER BASIS: f_C(Mv) = lam*f_tw(v), M circulant ===";
LHS2 := u^3*v + v^3*w + w^3*u;
RHS2 := lam * (X^4 + Y^4 + Z^4 + 6*(X*Y^3 + Y*Z^3 + Z*X^3)
              - 3*(X^2*Y^2 + Y^2*Z^2 + Z^2*X^2) + 3*X*Y*Z*(X+Y+Z));
FF2 := LHS2 - RHS2;

coeffs2, mons2 := CoefficientsAndMonomials(FF2);
I2 := ideal<R | coeffs2>;
print "Computing Groebner basis (other direction)...";
time GB2 := GroebnerBasis(I2);
print "Groebner basis has", #GB2, "elements:";
for g in GB2 do
    print "  ", g;
end for;

print "\nFactorizations:";
for g in GB2 do
    print "  ", Factorization(g);
end for;

quit;
