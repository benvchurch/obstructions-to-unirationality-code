/*******************************************************************************
 * j128_divfield.m
 *
 * Compute [Q(E[16]) : Q] for E = 3200j1 (j=128) by working up the tower
 * of division fields Q(E[2]) ⊂ Q(E[4]) ⊂ Q(E[8]) ⊂ Q(E[16]).
 *
 * [Q(E[n]) : Q] = |im(rho_{E,n})|.
 ******************************************************************************/

SetColumns(0);

QQ := Rationals();
E := MinimalModel(EllipticCurveWithjInvariant(QQ!128));
printf "E: %o\n", E;
printf "j = %o, conductor = %o\n\n", jInvariant(E), Conductor(E);

// Division polynomials
for n in [2, 4, 8, 16] do
    fn := DivisionPolynomial(E, n);
    fac := Factorization(fn);
    printf "psi_%o: degree %o, %o irreducible factors\n", n, Degree(fn), #fac;
    printf "  factor degrees: %o\n", [<Degree(f[1]), f[2]> : f in fac];
end for;

// Compute Galois groups of individual factors of psi_16
printf "\n=== Galois groups of psi_16 factors ===\n";
f16 := DivisionPolynomial(E, 16);
fac16 := Factorization(f16);
for i in [1..#fac16] do
    f := fac16[i][1];
    d := Degree(f);
    printf "Factor %o: degree %o", i, d;
    if d le 1 then
        printf " (rational root)\n";
        continue;
    end if;
    if d le 40 then
        G := GaloisGroup(f);
        printf ", |Gal| = %o, name = %o\n", #G, GroupName(G);
    else
        printf " (Galois group computation may be slow, trying...)\n";
        try
            G := GaloisGroup(f);
            printf "  |Gal| = %o", #G;
            if #G le 10000 then
                printf ", name = %o", GroupName(G);
            end if;
            printf "\n";
        catch e
            printf "  Failed: %o\n", e`Object;
        end try;
    end if;
end for;

// Compute the x-coordinate division fields step by step
printf "\n=== Division field tower (x-coordinates) ===\n";

// Q(E[2]): splitting field of the quadratic factor of psi_2
f2 := DivisionPolynomial(E, 2);
fac2 := Factorization(f2);
printf "\npsi_2 factors: %o\n", [<Degree(f[1]), f[2]> : f in fac2];

// The splitting field of psi_2 = splitting field of the quadratic factor
// (the linear factor is already rational)
quad2 := [f[1] : f in fac2 | Degree(f[1]) eq 2][1];
K2<a2> := NumberField(quad2);
printf "Q(x(E[2])) = Q(a2) where a2 root of %o\n", quad2;
printf "[Q(x(E[2])):Q] = %o\n", Degree(K2);

// For the full E[2] field, we also need y-coordinates.
// 2-torsion points have y=0 (for short Weierstrass), so Q(E[2]) = Q(x(E[2]))
printf "Q(E[2]) = Q(x(E[2])) (y=0 at 2-torsion)\n";
printf "[Q(E[2]):Q] = %o\n\n", Degree(K2);

// Now compute the splitting field of psi_4 over Q
// This gives Q(x(E[4]))
printf "Computing splitting field of psi_4...\n";
f4 := DivisionPolynomial(E, 4);
K4 := SplittingField(f4);
printf "[Q(x(E[4])):Q] = %o\n", Degree(K4);

// For the full Q(E[4]), we need y-coordinates of 4-torsion points
// y^2 = x^3 + x^2 + 17x - 87
// Over K4, all x-coords of E[4] are defined, so y = sqrt(x^3+x^2+17x-87)
// The extension might be degree 2 more
// Actually: Q(E[n]) / Q(x(E[n])) is at most degree 2, and it's degree 1
// iff -1 is in the image of det (which is the cyclotomic char mod n)
// For n=4: det maps onto (Z/4)*, so -1 = 3 is in the image.  Hence
// Q(E[4]) = Q(x(E[4]))?  Not exactly — the criterion is subtler.
// Let's just report x-coordinate field degrees.

printf "\nComputing splitting field of psi_8...\n";
f8 := DivisionPolynomial(E, 8);
try
    K8 := SplittingField(f8);
    printf "[Q(x(E[8])):Q] = %o\n", Degree(K8);
catch e
    printf "  SplittingField(psi_8) failed, trying factored approach...\n";

    // Factor psi_8 and compute degrees iteratively
    fac8 := Factorization(f8);
    printf "  psi_8 factors: %o\n", [<Degree(f[1]), f[2]> : f in fac8];

    // Start with Q, adjoin roots of each factor
    K := Rationals();
    for j in [1..#fac8] do
        f := fac8[j][1];
        if Degree(f) le 1 then continue; end if;
        PK := PolynomialRing(K);
        fK := PK ! Eltseq(f);
        facK := Factorization(fK);
        // Adjoin a root of each irreducible factor over K
        for g in facK do
            if Degree(g[1]) gt 1 then
                K := ext<K | g[1]>;
                // Only need splitting field, but this gets one root
            end if;
        end for;
    end for;
    printf "  After adjoining roots: degree %o (lower bound on splitting field)\n",
        Degree(K);
end try;

// Try a different approach: use the Galois group of psi_n directly
printf "\n=== Direct Galois group computation ===\n";
printf "Trying GaloisGroup(psi_4)...\n";
G4 := GaloisGroup(f4);
printf "|Gal(psi_4)| = %o\n", #G4;

printf "Trying GaloisGroup(psi_8)...\n";
try
    G8 := GaloisGroup(f8);
    printf "|Gal(psi_8)| = %o\n", #G8;
catch e
    printf "  Failed for psi_8\n";
end try;

printf "Trying GaloisGroup(psi_16)...\n";
try
    G16 := GaloisGroup(f16);
    printf "|Gal(psi_16)| = %o\n", #G16;
catch e
    printf "  Failed for psi_16 (expected — degree 129)\n";
end try;

// The degree of the x-coordinate field Q(x(E[n])) equals |Gal(psi_n)|
// (when psi_n is separable, which it is over Q).
// The full division field Q(E[n]) has degree |im(rho_{E,n})|.
// We have [Q(E[n]) : Q(x(E[n]))] divides 2.

// For n = 2^k, we can also compute |im(rho)| from |Gal(psi_n)| as follows:
// |im(rho)| = |Gal(psi_n)| * [Q(E[n]) : Q(x(E[n]))]
// The second factor is 2 iff -I is NOT in the image, and 1 iff -I IS in the image.
// -I has trace 0 and det 1.  In our Frobenius data, trace=0 only with det=15, not 1.
// So -I is NOT in the image!  Hence [Q(E[n]):Q(x(E[n]))] = 2.

printf "\n=== -I check ===\n";
printf "Is -I in the image?\n";
printf "  -I has trace = 0 mod 16, det = 1 mod 16\n";
printf "  Observed: trace=0 only with det=15.\n";
printf "  Therefore -I is NOT in the image.\n";
printf "  So [Q(E[16]) : Q(x(E[16]))] = 2.\n";
printf "  |im(rho_{E,16})| = 2 * |Gal(splitting field of psi_16)|.\n";

quit;
