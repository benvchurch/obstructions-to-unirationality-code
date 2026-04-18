/*******************************************************************************
 * j128_galrep.m
 *
 * Compute the image of the mod-16 Galois representation for the elliptic
 * curve with j=128, i.e., the image of Gal(Qbar/Q) -> GL_2(Z/16Z)
 * acting on E[16].
 ******************************************************************************/

SetColumns(0);

QQ := Rationals();

// Get a minimal model for j=128
E := MinimalModel(EllipticCurveWithjInvariant(QQ!128));
printf "Elliptic curve with j=128:\n  %o\n", E;
printf "  Conductor: %o\n", Conductor(E);
printf "  Discriminant: %o\n", Discriminant(E);
printf "  j-invariant: %o\n", jInvariant(E);
printf "  Cremona label: %o\n", CremonaReference(E);

// Torsion subgroup over Q
T, phi := TorsionSubgroup(E);
printf "  Torsion over Q: %o\n", T;

// Mod-2 representation
printf "\n=== Mod-2 Galois representation ===\n";
rho2 := GaloisRepresentation(E, 2);
printf "Type: %o\n", Type(rho2);

// Division polynomials for 2-power torsion
printf "\n=== Division polynomial approach ===\n";

// 2-division polynomial: roots are x-coords of E[2]\{O}
f2 := DivisionPolynomial(E, 2);
printf "Div poly psi_2: degree %o\n", Degree(f2);
printf "  %o\n", f2;
printf "  Factored: %o\n", Factorization(f2);

// 4-division polynomial
f4 := DivisionPolynomial(E, 4);
printf "\nDiv poly psi_4: degree %o\n", Degree(f4);
printf "  Factored degrees: %o\n", [<Degree(f[1]), f[2]> : f in Factorization(f4)];

// 8-division polynomial
f8 := DivisionPolynomial(E, 8);
printf "\nDiv poly psi_8: degree %o\n", Degree(f8);
fac8 := Factorization(f8);
printf "  Factored degrees: %o\n", [<Degree(f[1]), f[2]> : f in fac8];

// 16-division polynomial
printf "\nComputing psi_16...\n";
f16 := DivisionPolynomial(E, 16);
printf "Div poly psi_16: degree %o\n", Degree(f16);
fac16 := Factorization(f16);
printf "  Number of irreducible factors: %o\n", #fac16;
printf "  Factor degrees (with mult): %o\n", [<Degree(f[1]), f[2]> : f in fac16];

// The Galois group acts on the roots.  The factorization pattern
// already tells us about the image.  For GL_2(Z/16), the order is
// |GL_2(Z/16)| = 16^4 * (1-1/4) * (1-1/16)... let me compute it.
// Actually |GL_2(Z/2^k)| = 2^{4k} * prod(1-2^{-i}, i=1,2) for the
// GL_2(Z/2) part, times the kernel size.
// |GL_2(Z/16)| = |GL_2(Z/2)| * |ker(GL_2(Z/16)->GL_2(Z/2))|
//              = 6 * 2^{4*3} = 6 * 4096 = 24576?  No...
// |GL_2(Z/2^n)| = 2^{4n-3} * (2^2-1)(2^2-2) = 2^{4n-3} * 6
// For n=4: 2^{13} * 6 = 8192 * 6 = 49152

printf "\n|GL_2(Z/16)| = %o\n", 2^13 * 6;

// Now try to compute the actual Galois group of the 16-division field
// This is expensive but informative.
// The new 16-torsion x-coordinates (not already in lower levels) come from
// psi_16 / gcd(psi_16, psi_8).

printf "\n=== Galois groups of division fields ===\n";

// Q(E[2]): splitting field of psi_2
printf "\nQ(E[2]):\n";
G2 := GaloisGroup(f2);
printf "  Gal = %o, order %o\n", GroupName(G2), #G2;

// Q(E[4]): need splitting field of psi_4 (and y-coordinates)
// For now just look at x-coordinate field
printf "\nQ(x(E[4])): splitting field of psi_4\n";
// Factor psi_4 and look at the largest factor
for f in Factorization(f4) do
    if Degree(f[1]) gt 1 then
        printf "  Factor of degree %o", Degree(f[1]);
        if Degree(f[1]) le 20 then
            G := GaloisGroup(f[1]);
            printf ", Galois group: %o (order %o)", GroupName(G), #G;
        end if;
        printf "\n";
    else
        printf "  Linear factor: %o\n", f[1];
    end if;
end for;

printf "\nQ(x(E[8])): splitting field of psi_8\n";
for f in fac8 do
    if Degree(f[1]) gt 1 then
        printf "  Factor of degree %o", Degree(f[1]);
        if Degree(f[1]) le 24 then
            G := GaloisGroup(f[1]);
            printf ", Galois group: %o (order %o)", GroupName(G), #G;
        end if;
        printf "\n";
    end if;
end for;

printf "\nQ(x(E[16])): factors of psi_16\n";
for f in fac16 do
    if Degree(f[1]) gt 1 then
        printf "  Factor of degree %o", Degree(f[1]);
        if Degree(f[1]) le 32 then
            try
                G := GaloisGroup(f[1]);
                printf ", Galois group: %o (order %o)", GroupName(G), #G;
            catch e
                printf ", (Galois group computation skipped)";
            end try;
        end if;
        printf "\n";
    else
        printf "  Linear factor: %o\n", f[1];
    end if;
end for;

// Alternative: use Rouse-Zureick-Brown 2-adic image computation
// Magma V2.28 has TwoAdicImage for elliptic curves
printf "\n=== 2-adic image (Rouse-Zureick-Brown) ===\n";
try
    img := TwoAdicImage(E);
    printf "2-adic image label: %o\n", img;
catch e
    printf "TwoAdicImage not available: %o\n", e`Object;
end try;

// Also try modular degree and isogeny info
printf "\n=== Isogeny information ===\n";
isogs := Isogenies(E, 2);
printf "2-isogenies from E: %o\n", #isogs;
for iso in isogs do
    E2 := Codomain(iso);
    printf "  -> j=%o, conductor=%o\n", jInvariant(E2), Conductor(MinimalModel(E2));
end for;

isogs4 := Isogenies(E, 4);
printf "4-isogenies from E: %o\n", #isogs4;

quit;
