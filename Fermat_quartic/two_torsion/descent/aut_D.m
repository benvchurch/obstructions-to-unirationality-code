/*******************************************************************************
 * aut_D.m
 *
 * Compute the full automorphism group of D, the genus 5 etale double cover
 * of the Fermat quartic C: u^4 + t^4 + 1 = 0, defined by v^2 = q1 where
 * q1 = 2t^2 + (1-w)u^2 + (1+w) with w = sqrt(-3).
 *
 * Work over F_p where sqrt(-3) exists (p = 1 mod 3).
 * Goal: determine |Aut(D)| and its structure.
 ******************************************************************************/

// Try several primes for consistency
primes := [13, 19, 31, 37, 43];

for p in primes do
    Fp := GF(p);
    if not IsSquare(Fp!(-3)) then continue; end if;
    w := Sqrt(Fp!(-3));
    printf "=== p = %o, sqrt(-3) = %o ===\n", p, w;

    // Function field of C: u^4 + t^4 + 1 = 0
    Fpt<t> := FunctionField(Fp);
    Ku<u> := PolynomialRing(Fpt);
    f_C := u^4 + t^4 + 1;

    // Check irreducibility
    if not IsIrreducible(f_C) then
        printf "  C reducible at p=%o, skipping\n\n", p;
        continue;
    end if;

    FC<uu> := FunctionField(f_C);
    printf "  Genus(C) = %o\n", Genus(FC);

    // q1 on C
    q1 := 2*(FC!t)^2 + (1-w)*uu^2 + (1+w);

    // Function field of D: v^2 = q1
    Kv<v> := PolynomialRing(FC);
    f_D := v^2 - q1;

    if not IsIrreducible(f_D) then
        printf "  D reducible at p=%o (q1 is a square on C), skipping\n\n", p;
        continue;
    end if;

    FD<vv> := FunctionField(f_D);
    printf "  Genus(D) = %o\n", Genus(FD);

    // Try to compute automorphism group
    printf "  Computing Aut(D)...\n";
    try
        A, mp, gens := AutomorphismGroup(FD);
        printf "  |Aut(D)| = %o\n", #A;
        printf "  Structure: %o\n", GroupName(A);
        printf "  Abelian? %o\n", IsAbelian(A);

        // Check orders of elements
        orders := {Order(a) : a in A};
        printf "  Element orders: %o\n", orders;

        // Check if there's an involution beyond the deck involution
        involutions := [a : a in A | Order(a) eq 2];
        printf "  Number of involutions: %o\n", #involutions;
    catch e
        printf "  AutomorphismGroup failed: %o\n", e`Object;

        // Alternative: try via simple extension
        printf "  Trying simple extension...\n";
        try
            // Get primitive element for FD/Fpt
            alpha := vv + uu;  // try uu + vv as primitive element
            minpoly := MinimalPolynomial(alpha, Fpt);
            printf "  deg(minpoly of u+v over F_p(t)) = %o\n", Degree(minpoly);

            if Degree(minpoly) eq 8 then
                Kx<x> := PolynomialRing(Fpt);
                FD2<aa> := FunctionField(Kx ! minpoly);
                printf "  Genus(D via simple ext) = %o\n", Genus(FD2);
                A2, mp2, gens2 := AutomorphismGroup(FD2);
                printf "  |Aut(D)| = %o\n", #A2;
                printf "  Structure: %o\n", GroupName(A2);
                printf "  Abelian? %o\n", IsAbelian(A2);
                orders := {Order(a) : a in A2};
                printf "  Element orders: %o\n", orders;
                involutions := [a : a in A2 | Order(a) eq 2];
                printf "  Number of involutions: %o\n", #involutions;
            else
                printf "  u+v not primitive, trying 2u+v...\n";
                alpha := vv + 2*uu;
                minpoly := MinimalPolynomial(alpha, Fpt);
                printf "  deg(minpoly of 2u+v) = %o\n", Degree(minpoly);
                if Degree(minpoly) eq 8 then
                    Kx<x> := PolynomialRing(Fpt);
                    FD2<aa> := FunctionField(Kx ! minpoly);
                    printf "  Genus(D via simple ext) = %o\n", Genus(FD2);
                    A2, mp2, gens2 := AutomorphismGroup(FD2);
                    printf "  |Aut(D)| = %o\n", #A2;
                    printf "  Structure: %o\n", GroupName(A2);
                end if;
            end if;
        catch e2
            printf "  Simple extension also failed: %o\n", e2`Object;
        end try;
    end try;

    printf "\n";
end for;

quit;
