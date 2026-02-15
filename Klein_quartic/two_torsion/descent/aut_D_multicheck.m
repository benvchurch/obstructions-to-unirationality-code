/*******************************************************************************
 * aut_D_multicheck.m
 *
 * Verify Aut(D) across multiple primes with different residue conditions.
 *
 * D: genus 5 etale double cover of Fermat quartic C: u^4+t^4+1=0,
 * defined by v^2 = q1 = 2t^2 + (1-w)u^2 + (1+w), w = sqrt(-3).
 *
 * Key question: is Aut(D) defined over Q(sqrt(-3)) alone, or does it
 * require Q(sqrt(-3), i)?
 *
 * Strategy:
 * - p ≡ 1 mod 12: both sqrt(-3) and sqrt(-1) exist in F_p
 *     => all auts over Q(sqrt(-3),i) are visible
 * - p ≡ 7 mod 12: sqrt(-3) exists, sqrt(-1) does NOT
 *     => only auts over Q(sqrt(-3)) are visible
 * If |Aut(D)| differs between these classes, some auts need i.
 ******************************************************************************/

// Classification helper
function ResidueClass(p)
    has3 := IsSquare(GF(p)!(-3));
    has1 := IsSquare(GF(p)!(-1));
    if has3 and has1 then return "1 mod 12 (sqrt(-3) YES, sqrt(-1) YES)";
    elif has3 and not has1 then return "7 mod 12 (sqrt(-3) YES, sqrt(-1) NO)";
    elif not has3 and has1 then return "5 mod 12 (sqrt(-3) NO, sqrt(-1) YES)";
    else return "11 mod 12 (sqrt(-3) NO, sqrt(-1) NO)";
    end if;
end function;

// Primes grouped by residue class
// p ≡ 1 mod 12: 13, 37, 61, 73, 97
// p ≡ 7 mod 12: 7, 19, 31, 43, 67
// Also try p=5 (≡ 5 mod 12), p=11 (≡ 11 mod 12) for cross-check
primes := [5, 7, 11, 13, 19, 31, 37, 43, 61, 67];

for p in primes do
    Fp := GF(p);
    has_sqrt3 := IsSquare(Fp!(-3));
    has_sqrt1 := IsSquare(Fp!(-1));
    printf "=== p = %o [%o] ===\n", p, ResidueClass(p);

    if not has_sqrt3 then
        printf "  sqrt(-3) does not exist, cannot define D over F_p. Skipping.\n\n";
        continue;
    end if;

    w := Sqrt(Fp!(-3));

    // Function field of C
    Fpt<t> := FunctionField(Fp);
    Ku<u> := PolynomialRing(Fpt);
    f_C := u^4 + t^4 + 1;

    if not IsIrreducible(f_C) then
        printf "  C reducible mod %o, skipping.\n\n", p;
        continue;
    end if;

    FC<uu> := FunctionField(f_C);
    g_C := Genus(FC);

    // q1 on C
    q1 := 2*(FC!t)^2 + (1-w)*uu^2 + (1+w);

    // D: v^2 = q1
    Kv<v> := PolynomialRing(FC);
    f_D := v^2 - q1;

    if not IsIrreducible(f_D) then
        printf "  D reducible (q1 is square on C), skipping.\n\n", p;
        continue;
    end if;

    FD<vv> := FunctionField(f_D);
    g_D := Genus(FD);
    printf "  Genus(C) = %o, Genus(D) = %o\n", g_C, g_D;

    // Compute Aut(D) over F_p
    printf "  Computing Aut(D) over F_%o...\n", p;
    try
        A, mp := AutomorphismGroup(FD);
        phi, G := CosetAction(A, sub<A | Id(A)>);
        printf "  |Aut(D)| = %o\n", #G;
        printf "  GroupName = %o\n", GroupName(G);
        Z := Center(G);
        printf "  |Z(Aut(D))| = %o\n", #Z;

        // Find deck involution: v -> -v, u -> u, t -> t
        // Must check t too! (t,u,v)->(-t,u,-v) also has v->-v, u->u
        deck_found := false;
        for g in G do
            if Order(g) ne 2 then continue; end if;
            a := g @@ phi;
            aut := mp(a);
            if aut(vv) eq -vv and aut(FD!uu) eq FD!uu and aut(FD!t) eq FD!t then
                printf "  Deck involution: central? %o\n", g in Z;
                deck_found := true;
                break;
            end if;
        end for;
        if not deck_found then
            printf "  WARNING: deck involution not found!\n";
        end if;

        // SmallGroup identification
        id := IdentifyGroup(G);
        printf "  SmallGroup(%o, %o)\n", id[1], id[2];

    catch e
        printf "  AutomorphismGroup failed: %o\n", e`Object;

        // Fallback: try via simple extension
        printf "  Trying simple extension (u+v)...\n";
        try
            alpha := vv + uu;
            minpoly := MinimalPolynomial(alpha, Fpt);
            if Degree(minpoly) eq 8 then
                Kx<x> := PolynomialRing(Fpt);
                FD2<aa> := FunctionField(Kx ! minpoly);
                A2, mp2 := AutomorphismGroup(FD2);
                phi2, G2 := CosetAction(A2, sub<A2 | Id(A2)>);
                printf "  |Aut(D)| = %o (via simple ext)\n", #G2;
                printf "  GroupName = %o\n", GroupName(G2);
                id := IdentifyGroup(G2);
                printf "  SmallGroup(%o, %o)\n", id[1], id[2];
            else
                printf "  u+v not primitive (deg %o)\n", Degree(minpoly);
            end if;
        catch e2
            printf "  Simple extension also failed: %o\n", e2`Object;
        end try;
    end try;

    printf "\n";
end for;

printf "=== SUMMARY ===\n";
printf "If |Aut(D)| = 96 at ALL primes (both 1 mod 12 and 7 mod 12),\n";
printf "then Aut(D) is defined over Q(sqrt(-3)) alone.\n";
printf "If |Aut(D)| < 96 at primes ≡ 7 mod 12 (no sqrt(-1)),\n";
printf "then some auts require Q(i), so field of definition is Q(sqrt(-3), i).\n";

quit;
