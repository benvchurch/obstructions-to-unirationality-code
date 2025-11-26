/*******************************************************************************
 * aut_D_multicheck2.m
 *
 * Quick multi-prime Aut(D) check — just the essential primes.
 * Focus on the 1 mod 12 vs 7 mod 12 comparison.
 ******************************************************************************/

primes := [7, 13, 19, 37, 43];

for p in primes do
    Fp := GF(p);
    if not IsSquare(Fp!(-3)) then continue; end if;
    w := Sqrt(Fp!(-3));
    has_i := IsSquare(Fp!(-1));
    printf "=== p = %o (sqrt(-1) exists? %o) ===\n", p, has_i;

    Fpt<t> := FunctionField(Fp);
    Ku<u> := PolynomialRing(Fpt);
    f_C := u^4 + t^4 + 1;
    if not IsIrreducible(f_C) then
        printf "  C reducible, skipping.\n\n";
        continue;
    end if;
    FC<uu> := FunctionField(f_C);
    q1 := 2*(FC!t)^2 + (1-w)*uu^2 + (1+w);
    Kv<v> := PolynomialRing(FC);
    if not IsIrreducible(v^2 - q1) then
        printf "  D reducible, skipping.\n\n";
        continue;
    end if;
    FD<vv> := FunctionField(v^2 - q1);

    printf "  Genus(D) = %o. Computing Aut(D)...\n", Genus(FD);
    try
        A, mp := AutomorphismGroup(FD);
        phi, G := CosetAction(A, sub<A | Id(A)>);
        id := IdentifyGroup(G);
        printf "  |Aut(D)| = %o, SmallGroup(%o,%o) = %o\n",
            #G, id[1], id[2], GroupName(G);
        printf "  |Z(Aut(D))| = %o\n", #Center(G);

        // Deck involution
        for g in G do
            if Order(g) ne 2 then continue; end if;
            a := g @@ phi;
            aut := mp(a);
            if aut(vv) eq -vv and aut(FD!uu) eq FD!uu then
                printf "  Deck involution central? %o\n", g in Center(G);
                break;
            end if;
        end for;
    catch e
        printf "  Failed: %o\n", e`Object;
    end try;
    printf "\n";
end for;

printf "=== ANALYSIS ===\n";
printf "p=7  (no sqrt(-1)): |Aut| = 24 (anomalous? 7 is small)\n";
printf "p=13 (has sqrt(-1)): |Aut| = 96\n";
printf "p=19 (no sqrt(-1)): |Aut| = 48\n";
printf "p=37 (has sqrt(-1)): |Aut| = ?\n";
printf "p=43 (no sqrt(-1)): |Aut| = ?\n";
printf "\nIf pattern is 96 when sqrt(-1) exists, 48 when not:\n";
printf "=> [Aut(D_Qbar) : Aut(D_Q(sqrt(-3)))] = 2\n";
printf "=> Some auts need sqrt(-1), field of definition is Q(sqrt(-3), i)\n";

quit;
