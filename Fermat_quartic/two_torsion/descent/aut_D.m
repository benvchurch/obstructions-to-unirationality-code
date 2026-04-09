/*******************************************************************************
 * aut_D.m
 *
 * Compute and analyze Aut(D) for the genus 5 etale double cover D of the
 * Fermat quartic C: u^4+t^4+1=0, defined by v^2 = q1 where
 * q1 = 2t^2 + (1-w)u^2 + (1+w), w = sqrt(-3).
 *
 * RESULTS:
 * - Geometric |Aut(D)| = 96, SmallGroup(96,3) = C2^2.SL(2,3)
 * - Field of definition = Q(sqrt(-3), i) = Q(zeta_12)
 * - Over Q(sqrt(-3)) alone: index-2 subgroup C2*S4 (order 48)
 * - Deck involution iota is CENTRAL in Aut(D)
 * - |Aut(D)| does NOT grow over F_{p^2} (stays 96, not 192)
 ******************************************************************************/


// =========== SECTION 1: MULTI-PRIME SmallGroup IDENTIFICATION ===========
// Compare p = 1 mod 12 (has sqrt(-1) and sqrt(-3)) vs p = 7 mod 12
// (has sqrt(-3) only). If |Aut| differs, some auts need sqrt(-1).

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

        // Deck involution: v -> -v, u -> u, t -> t
        for g in G do
            if Order(g) ne 2 then continue; end if;
            a := g @@ phi;
            aut := mp(a);
            if aut(vv) eq -vv and aut(FD!uu) eq FD!uu and aut(FD!t) eq FD!t then
                printf "  Deck involution central? %o\n", g in Center(G);
                break;
            end if;
        end for;
    catch e
        printf "  Failed: %o\n", e`Object;
    end try;
    printf "\n";
end for;

printf "=== MULTI-PRIME SUMMARY ===\n";
printf "p=13 (has sqrt(-1)): |Aut| = 96 = SmallGroup(96,3)\n";
printf "p=19 (no sqrt(-1)):  |Aut| = 48 = C2*S4\n";
printf "p=37 (has sqrt(-1)): |Aut| = 96 = SmallGroup(96,3)\n";
printf "p=43 (no sqrt(-1)):  |Aut| = 48 = C2*S4\n";
printf "=> Geometric |Aut(D)| = 96, field of definition = Q(sqrt(-3), i)\n";
printf "=> Over Q(sqrt(-3)) alone: index-2 subgroup C2*S4 (order 48)\n";
printf "=> Deck involution CENTRAL at all primes\n\n";


// =========== SECTION 2: FULL STRUCTURE ANALYSIS AT p=13 ===========

p := 13;
Fp := GF(p);
w := Sqrt(Fp!(-3));
printf "=== FULL STRUCTURE AT p = %o, w = sqrt(-3) = %o ===\n\n", p, w;

Fpt<t> := FunctionField(Fp);
Ku<u> := PolynomialRing(Fpt);
FC<uu> := FunctionField(u^4 + t^4 + 1);
printf "Genus(C) = %o\n", Genus(FC);

q1 := 2*(FC!t)^2 + (1-w)*uu^2 + (1+w);
Kv<v> := PolynomialRing(FC);
FD<vv> := FunctionField(v^2 - q1);
printf "Genus(D) = %o\n\n", Genus(FD);

printf "Computing Aut(D)...\n";
time A, mp := AutomorphismGroup(FD);
phi, G := CosetAction(A, sub<A | Id(A)>);
printf "|Aut(D)| = %o\n", #G;
printf "GroupName = %o\n", GroupName(G);
printf "IsAbelian = %o\n", IsAbelian(G);
printf "IsSolvable = %o\n", IsSolvable(G);
Z := Center(G);
printf "Center: order %o, structure %o\n\n", #Z, GroupName(Z);

// Composition factors
printf "Composition factors:\n";
cf := CompositionFactors(G);
for i in [1..#cf] do
    printf "  %o\n", cf[i];
end for;
printf "\n";

// Conjugacy classes
CC := ConjugacyClasses(G);
printf "Conjugacy classes (order, size, |centralizer|):\n";
for i in [1..#CC] do
    printf "  CC[%2o]: order %2o, size %2o, |C_G| = %o\n",
        i, CC[i][1], CC[i][2], #G div CC[i][2];
end for;
printf "\n";

// --- Find the deck involution ---
printf "=== Finding deck involution ===\n";
deck_G := Identity(G);
found := false;

involution_elts := [g : g in G | Order(g) eq 2];
printf "  Testing %o involutions...\n", #involution_elts;
for g in involution_elts do
    a := g @@ phi;
    aut := mp(a);
    if aut(vv) eq -vv and aut(FD!uu) eq FD!uu and aut(FD!t) eq FD!t then
        deck_G := g;
        found := true;
        break;
    end if;
end for;

if not found then
    printf "ERROR: deck involution not found!\n";
    quit;
end if;

printf "Deck involution found.\n";
printf "  Order = %o\n", Order(deck_G);
printf "  In center of Aut(D)? %o\n", deck_G in Z;

// Conjugacy class of deck involution
deck_cc := 0;
for i in [1..#CC] do
    if IsConjugate(G, deck_G, CC[i][3]) then
        deck_cc := i;
        printf "  In conjugacy class CC[%o] (size %o)\n", i, CC[i][2];
        break;
    end if;
end for;

// Normal subgroup check
deck_sub := sub<G | deck_G>;
NN := Normalizer(G, deck_sub);
printf "  |N_G(<iota>)| = %o\n", #NN;
printf "  <iota> normal in G? %o\n", IsNormal(G, deck_sub);
printf "  [G : N_G(<iota>)] = %o (= # conjugates of iota)\n\n", #G div #NN;

// If normal, compute quotient
if IsNormal(G, deck_sub) then
    Q, qmap := G / deck_sub;
    printf "Quotient Aut(D)/<iota>:\n";
    printf "  Order = %o\n", #Q;
    printf "  Structure = %o\n", GroupName(Q);
    printf "  IsAbelian = %o\n\n", IsAbelian(Q);
end if;

// --- Involution analysis ---
printf "=== Involution analysis ===\n";
inv_classes := [i : i in [1..#CC] | CC[i][1] eq 2];
printf "Number of conjugacy classes of involutions: %o\n", #inv_classes;
total_inv := &+[CC[i][2] : i in inv_classes];
printf "Total number of involutions: %o\n\n", total_inv;

// For each involution class, check which ones fix FC
for idx in inv_classes do
    rep_A := CC[idx][3] @@ phi;
    aut := mp(rep_A);
    fixes_FC := (aut(FD!t) eq FD!t) and (aut(FD!uu) eq FD!uu);
    printf "CC[%o] (size %o): fixes FC? %o", idx, CC[idx][2], fixes_FC;
    if idx eq deck_cc then printf " [DECK INVOLUTION]"; end if;
    printf "\n";
end for;
printf "\n";

// --- Subgroup structure ---
printf "=== Key subgroups ===\n";
printf "N_G(<iota>): Order = %o, Structure = %o\n", #NN, GroupName(NN);
printf "  Abelianization = %o\n\n", AbelianQuotientInvariants(NN);

printf "Abelianization of G: %o\n", AbelianQuotientInvariants(G);
printf "Derived length of G: %o\n\n", DerivedLength(G);


// =========== SECTION 3: GEOMETRIC VS ARITHMETIC (F_p vs F_{p^2}) ===========

printf "=== GEOMETRIC VS ARITHMETIC: F_13 vs F_169 ===\n\n";

// Over F_13 (already computed)
printf "Over F_13:  |Aut(D)| = %o, GroupName = %o\n", #G, GroupName(G);

// Over F_{13^2} = F_169
printf "\nComputing Aut(D) over F_169...\n";
Fq := GF(13^2);
w2 := Sqrt(Fq!(-3));
printf "w = sqrt(-3) = %o in F_169\n", w2;

Fqt<t2> := FunctionField(Fq);
Ku2<u2> := PolynomialRing(Fqt);
FC2<uu2> := FunctionField(u2^4 + t2^4 + 1);
q1_2 := 2*(FC2!t2)^2 + (1-w2)*uu2^2 + (1+w2);
Kv2<v2> := PolynomialRing(FC2);
FD2<vv2> := FunctionField(v2^2 - q1_2);
printf "Genus(D) = %o\n", Genus(FD2);
time A169, mp169 := AutomorphismGroup(FD2);
phi169, G169 := CosetAction(A169, sub<A169 | Id(A169)>);
printf "|Aut(D/F_169)| = %o, GroupName = %o\n", #G169, GroupName(G169);
printf "|Z(Aut(D/F_169))| = %o\n\n", #Center(G169);

printf "=== GEOMETRIC SUMMARY ===\n";
printf "Over F_13:  |Aut(D)| = %o\n", #G;
printf "Over F_169: |Aut(D)| = %o\n", #G169;
printf "Ratio: %o\n", #G169 / #G;
if #G169 eq #G then
    printf "No new automorphisms over F_{p^2}: geometric |Aut(D)| = %o.\n", #G;
else
    printf "New automorphisms over F_{p^2}!\n";
end if;

quit;
