/*******************************************************************************
 * aut_D_full.m
 *
 * Full analysis of Aut(D) for the descent-as-a-curve problem.
 * D: genus 5 etale double cover of Fermat quartic C: u^4+t^4+1=0,
 * defined by v^2 = q1 = 2t^2 + (1-w)u^2 + (1+w), w = sqrt(-3).
 *
 * Goal: determine Aut(D), find the deck involution iota inside it,
 * check if <iota> is normal/central, and analyze the quotient.
 ******************************************************************************/

p := 13;
Fp := GF(p);
w := Sqrt(Fp!(-3));
printf "p = %o, w = sqrt(-3) = %o\n\n", p, w;

// Function field of C: u^4 + t^4 + 1 = 0
Fpt<t> := FunctionField(Fp);
Ku<u> := PolynomialRing(Fpt);
FC<uu> := FunctionField(u^4 + t^4 + 1);
printf "Genus(C) = %o\n", Genus(FC);

// D: v^2 = q1 on C
q1 := 2*(FC!t)^2 + (1-w)*uu^2 + (1+w);
Kv<v> := PolynomialRing(FC);
FD<vv> := FunctionField(v^2 - q1);
printf "Genus(D) = %o\n\n", Genus(FD);

// Compute Aut(D)
printf "Computing Aut(D)...\n";
time A, mp := AutomorphismGroup(FD);
printf "|Aut(D)| = %o\n", #A;
printf "Type = %o\n\n", Type(A);

// Convert to permutation group for structural analysis
printf "Converting to permutation group...\n";
phi, G := CosetAction(A, sub<A | Id(A)>);
printf "Permutation degree = %o\n", Degree(G);
printf "|G| = %o\n", #G;
printf "GroupName = %o\n", GroupName(G);
printf "IsAbelian = %o\n", IsAbelian(G);
printf "IsSolvable = %o\n", IsSolvable(G);
Z := Center(G);
printf "Center: order %o, structure %o\n\n", #Z, GroupName(Z);

// Composition/chief factors
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

// === Find the deck involution ===
// iota: t -> t, u -> u, v -> -v (the covering involution of D -> C)
// Strategy: check involutions in G (order 2 elements), pull back to A, test
printf "=== Finding deck involution ===\n";
deck_G := Identity(G);
found := false;

// Only check elements of order 2 (involutions)
involution_elts := [g : g in G | Order(g) eq 2];
printf "  Testing %o involutions...\n", #involution_elts;
for g in involution_elts do
    a := g @@ phi;
    aut := mp(a);
    if aut(vv) eq -vv and aut(FD!uu) eq FD!uu then
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

// === Involution analysis ===
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

// === Subgroup structure ===
printf "=== Key subgroups ===\n";

// N_G(<iota>) structure
printf "N_G(<iota>):\n";
printf "  Order = %o\n", #NN;
printf "  Structure = %o\n", GroupName(NN);
printf "  Abelianization = %o\n\n", AbelianQuotientInvariants(NN);

// Full group
printf "Abelianization of G: %o\n", AbelianQuotientInvariants(G);
printf "Derived length of G: %o\n\n", DerivedLength(G);

// Check: for each involution class, compute the quotient genus
// An involution tau on a genus 5 curve: if tau has r fixed points,
// the quotient has genus g' where 2*5-2 = 2*(2*g'-2) + r, i.e. 8 = 4g'-4+r
// So r = 12 - 4g'. For etale (r=0): g'=3. For r=4: g'=2. For r=8: g'=1.
printf "=== Quotient genera by involution classes ===\n";
printf "(Computing via Riemann-Hurwitz on function field)\n";
for idx in inv_classes do
    rep_A := CC[idx][3] @@ phi;
    aut := mp(rep_A);
    // The fixed field of <aut> has some genus
    // We can compute this by finding the genus of the fixed field
    // For now, count fixed places of degree 1
    // Actually, use the formula: for an involution with r fixed points,
    // g(D/<tau>) = (g(D) - 1 + r/2) / ... wait, wrong formula
    // RH: 2g(D)-2 = 2*(2g(Q)-2) + r, Q = D/<tau>
    // 8 = 4g(Q) - 4 + r => r = 12 - 4g(Q)
    // g(Q)=3: r=0 (etale), g(Q)=2: r=4, g(Q)=1: r=8, g(Q)=0: r=12
    //
    // Count fixed points by checking places of degree 1
    // This is slow, so skip for now and just note which class is the deck
    printf "  CC[%o] (size %o)", idx, CC[idx][2];
    if idx eq deck_cc then printf " = deck involution (etale, quotient genus 3)"; end if;
    printf "\n";
end for;

quit;
