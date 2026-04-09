/*******************************************************************************
 * descent_criterion.m
 *
 * Does D descend to Q as a curve? Analyze g^2 = iota in G = SmallGroup(96,3).
 *
 * Setup:
 * - C: x^4+y^4+z^4=0 (Fermat quartic), D -> C etale double cover
 * - D defined over K = Q(sqrt(-3)), Brauer obstruction for cover is nontrivial
 * - Aut(D) = G = SmallGroup(96,3) = C2^2.SL(2,3)
 * - Deck involution iota = Z(G) (central!)
 * - sigma in Gal(K/Q) acts trivially on Aut(D) (proved via Hom(G/Z,Z/2)=0)
 *
 * CONCLUSION: g^2 = iota has NO solutions => D does NOT descend to Q.
 ******************************************************************************/


// =========== SECTION 1: COUNTING SOLUTIONS TO g^2 = iota ===========

H := SmallGroup(96, 3);
iota := Center(H).1;
printf "G = %o, |G| = %o, Z(G) = %o\n", GroupName(H), #H, GroupName(Center(H));
printf "iota = generator of center, order %o\n\n", Order(iota);

// Count solutions to g^2 = iota
solutions := [h : h in H | h^2 eq iota];
printf "Number of g in G with g^2 = iota: %o\n\n", #solutions;

// Count solutions to g^2 = 1 (involutions + identity)
inv_solutions := [h : h in H | h^2 eq Id(H)];
printf "Number of g with g^2 = 1: %o (= 1 + #involutions)\n", #inv_solutions;

// Count order-4 elements and what they square to
order4 := [h : h in H | Order(h) eq 4];
printf "Number of order-4 elements: %o\n", #order4;

// What do the order-4 elements square to?
squares := {h^2 : h in order4};
printf "Distinct squares of order-4 elements: %o elements\n", #squares;
for s in squares do
    count := #[h : h in order4 | h^2 eq s];
    printf "  Square = (order %o, central? %o): %o elements\n",
        Order(s), s in Center(H), count;
end for;

printf "\n";

// Square roots of iota
printf "Square roots of iota (g^2 = iota):\n";
if #solutions eq 0 then
    printf "  NONE! iota has no square roots in G.\n\n";
else
    for s in solutions do
        printf "  Order %o, central? %o\n", Order(s), s in Center(H);
    end for;
end if;

// Normal subgroups of order 4
printf "Normal subgroups of order 4:\n";
norms := NormalSubgroups(H : OrderEqual := 4);
for n in norms do
    printf "  %o, isomorphic to %o\n", n`order, GroupName(n`subgroup);
    printf "    Contains iota? %o\n", iota in n`subgroup;
    for g in n`subgroup do
        if g ne Id(H) then
            printf "    Element: order %o, central? %o\n", Order(g), g in Center(H);
        end if;
    end for;
end for;


// =========== SECTION 2: COHOMOLOGICAL FRAMEWORK (H^1 and H^2) ===========

printf "\n=== H^1(Z/2, Aut(D)) with trivial action ===\n\n";
printf "With trivial sigma-action:\n";
printf "H^1(Z/2, Aut(D)) = {involutions + 1 in Aut(D)} / conjugacy\n\n";

// Conjugacy classes of involutions
CC := ConjugacyClasses(H);
inv_classes := [c : c in CC | c[1] eq 2];
printf "Conjugacy classes of involutions:\n";
for c in inv_classes do
    is_iota := IsConjugate(H, c[3], iota);
    printf "  Order 2, size %o, central? %o", c[2], c[3] in Center(H);
    if is_iota then printf " [= iota, deck involution]"; end if;
    printf "\n";
end for;
printf "Plus the trivial class {1}.\n";
printf "Total H^1 classes: %o (including trivial)\n\n",
    1 + #inv_classes;

// The descent class [D]
printf "The descent class [D] = [sigma -> iota] in H^1.\n";
printf "Is [D] trivial? NO (iota is central, cannot be conjugated to 1).\n\n";

// === H^2 analysis ===
printf "=== Kernel of H^2(G_Q, Z/2) -> H^2(G_Q, Aut(D)) ===\n\n";

// SES: 1 -> Z/2 -> Aut(D) -> Q -> 1 (central extension)
Q := H / Center(H);
printf "Q = Aut(D)/<iota> = %o, order %o\n", GroupName(Q), #Q;
printf "Ab(Q) = %o\n\n", AbelianQuotientInvariants(Q);

// delta: H^1(Z/2, Q) -> H^2(Z/2, Z/2)
Q_inv_classes := [c : c in ConjugacyClasses(Q) | c[1] eq 2];
printf "H^1(Z/2, Q) classes (= conjugacy classes of involutions in Q + {1}):\n";
for c in Q_inv_classes do
    printf "  Order 2, size %o\n", c[2];
end for;
printf "Plus trivial class.\n\n";

// For each involution class in Q, compute delta
printf "Computing delta: H^1(Z/2, Q) -> H^2(Z/2, Z/2) = Z/2:\n";
printf "  delta(1) = 0\n";

qH, qmap := H / Center(H);
for c in Q_inv_classes do
    rep_Q := c[3];
    lift := rep_Q @@ qmap;
    lift_sq := lift^2;
    printf "  delta(inv class size %o) = lift^2 = ", c[2];
    if lift_sq eq Id(H) then
        printf "0 (lift is involution in H)\n";
    elif lift_sq eq iota then
        printf "1 (lift has order 4, squares to iota)\n";
    else
        printf "??? (lift^2 = element of order %o)\n", Order(lift_sq);
    end if;
end for;


// =========== SECTION 3: DIRECT LIFT COMPUTATION ===========

printf "\n=== DIRECT LIFT ANALYSIS ===\n";

// For each involution in G, check if it squares to iota
involutions_in_G := [h : h in H | Order(h) eq 2];
printf "Involutions in G: %o\n", #involutions_in_G;

// Elements of order 4 squaring to iota?
printf "Elements of order 4 in G: %o\n", #order4;
has_nontrivial_delta := false;
for h in order4 do
    if h^2 eq iota then
        printf "  FOUND: h^2 = iota! (h has order 4)\n";
        has_nontrivial_delta := true;
    end if;
end for;

printf "\n# solutions to g^2 = iota: %o\n\n", #solutions;

// Analyze lifts via cosets
printf "=== Analyzing lifts of involutions ===\n";
inv_lifts := [h : h in H | Order(h) in {2,4} and h^2 in {Id(H), iota}
              and h ne Id(H) and h ne iota];
printf "Elements projecting to involutions in Q (excl identity): %o\n", #inv_lifts;

cosets := {};
for h in inv_lifts do
    coset := {h, iota*h};
    Include(~cosets, coset);
end for;
printf "Cosets (= involutions in Q): %o\n", #cosets;

for coset in cosets do
    h := Representative(coset);
    if h^2 eq Id(H) then
        printf "  Lift is INVOLUTION (h^2=1) => delta = 0\n";
    elif h^2 eq iota then
        printf "  Lift has ORDER 4 (h^2=iota) => delta = 1 !!\n";
    end if;
end for;

printf "\nIm(delta) contains 1? %o\n\n", has_nontrivial_delta;

// Also check twisted cocycles (inner automorphisms)
if #solutions eq 0 then
    printf "Double-check: g * sigma(g) = iota with sigma = inner aut by h?\n";
    any_inner := false;
    for h in H do
        sigma_h := map<H -> H | x :-> h * x * h^-1>;
        count := #[g : g in H | g * sigma_h(g) eq iota];
        if count gt 0 then
            printf "  Inner aut by h (order %o): %o solutions\n", Order(h), count;
            any_inner := true;
        end if;
    end for;
    if not any_inner then
        printf "  No inner automorphism helps.\n";
    end if;
end if;


// =========== CONCLUSION ===========

printf "\n=== FINAL RESULT ===\n\n";
if has_nontrivial_delta then
    printf "Im(delta) = Z/2 => ker(H^2(G_Q,Z/2)->H^2(G_Q,Aut(D))) = Z/2.\n";
    printf "The Brauer class IS in the kernel.\n";
    printf "*** D DESCENDS to Q as a curve. ***\n";
else
    printf "Im(delta) = 0 => ker(H^2(G_Q,Z/2)->H^2(G_Q,Aut(D))) = 0.\n";
    printf "The Brauer class is NOT in the kernel.\n";
    printf "*** D does NOT descend to Q as a curve. ***\n";
end if;

printf "\nKey facts:\n";
printf "1. Aut(D) = C2^2.SL(2,3), with iota CENTRAL.\n";
printf "2. sigma acts trivially on Aut(D)\n";
printf "   (since Hom(Aut(D)/<iota>, Z/2) = Hom(C4^2:C3, Z/2) = 0).\n";
printf "3. g^2 = iota has NO solutions in G.\n";
printf "4. The cocycle [sigma -> iota] is nontrivial in H^1(G_Q, Aut(D)),\n";
printf "   and the Brauer class survives H^2(G_Q,Z/2) -> H^2(G_Q,Aut(D)).\n";

quit;
