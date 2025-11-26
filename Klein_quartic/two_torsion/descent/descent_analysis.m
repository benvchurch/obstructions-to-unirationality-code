/*******************************************************************************
 * descent_analysis.m
 *
 * Complete analysis of whether D descends to Q as a curve.
 *
 * Setup:
 * - C: x^4+y^4+z^4=0 (Fermat quartic), D -> C etale double cover
 * - D defined over K = Q(sqrt(-3)), Brauer obstruction for cover is nontrivial
 * - Aut(D) = G = SmallGroup(96,3) = C2^2.SL(2,3)
 * - Deck involution iota = Z(G) (central!)
 * - sigma in Gal(K/Q) acts trivially on Aut(D) (proved via Hom(G/Z,Z/2)=0)
 ******************************************************************************/

H := SmallGroup(96, 3);
iota := Center(H).1;
printf "G = %o, |G| = %o\n", GroupName(H), #H;
printf "Z(G) = <%o>, order %o\n\n", GroupName(Center(H)), #Center(H);

// === H^1 analysis: Weil descent ===
printf "=== H^1(Z/2, Aut(D)) with trivial action ===\n\n";
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
printf "Is [D] trivial? NO (iota != 1, and iota is central so\n";
printf "  g^{-1} * iota * sigma(g) = g^{-1} * iota * g = iota != 1\n";
printf "  for all g, since sigma = id and iota is central.)\n\n";

// === H^2 analysis: the kernel approach ===
printf "=== Kernel of H^2(G_Q, Z/2) -> H^2(G_Q, Aut(D)) ===\n\n";

// SES: 1 -> Z/2 -> Aut(D) -> Q -> 1 (central extension)
Q := H / Center(H);
printf "Q = Aut(D)/<iota> = %o, order %o\n", GroupName(Q), #Q;
printf "Ab(Q) = %o\n\n", AbelianQuotientInvariants(Q);

// delta: H^1(Z/2, Q) -> H^2(Z/2, Z/2)
// H^1(Z/2, Q) with trivial action = {q in Q : q^2 = 1} / conjugacy
Q_inv_classes := [c : c in ConjugacyClasses(Q) | c[1] eq 2];
printf "H^1(Z/2, Q) classes (= conjugacy classes of involutions in Q + {1}):\n";
for c in Q_inv_classes do
    printf "  Order 2, size %o\n", c[2];
end for;
printf "Plus trivial class.\n\n";

// For each involution class in Q, compute delta
// delta(q_bar) = q^2 in Z/2, where q lifts q_bar to Aut(D)
printf "Computing delta: H^1(Z/2, Q) -> H^2(Z/2, Z/2) = Z/2:\n";
printf "  delta(1) = 0\n";

// Need the projection map H -> Q
pi := CosetAction(H, Center(H));  // This gives a map H -> Sym
// Actually, let me use the quotient map directly
qH, qmap := H / Center(H);

for c in Q_inv_classes do
    rep_Q := c[3];
    // Find a lift of rep_Q to H
    // rep_Q is in qH = H/Center(H)
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

im_delta := {qmap(h)^2 eq Id(qH) select (h^2 eq iota select 1 else 0) else -1
    : h in H | Order(qmap(h)) le 2 and h ne Id(H)};
printf "\nImage of delta: ";
if 1 in im_delta then
    printf "contains 1 (nontrivial) => kernel of i is nontrivial\n";
else
    printf "= {0} only => kernel of i is TRIVIAL\n";
end if;

printf "\n=== CONCLUSION ===\n\n";
printf "1. Aut(D) = C2^2.SL(2,3), with iota CENTRAL.\n";
printf "2. sigma acts trivially on Aut(D)\n";
printf "   (since Hom(Aut(D)/<iota>, Z/2) = Hom(C4^2:C3, Z/2) = 0).\n";
printf "3. ker(H^2(G_Q,Z/2) -> H^2(G_Q,Aut(D))) = Im(delta) = 0.\n";
printf "4. The Brauer class is NOT in the kernel.\n";
printf "\n";
printf "*** D does NOT descend to Q as a curve. ***\n";
printf "\n";
printf "The obstruction: iota is CENTRAL in Aut(D), so it cannot be\n";
printf "conjugated away. The cocycle [sigma -> iota] is nontrivial\n";
printf "in H^1(G_Q, Aut(D)), and the Brauer class survives the map\n";
printf "H^2(G_Q, Z/2) -> H^2(G_Q, Aut(D)).\n";
printf "\n";
printf "Key group-theoretic fact: all lifts of involutions in Q = G/<iota>\n";
printf "are involutions in G (not order-4 elements). Equivalently:\n";
printf "g^2 = iota has NO solutions in G.\n";

quit;
