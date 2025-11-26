/*******************************************************************************
 * count_solutions.m
 *
 * Count the actual number of solutions to g^2 = iota in G = SmallGroup(96,3).
 * This is the KEY descent criterion.
 ******************************************************************************/

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

// What elements does iota have as square roots?
printf "Square roots of iota (g^2 = iota):\n";
if #solutions eq 0 then
    printf "  NONE! iota has no square roots in G.\n\n";
else
    for s in solutions do
        printf "  Order %o, central? %o\n", Order(s), s in Center(H);
    end for;
end if;

// Normal subgroups of order 4 (the C2^2 normal subgroup)
printf "Normal subgroups of order 4:\n";
norms := NormalSubgroups(H : OrderEqual := 4);
for n in norms do
    printf "  %o, isomorphic to %o\n", n`order, GroupName(n`subgroup);
    // Is iota in this subgroup?
    printf "    Contains iota? %o\n", iota in n`subgroup;
    // Elements of this subgroup
    for g in n`subgroup do
        if g ne Id(H) then
            printf "    Element: order %o, central? %o\n", Order(g), g in Center(H);
        end if;
    end for;
end for;

printf "\n=== CONCLUSION ===\n";
if #solutions gt 0 then
    printf "g^2 = iota HAS solutions => D descends to Q as a curve.\n";
else
    printf "g^2 = iota has NO solutions => Brauer class NOT killed.\n";
    printf "D does NOT descend to Q as a curve (with this analysis).\n";

    // But wait: check if the sigma-action could be nontrivial
    // (even though Hom(G/Z, Z/2) = 0 says it must be trivial)
    // Double-check by examining all elements
    printf "\nDouble-check: g * sigma(g) = iota with sigma = inner aut by h?\n";
    for h in H do
        sigma_h := map<H -> H | x :-> h * x * h^-1>;
        count := #[g : g in H | g * sigma_h(g) eq iota];
        if count gt 0 then
            printf "  Inner aut by h (order %o): %o solutions\n", Order(h), count;
        end if;
    end for;
end if;

quit;
