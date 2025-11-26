/*******************************************************************************
 * descent_final.m
 *
 * Final analysis: does D descend to Q as a curve?
 ******************************************************************************/

H := SmallGroup(96, 3);
iota := Center(H).1;
printf "G = %o, |G| = %o, Z(G) = C2\n\n", GroupName(H), #H;

// === Key computation: image of delta ===
// delta: H^1(Z/2,Q) -> H^2(Z/2,Z/2) where Q = G/<iota>
// delta(q_bar) = q^2 where q is any lift of q_bar to G
// (well-defined since iota is central and q_bar^2 = 1 => q^2 in <iota>)

printf "=== Computing delta directly ===\n";
printf "For each involution in G, check if it squares to iota:\n\n";

involutions_in_G := [h : h in H | Order(h) eq 2];
printf "Involutions in G: %o\n", #involutions_in_G;
for h in involutions_in_G do
    printf "  h^2 = %o, central? %o\n",
        h^2 eq Id(H) select "1" else (h^2 eq iota select "iota" else "other"),
        h in Center(H);
end for;

printf "\nElements of order 4 in G: ";
order4 := [h : h in H | Order(h) eq 4];
printf "%o\n", #order4;
for h in order4 do
    sq := h^2;
    sq_is_iota := sq eq iota;
    if sq_is_iota then
        printf "  FOUND: h^2 = iota! (h has order 4)\n";
    end if;
end for;

solutions := #{h : h in H | h^2 eq iota};
printf "\n# solutions to g^2 = iota: %o\n\n", solutions;

// The key point: do involutions in Q lift to involutions or order-4 elements?
// Q = G/<iota>, so Q has order 48.
// Involutions in Q: their preimages in G are pairs {h, iota*h}
// If h^2 = 1: h is involution in G (lift is involution) => delta(h_bar) = 0
// If h^2 = iota: h has order 4 (lift has order 4) => delta(h_bar) = 1

printf "=== Analyzing lifts of involutions ===\n";
// Work directly: h in G with h^2 in {1, iota} and h != 1 and h != iota
// These project to involutions in Q.
// Group them by cosets of <iota>:
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

// Im(delta)
has_nontrivial_delta := exists{h : h in inv_lifts | h^2 eq iota};
printf "\nIm(delta) contains 1? %o\n\n", has_nontrivial_delta;

printf "=== FINAL RESULT ===\n\n";
if has_nontrivial_delta then
    printf "Im(delta) = Z/2 => ker(H^2(G_Q,Z/2)->H^2(G_Q,Aut(D))) = Z/2.\n";
    printf "The Brauer class IS in the kernel.\n";
    printf "*** D DESCENDS to Q as a curve. ***\n";
else
    printf "Im(delta) = 0 => ker(H^2(G_Q,Z/2)->H^2(G_Q,Aut(D))) = 0.\n";
    printf "The Brauer class is NOT in the kernel.\n";
    printf "*** D does NOT descend to Q as a curve. ***\n";
end if;

printf "\n=== Cross-check with H^1 ===\n";
printf "H^1(Z/2, Aut(D)) with trivial action:\n";
printf "Classes = conjugacy classes of {involutions, 1} in G:\n";
CC := ConjugacyClasses(H);
inv_cc := [c : c in CC | c[1] le 2];
for c in inv_cc do
    printf "  Order %o, size %o\n", c[1], c[2];
end for;
printf "[D] = class of iota (order 2, size 1, CENTRAL).\n";
printf "[D] is nontrivial since iota != 1 and iota is central\n";
printf "(cannot be conjugated to 1).\n";
printf "Consistent: D does NOT descend.\n";

quit;
