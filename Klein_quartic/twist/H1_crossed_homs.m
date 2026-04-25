/*******************************************************************************
 * H1_crossed_homs.m
 *
 * Purpose:
 *   Compute H^1(Z/n, PSL(2,7)) where the generator sigma of Z/n acts on
 *   PSL(2,7) by an outer automorphism of order n = sigma_order.
 *
 *   sigma_order = 2: H^1(Gal(Q(sqrt(-7))/Q), PSL(2,7)), classifying
 *     twists of C_twist trivial over Q(sqrt(-7)).
 *   sigma_order = 6: H^1(Gal(Q(zeta_7)/Q), PSL(2,7)), classifying
 *     twists of the Klein quartic trivial over Q(zeta_7).
 *
 * Method:
 *   1. Find an outer automorphism sigma of order n in Aut(PSL(2,7))
 *   2. Compute Z^1 = {g in G : g * sigma(g) * ... * sigma^(n-1)(g) = 1}
 *   3. Compute B^1 = {h^(-1) * sigma(h) : h in G}
 *   4. Compute H^1 = Z^1 / ~ where g1 ~ g2 iff exists h with
 *      g1 = h^(-1) * g2 * sigma(h)
 *   5. Symplectic lifting: lift sigma to SL(2,7) and check which PSL
 *      classes are in the image of H^1(Z/n, SL(2,7)) -> H^1(Z/n, PSL(2,7)).
 *
 * Schur cover:
 *   SL(2,7) is the Schur cover of PSL(2,7): the universal central extension
 *   1 -> Z/2 -> SL(2,7) -> PSL(2,7) -> 1, with H_2(PSL(2,7), Z) = Z/2.
 *   Every automorphism of PSL(2,7) lifts uniquely to SL(2,7) (universal
 *   property), and uniqueness forces the lift to preserve order.
 ******************************************************************************/

// === PARAMETER ===
sigma_order := 6;

// Step 1: Setup — find outer automorphism of given order
G := PSL(2,7);
A := AutomorphismGroup(G);

sigma := Identity(A);
found := false;

for gen in Generators(A) do
    ord := Order(gen);
    if ord mod sigma_order eq 0 then
        candidate := gen^(ord div sigma_order);
        if Order(candidate) eq sigma_order and not IsInner(candidate) then
            sigma := candidate;
            found := true;
            break;
        end if;
    end if;
end for;

if not found then
    AutSet := { A!1 };
    repeat
        for g1 in Generators(A) do
            for g2 in AutSet do
                Include(~AutSet, g1*g2);
            end for;
        end for;
    until #AutSet eq #A;

    for elt in AutSet do
        if Order(elt) eq sigma_order and not IsInner(elt) then
            sigma := elt;
            found := true;
            break;
        end if;
    end for;
end if;

assert found;
print "Found outer automorphism sigma of order", sigma_order;

// Define sigma as a function on G
sigma_map := func< g | sigma(g) >;

// Compute and identify the fixed subgroup G^sigma = {g in G : sigma(g) = g}
fixed_gens := [g : g in G | sigma_map(g) eq g];
G_sigma := sub<G | fixed_gens>;
print "Fixed subgroup G^sigma: order", #G_sigma, ", isomorphic to", GroupName(G_sigma),
      ", ID =", IdentifyGroup(G_sigma);

// Step 2: Compute Z^1 (1-cocycles)
// f(sigma^n) = g * sigma(g) * sigma^2(g) * ... * sigma^(n-1)(g) = 1
Z1 := [];
for g in G do
    prod := Id(G);
    val := g;
    for k := 0 to sigma_order - 1 do
        prod := prod * val;
        val := sigma_map(val);
    end for;
    if prod eq Id(G) then
        Append(~Z1, g);
    end if;
end for;
print "";
print "=== Z^1 (1-cocycles) ===";
print "  |Z^1| =", #Z1;

// Step 3: Compute B^1 (1-coboundaries)
// B^1 = {h^(-1) * sigma(h) : h in G}
B1_set := {};
for h in G do
    b := h^(-1) * sigma_map(h);
    Include(~B1_set, b);
end for;
B1 := SetToSequence(B1_set);
print "";
print "=== B^1 (1-coboundaries) ===";
print "  |B^1| =", #B1;

// Sanity check: every coboundary is a cocycle
for b in B1 do
    assert b in Z1;
end for;
print "  Verified: B^1 subset Z^1";

// Step 4: Compute H^1 = Z^1 / ~
// g1 ~ g2 iff exists h in G with g1 = h^(-1) * g2 * sigma(h)
classes := [];
for i := 1 to #Z1 do
    g1 := Z1[i];
    already := false;
    for j := 1 to #classes do
        if g1 in classes[j] then
            already := true;
            break;
        end if;
    end for;
    if already then
        continue;
    end if;
    cls := {g1};
    for h in G do
        g2 := h^(-1) * g1 * sigma_map(h);
        Include(~cls, g2);
    end for;
    Append(~classes, cls);
end for;

print "";
print "=== H^1 (cohomology classes) ===";
print "  |H^1| =", #classes;

// Sanity check: classes partition Z^1
total := 0;
for cls in classes do
    total +:= #cls;
end for;
assert total eq #Z1;
print "  Verified: classes partition Z^1 (total", total, "=", #Z1, ")";

// Identify conjugacy classes of G for labeling
CC := ConjugacyClasses(G);
conj_class_label := func< g |
    exists(i){ i : i in [1..#CC] | g in Class(G, CC[i][3]) }
    select i else 0
>;

// Step 5: Print summary
print "";
print "=== Summary ===";
print "  |G| =", #G;
print "  |Z^1| =", #Z1;
print "  |B^1| =", #B1;
print "  |H^1| =", #classes;
print "";

for i := 1 to #classes do
    cls := classes[i];
    rep := Representative(cls);
    cc_idx := conj_class_label(rep);
    print "  Class", i, ": size", #cls,
          "| representative =", rep,
          "(order", Order(rep), ", conjugacy class", cc_idx, ")";
    if Id(G) in cls then
        print "    ^ This is the distinguished (trivial) class = B^1";
        assert cls eq B1_set;
    end if;
end for;

// =========================================================================
// Step 6: Symplectic lifting — which H^1(PSL) classes lift to H^1(SL)?
// SL(2,7) is the Schur cover of PSL(2,7), so every automorphism of PSL
// lifts uniquely to SL, preserving order. We derive sigma on PSL from
// sigma on SL via the quotient map to ensure compatibility.
// =========================================================================
print "";
print "========================================";
print "=== Symplectic lifting via SL(2,7) ===";
print "========================================";

F7 := GF(7);
G_sl := SL(2, F7);
Z_center := Center(G_sl);
G_psl2, pi := quo<G_sl | Z_center>;
print "SL(2,7): order", #G_sl, ", center order", #Z_center;

// Build preimage table for the quotient map
preimage := AssociativeArray();
for g in G_sl do
    x := pi(g);
    if not IsDefined(preimage, x) then
        preimage[x] := g;
    end if;
end for;

// Choose sigma on SL(2,7)
use_explicit_sigma := true;

if use_explicit_sigma then
    // Explicit model: sigma(a,b;c,d) = (a, zeta*b; zeta^-1*c, d)
    // where zeta is a primitive root mod 7. This is conjugation by
    // diag(alpha, alpha^-1) in GL(2,7) where alpha^2 = zeta (no such
    // alpha in F_7, so sigma is outer). Order = 6.
    zeta := PrimitiveElement(F7);
    print "Using explicit sigma: (a,b;c,d) -> (a,", zeta, "*b;",
          zeta^(-1), "*c, d)";
    sigma_sl_map := func<g |
        G_sl ! Matrix(F7, 2, 2, [g[1,1], zeta*g[1,2],
                                  zeta^(-1)*g[2,1], g[2,2]])
    >;
    // Verify order
    test := G_sl ! Matrix(F7, 2, 2, [1,1,0,1]);
    val := test;
    for k := 1 to sigma_order do val := sigma_sl_map(val); end for;
    assert val eq test;
    val := test;
    for k := 1 to sigma_order - 1 do val := sigma_sl_map(val); end for;
    assert val ne test;
    print "  Verified: explicit sigma has order", sigma_order;
else
    A_sl := AutomorphismGroup(G_sl);
    sigma_sl := Identity(A_sl);
    found_sl := false;

    for gen in Generators(A_sl) do
        ord := Order(gen);
        if ord mod sigma_order eq 0 then
            candidate := gen^(ord div sigma_order);
            if Order(candidate) eq sigma_order and not IsInner(candidate) then
                sigma_sl := candidate;
                found_sl := true;
                break;
            end if;
        end if;
    end for;

    if not found_sl then
        AutSet_sl := {A_sl ! 1};
        repeat
            for g1 in Generators(A_sl) do
                for g2 in AutSet_sl do
                    Include(~AutSet_sl, g1 * g2);
                end for;
            end for;
        until #AutSet_sl eq #A_sl;
        for elt in AutSet_sl do
            if Order(elt) eq sigma_order and not IsInner(elt) then
                sigma_sl := elt;
                found_sl := true;
                break;
            end if;
        end for;
    end if;

    assert found_sl;
    print "Found outer automorphism of SL(2,7) of order", sigma_order;
    sigma_sl_map := func<g | sigma_sl(g)>;
end if;

// Derive the induced sigma on PSL via pi
// sigma_psl(pi(g)) := pi(sigma_sl(g)) — well-defined since center is characteristic
sigma_psl2_tab := AssociativeArray();
for x in G_psl2 do
    g := preimage[x];
    sigma_psl2_tab[x] := pi(sigma_sl_map(g));
end for;
sigma_psl2 := func<x | sigma_psl2_tab[x]>;

// Compute Z^1 and H^1 for SL(2,7)
Z1_sl := [];
for g in G_sl do
    prod := Id(G_sl);
    val := g;
    for k := 0 to sigma_order - 1 do
        prod := prod * val;
        val := sigma_sl_map(val);
    end for;
    if prod eq Id(G_sl) then
        Append(~Z1_sl, g);
    end if;
end for;
print "";
print "  |Z^1(SL)| =", #Z1_sl;

classes_sl := [];
for i := 1 to #Z1_sl do
    g1 := Z1_sl[i];
    already := false;
    for j := 1 to #classes_sl do
        if g1 in classes_sl[j] then
            already := true;
            break;
        end if;
    end for;
    if already then continue; end if;
    cls := {g1};
    for h in G_sl do
        g2 := h^(-1) * g1 * sigma_sl_map(h);
        Include(~cls, g2);
    end for;
    Append(~classes_sl, cls);
end for;
print "  |H^1(SL)| =", #classes_sl;

for j := 1 to #classes_sl do
    rep := Representative(classes_sl[j]);
    print "    SL class", j, ": size", #classes_sl[j],
          ", rep order", Order(rep);
end for;

// Compute Z^1 and H^1 for PSL with the induced sigma
Z1_psl2 := [];
for g in G_psl2 do
    prod := Id(G_psl2);
    val := g;
    for k := 0 to sigma_order - 1 do
        prod := prod * val;
        val := sigma_psl2(val);
    end for;
    if prod eq Id(G_psl2) then
        Append(~Z1_psl2, g);
    end if;
end for;
print "";
print "  |Z^1(PSL, induced sigma)| =", #Z1_psl2;

classes_psl2 := [];
for i := 1 to #Z1_psl2 do
    g1 := Z1_psl2[i];
    already := false;
    for j := 1 to #classes_psl2 do
        if g1 in classes_psl2[j] then
            already := true;
            break;
        end if;
    end for;
    if already then continue; end if;
    cls := {g1};
    for h in G_psl2 do
        g2 := h^(-1) * g1 * sigma_psl2(h);
        Include(~cls, g2);
    end for;
    Append(~classes_psl2, cls);
end for;
print "  |H^1(PSL, induced sigma)| =", #classes_psl2;

// Project each SL class to PSL and track which PSL classes are hit
image_classes := {};
for j := 1 to #classes_sl do
    rep_sl := Representative(classes_sl[j]);
    rep_psl := pi(rep_sl);
    for k := 1 to #classes_psl2 do
        if rep_psl in classes_psl2[k] then
            Include(~image_classes, k);
            print "    SL class", j, "-> PSL class", k;
            break;
        end if;
    end for;
end for;

// Identify which PSL class is the trivial (distinguished) one
trivial_psl_class := 0;
for k := 1 to #classes_psl2 do
    if Id(G_psl2) in classes_psl2[k] then
        trivial_psl_class := k;
        break;
    end if;
end for;

print "";
print "=== Symplectic summary ===";
for k := 1 to #classes_psl2 do
    rep := Representative(classes_psl2[k]);
    is_symp := k in image_classes;
    triv := (k eq trivial_psl_class);
    label := "";
    if triv then label := " [trivial]"; end if;
    if is_symp then
        print "  PSL class", k, "(size", #classes_psl2[k],
              ", rep order", Order(rep), "):" cat label, "SYMPLECTIC";
    else
        print "  PSL class", k, "(size", #classes_psl2[k],
              ", rep order", Order(rep), "):" cat label, "NOT symplectic";
    end if;
end for;

// Print SL cocycle representatives (as matrices) for classes over the
// nontrivial PSL class
print "";
print "=== SL cocycle representatives over nontrivial PSL class ===";
for j := 1 to #classes_sl do
    rep_sl := Representative(classes_sl[j]);
    rep_psl := pi(rep_sl);
    psl_idx := 0;
    for k := 1 to #classes_psl2 do
        if rep_psl in classes_psl2[k] then
            psl_idx := k;
            break;
        end if;
    end for;
    if psl_idx ne trivial_psl_class then
        print "";
        print "  SL class", j, "-> PSL class", psl_idx;
        print "  Representative (order", Order(rep_sl), "):";
        print "   ", rep_sl;
    end if;
end for;

// =========================================================================
// Step 7: Twisted action on F_7^2
// The SL(2,7) action on F_7^2 is equivariant if we let sigma act on F_7^2
// by M_old = diag(zeta, 1), since sigma(M) = M_old * M * M_old^{-1}.
// Twisting by the cocycle rho gives a new action: sigma_new(v) = rho(sigma) * M_old * v.
// By the cocycle identity, (rho(sigma)*M_old)^n = rho(sigma^n)*M_old^n = I.
// =========================================================================
print "";
print "========================================";
print "=== Twisted action on F_7^2 ===";
print "========================================";

Mat2 := MatrixRing(F7, 2);
M_old := Mat2 ! [zeta, 0, 0, 1];
print "Old sigma action on F_7^2: M_old = diag(zeta, 1) =";
print " ", M_old;

// Verify equivariance: sigma(M) = M_old * M * M_old^{-1} for all M in SL(2,7)
equivariant := true;
for M in G_sl do
    lhs := Mat2 ! sigma_sl_map(M);
    rhs := M_old * (Mat2 ! M) * M_old^(-1);
    if lhs ne rhs then
        equivariant := false;
        break;
    end if;
end for;
assert equivariant;
print "Verified: sigma(M) = M_old * M * M_old^(-1) (equivariant)";

// Get cocycle representative over the nontrivial PSL class
rho_sigma := Id(G_sl);
for j := 1 to #classes_sl do
    rep_sl := Representative(classes_sl[j]);
    rep_psl := pi(rep_sl);
    psl_idx := 0;
    for k := 1 to #classes_psl2 do
        if rep_psl in classes_psl2[k] then
            psl_idx := k;
            break;
        end if;
    end for;
    if psl_idx ne trivial_psl_class then
        rho_sigma := rep_sl;
        break;
    end if;
end for;

print "";
print "Cocycle representative rho(sigma) =";
print " ", rho_sigma;

// Twisted action matrix: M_new = rho(sigma) * M_old
M_new := (Mat2 ! rho_sigma) * M_old;
print "";
print "Twisted sigma action: M_new = rho(sigma) * M_old =";
print " ", M_new;

// Verify M_new^n = I (valid Z/n action)
I2 := Mat2 ! 1;
assert M_new^sigma_order eq I2;
print "";
print "Verified: M_new^" cat IntegerToString(sigma_order) cat " = I";

// Find actual order of M_new
m_ord := 1;
pow := M_new;
while pow ne I2 do
    m_ord +:= 1;
    pow := pow * M_new;
end while;
print "Order of M_new:", m_ord;

print "";
print "Done.";
quit;
