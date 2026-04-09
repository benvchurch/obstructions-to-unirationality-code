/*******************************************************************************
 * H1_crossed_homs.m
 *
 * Purpose:
 *   Compute H^1(Gal(Q(sqrt(-7))/Q), PSL(2,7)) via crossed homomorphisms.
 *   The Galois group is Z/2 with generator sigma acting on PSL(2,7) by the
 *   unique (up to inner) outer automorphism of order 2.
 *
 * Method:
 *   1. Find the outer automorphism sigma of order 2 in Aut(PSL(2,7))
 *   2. Compute Z^1 = {g in G : g * sigma(g) = 1}
 *   3. Compute B^1 = {sigma(h) * h^(-1) : h in G}
 *   4. Compute H^1 = Z^1 / ~ where g1 ~ g2 iff exists h with g1 = sigma(h)*g2*h^(-1)
 *
 * Dependencies:
 *   None (standalone computation)
 ******************************************************************************/

// Step 1: Setup — find outer automorphism of order 2
G := PSL(2,7);
A := AutomorphismGroup(G);

// Find an outer automorphism of order 2
sigma := Identity(A);
found := false;

// First check generators and their powers
for gen in Generators(A) do
    ord := Order(gen);
    if ord eq 2 then
        if not IsInner(gen) then
            sigma := gen;
            found := true;
            break;
        end if;
    elif IsEven(ord) then
        candidate := gen^(ord div 2);
        if Order(candidate) eq 2 and not IsInner(candidate) then
            sigma := candidate;
            found := true;
            break;
        end if;
    end if;
end for;

// If not found in generators, search all elements
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
        if Order(elt) eq 2 and not IsInner(elt) then
            sigma := elt;
            found := true;
            break;
        end if;
    end for;
end if;

assert found;
print "Found outer automorphism sigma of order 2";

// Define sigma as a function on G
sigma_map := func< g | sigma(g) >;

// Step 2: Compute Z^1 (1-cocycles)
// A crossed hom Z/2 -> G is determined by g := f(sigma), with condition
// f(sigma^2) = f(sigma) * sigma(f(sigma)) = g * sigma(g) = 1
Z1 := [];
for g in G do
    if g * sigma_map(g) eq Id(G) then
        Append(~Z1, g);
    end if;
end for;
print "";
print "=== Z^1 (1-cocycles) ===";
print "  |Z^1| =", #Z1;

// Step 3: Compute B^1 (1-coboundaries)
// B^1 = {sigma(h) * h^(-1) : h in G}
B1_set := {};
for h in G do
    b := sigma_map(h) * h^(-1);
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
// g1 ~ g2 iff exists h in G with g1 = sigma(h) * g2 * h^(-1)
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
        g2 := sigma_map(h) * g1 * h^(-1);
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

print "";
print "Done.";
quit;
