/*******************************************************************************
 * groups1344.m
 *
 * Purpose:
 *   Search for Hurwitz groups of order 1344 = 84*16 in Magma's SmallGroups
 *   database. Order 1344 corresponds to Hurwitz curves of genus 17.
 *
 * Method:
 *   1. Iterate through all groups of order 1344 in SmallGroups database
 *   2. For each group, search for a spherical triple (g2, g3, g7) with
 *      orders (2, 3, 7) and g2*g3 = g7^(-1)
 *   3. Verify that the triple generates the entire group
 *
 * Additional analysis:
 *   - For the Hurwitz group found, analyze the normal subgroup structure
 *   - Build F_2-representation of quotient acting on normal subgroup
 *   - Study the GModule structure
 *
 * Output:
 *   - List of all Hurwitz groups of order 1344
 *   - F_2-representation matrices for the quotient action
 *
 * Dependencies:
 *   None (standalone computation)
 *
 * Mathematical background:
 *   There are 11686 groups of order 1344 in the SmallGroups database.
 *   Only one is a Hurwitz group (the automorphism group of the genus 17
 *   Hurwitz curve).
 ******************************************************************************/

L := SmallGroups(1344);
Hurwitz_groups := [];

for G in L do 
  for c in ConjugacyClasses(G) do
    if c[1] eq 2 then
      for g in G do
        if Order(g) eq 3 and Order(c[3]*g) eq 7 and Order(sub<G | c[3], g>) eq Order(G) then
          print G;
          Append(~Hurwitz_groups, G);
          break;
        end if;
      end for;
    end if;
  end for;
end for;

print "Number of Hurwitz Groups:", #Hurwitz_groups;
print "Groups:", Hurwitz_groups;

// After your existing code:
G := Hurwitz_groups[1];
N := NormalSubgroups(G)[2]`subgroup;
Q, pi := quo<G | N>;

// Convert N to F_2 vector space using PC presentation
F2 := GF(2);
n := 3;
V := VectorSpace(F2, n);

// Get generators of N
N_gens := [N.i : i in [2..4]];

// Function to get coordinates of an element in N
function GetCoords(x)
    for i in [1..2] do
      for j in [1..2] do
        for k in [1..2] do
          if x eq N_gens[1]^i*N_gens[2]^j*N_gens[3]^k then
            return [i mod 2, j mod 2, k mod 2];
          end if;
        end for;
      end for;
    end for;
    return [0,0,0];
end function;

// Build matrices for generators of Q
matrices := [];
for i in [1..Ngens(Q)] do
    q := Q.i;
    g := q @@ pi;  // Lift to G
    
    // Build matrix: j-th column is coordinates of N_gens[j]^g
    cols := [];
    for j in [1..n] do
        n_conj := N_gens[j]^g;
        Append(~cols, GetCoords(n_conj));
    end for;
    Append(~matrices, Matrix(F2, n, n, &cat[Eltseq(col) : col in cols]));
end for;

// Create GModule
M := GModule(Q, matrices);
phi := Representation(M);

print "Dimension:", Dimension(M);