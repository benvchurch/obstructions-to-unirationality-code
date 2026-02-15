/*******************************************************************************
 * tau_full_J2.m
 *
 * Compute the τ-fixed subspace of the FULL J[2](F̄) = (Z/2Z)^6 for C2.
 * Work at p ≡ 1 mod 8 where J[2](F_p) = (Z/2Z)^6.
 *
 * Strategy: generate J[2] from degree-1 place differences. Use pairwise
 * and triple differences to span as much as possible.
 ******************************************************************************/

function J2Subgroup(Cl, invs)
    gens := [];
    for i in [1..#invs] do
        if invs[i] ne 0 and invs[i] mod 2 eq 0 then
            Append(~gens, (invs[i] div 2) * Cl.i);
        end if;
    end for;
    if #gens eq 0 then return sub<Cl | Cl!0>; end if;
    return sub<Cl | gens>;
end function;

// Use p=17 where ζ₈ exists and J[2] = (Z/2Z)^6
p := 17;
printf "Working at p = %o (p mod 8 = %o)\n", p, p mod 8;
Fp := GF(p);

// Find i and ζ₈ in F_p
ii := Fp!0;
for x in Fp do
    if x ne 0 and x^2 eq Fp!(-1) then ii := x; break; end if;
end for;
z8 := Fp!0;
for x in Fp do
    if x ne 0 and x^4 eq Fp!(-1) then z8 := x; break; end if;
end for;
printf "i = %o, ζ₈ = %o (ζ₈⁴ = %o)\n", ii, z8, z8^4;

Fpt<tt> := FunctionField(Fp);
Fptu<uu> := PolynomialRing(Fpt);

FF2<vv> := FunctionField(uu^4 + tt^4 - 1);
Cl2, mm2 := ClassGroup(FF2);
invs2 := Invariants(Cl2);
J2_sub := J2Subgroup(Cl2, invs2);
printf "Cl(C2/F_%o) = %o\n|J[2]| = %o (should be 64)\n\n", p, invs2, #J2_sub;

// Enumerate affine degree-1 places
pls2 := Places(FF2, 1);
aff2 := [];
coord_lookup := AssociativeArray();
for P in pls2 do
    if Valuation(FF2!tt, P) lt 0 or Valuation(vv, P) lt 0 then continue; end if;
    tv := Fp!Evaluate(FF2!tt, P);
    uv := Fp!Evaluate(vv, P);
    Append(~aff2, P);
    coord_lookup[Sprint(<tv, uv>)] := P;
end for;
printf "Affine deg-1 places: %o\n", #aff2;

// Also get degree-2 places
pls2_d2 := Places(FF2, 2);
printf "Degree-2 places: %o\n", #pls2_d2;

// Build τ map on affine places: (t,u) -> (t/i, u/i)
inv_i := Fp!(1/ii);
tau_map := AssociativeArray();
for P in aff2 do
    tv := Fp!Evaluate(FF2!tt, P);
    uv := Fp!Evaluate(vv, P);
    target := <tv * inv_i, uv * inv_i>;
    key := Sprint(target);
    if IsDefined(coord_lookup, key) then
        tau_map[P] := coord_lookup[key];
    end if;
end for;
printf "τ maps %o/%o affine places\n", #Keys(tau_map), #aff2;

// Generate J[2] elements from place differences
P0 := aff2[1];
printf "Reference: P0 = (%o, %o)\n\n",
    Fp!Evaluate(FF2!tt, P0), Fp!Evaluate(vv, P0);

// Collect classes from all pairwise differences
j2_gens := [];
for i in [1..#aff2] do
    for j in [i+1..#aff2] do
        D := 1*aff2[i] - 1*aff2[j];
        cls := D @@ mm2;
        Append(~j2_gens, cls);
    end for;
end for;

// Also try triple differences: [P+Q-R-S] for all quadruples
for i in [1..#aff2] do
    for j in [i+1..#aff2] do
        for k in [1..#aff2] do
            if k eq i or k eq j then continue; end if;
            for l in [k+1..#aff2] do
                if l eq i or l eq j then continue; end if;
                D := 1*aff2[i] + 1*aff2[j] - 1*aff2[k] - 1*aff2[l];
                cls := D @@ mm2;
                Append(~j2_gens, cls);
            end for;
        end for;
    end for;
end for;

j2_from_places := sub<Cl2 | j2_gens> meet J2_sub;
printf "J[2] elements reachable from place differences: %o/%o\n",
    #j2_from_places, #J2_sub;

// Test τ on reachable elements
// For each g in j2_from_places, we need a deg-1-only representative.
// Strategy: for each g, try all representations as [P_i - P_j].
printf "\n=== TESTING τ ON REACHABLE J[2] ELEMENTS ===\n";

// First, build a lookup: class -> list of (i,j) pairs with [P_i - P_j] = class
class_reps := AssociativeArray();
for i in [1..#aff2] do
    for j in [1..#aff2] do
        if i eq j then continue; end if;
        D := 1*aff2[i] - 1*aff2[j];
        cls := D @@ mm2;
        if cls in J2_sub then
            key := Sprint(cls);
            if not IsDefined(class_reps, key) then
                class_reps[key] := [];
            end if;
            Append(~class_reps[key], <i, j>);
        end if;
    end for;
end for;

// Also build reps from sums of two differences: [P_a-P_b] + [P_c-P_d]
// = [P_a+P_c - P_b-P_d]
for a in [1..#aff2] do
for b in [1..#aff2] do
    if a eq b then continue; end if;
    D1 := 1*aff2[a] - 1*aff2[b];
    cls1 := D1 @@ mm2;
    if not (cls1 in J2_sub) then continue; end if;
    for c in [1..#aff2] do
    for d in [1..#aff2] do
        if c eq d then continue; end if;
        D2 := 1*aff2[c] - 1*aff2[d];
        cls2 := D2 @@ mm2;
        if not (cls2 in J2_sub) then continue; end if;
        sum_cls := cls1 + cls2;
        if sum_cls eq Cl2!0 then continue; end if;
        if not (sum_cls in J2_sub) then continue; end if;
        key := Sprint(sum_cls);
        if not IsDefined(class_reps, key) then
            class_reps[key] := [];
            // Store as a 4-tuple: sum of [P_a-P_b] + [P_c-P_d]
            // We'll use pairs of pairs
        end if;
        // Only need one rep per class, and we already have single-pair reps
        // if they exist. Skip to save time.
    end for;
    end for;
end for;
end for;

printf "Classes with deg-1 representatives: %o\n", #Keys(class_reps);

// Now test τ
tau_fixed_count := 1;  // identity is always fixed
tau_nontrivial_count := 0;
untestable := 0;

for g in j2_from_places do
    if g eq Cl2!0 then continue; end if;
    key := Sprint(g);

    if IsDefined(class_reps, key) then
        // Use first available rep
        rep := class_reps[key][1];
        Pi := aff2[rep[1]]; Pj := aff2[rep[2]];

        // Apply τ: [τ(P_i) - τ(P_j)]
        if IsDefined(tau_map, Pi) and IsDefined(tau_map, Pj) then
            tau_D := 1*tau_map[Pi] - 1*tau_map[Pj];
            tau_g := tau_D @@ mm2;
            if tau_g eq g then
                tau_fixed_count +:= 1;
            else
                tau_nontrivial_count +:= 1;
            end if;
        else
            untestable +:= 1;
        end if;
    else
        untestable +:= 1;
    end if;
end for;

printf "\nResults:\n";
printf "  Fixed by τ: %o (including identity)\n", tau_fixed_count;
printf "  Moved by τ: %o\n", tau_nontrivial_count;
printf "  Untestable: %o\n", untestable;
total := tau_fixed_count + tau_nontrivial_count;
printf "  Total tested: %o/%o\n", total, #j2_from_places;

if untestable eq 0 and total eq #j2_from_places then
    // fixed subspace is a subgroup
    fixed_dim := 0;
    n := tau_fixed_count;
    while n gt 1 do n := n div 2; fixed_dim +:= 1; end while;
    printf "  τ-fixed subspace dimension: %o (out of 6)\n", fixed_dim;
    if fixed_dim lt 3 then
        printf "\n  Since dim(τ-fixed) = %o < 3 = dim(J[2](Q)),\n", fixed_dim;
        printf "  the 3-dim subspace J[2](Q) CANNOT be contained in τ-fixed.\n";
        printf "  Therefore φ_*(J[2](Q)_C1) ≠ J[2](Q)_C2.\n";
        printf "  CONCLUSION: The J[2](Q) subspaces are DIFFERENT.\n";
    else
        printf "\n  dim(τ-fixed) = %o >= 3, so subspaces MIGHT be the same.\n", fixed_dim;
        printf "  Further analysis needed.\n";
    end if;
end if;

quit;
