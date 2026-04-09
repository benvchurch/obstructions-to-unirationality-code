/*******************************************************************************
 * exhaustive_F3.m
 *
 * Exhaustive search for ALL decompositions x^4+y^4+z^4 = Q1*Q3 - Q2^2
 * over F_3.  Handles all factorization patterns of F+Q2^2.
 *
 * Merged from: exhaustive_F3.m + halfdiv_F3.m
 *
 * Methodological note (from halfdiv_F3.m):
 *   The 2-torsion class is eta = [(1/2) div(q1)] where we halve ALL
 *   multiplicities (both zeros and poles) -- this is HalfDiv.
 *   HalfPositive only halves the positive part and gives a DIFFERENT divisor.
 *   Previous error: computing D1-D3 = div(Q2/Q3) which is always principal.
 *   Correct approach: use HalfDiv of div(q1) (or equivalently div(q3)).
 *
 * Sanity check: since Br(F_p) = 0, ALL of J[2](F_p) should be reachable.
 ******************************************************************************/

p := 3;
Fp := GF(p);
R<X,Y,Z> := PolynomialRing(Fp, 3);
Ff := X^4 + Y^4 + Z^4;

// Function field setup
Fpt<t> := FunctionField(Fp);
Fptu<u> := PolynomialRing(Fpt);
ff := u^4 + t^4 + 1;
assert IsIrreducible(ff);
FF := FunctionField(ff);
Cl, m := ClassGroup(FF);
invs := Invariants(Cl);
printf "Cl(C/F_%o) = ", p;
for i in [1..#invs] do
    if i gt 1 then printf " x "; end if;
    if invs[i] eq 0 then printf "Z"; else printf "Z/%oZ", invs[i]; end if;
end for;
printf "\n\n";

elt_t := FF ! t;
elt_u := FF.1;

// J[2]
e1 := 2*Cl.1; e2 := 2*Cl.2; e3 := 2*Cl.3;
J2 := sub<Cl | e1, e2, e3>;
printf "J[2](F_%o) has %o elements\n\n", p, #J2;

// =========== HELPER FUNCTIONS ===========

// HalfDiv: halve ALL multiplicities (zeros AND poles).
// Returns <false, _> if any multiplicity is odd.
function HalfDiv(D)
    B := D - D;
    for pl in Support(D) do
        v := Valuation(D, pl);
        if v mod 2 ne 0 then
            return false, B;
        end if;
        B := B + (v div 2) * pl;
    end for;
    return true, B;
end function;

// HalfPositive: halve only the POSITIVE multiplicities (zeros).
// WARNING: this is NOT the same as HalfDiv -- it ignores poles.
// Use HalfDiv for the correct 2-torsion class from quadric decompositions.
// HalfPositive is still useful for bitangent half-divisors.
function HalfPositive(D)
    B := D - D;
    for pl in Support(D) do
        v := Valuation(D, pl);
        if v gt 0 then
            B := B + (v div 2) * pl;
        end if;
    end for;
    return B;
end function;

// =========== QUADRIC PAIRING ENUMERATION ===========

// Given factorization of a degree-4 form, find ALL ways to write it as
// Q1*Q3 where both have total degree 2.
// fac = sequence of <irreducible_factor, multiplicity> pairs.
function AllQuadricPairings(G, fac)
    pairs := [];
    k := #fac;
    if k eq 0 then return pairs; end if;

    product := &*[f[1]^f[2] : f in fac];
    mons := Monomials(G);
    if #mons eq 0 then return pairs; end if;
    coeff_G := MonomialCoefficient(G, mons[1]);
    coeff_P := MonomialCoefficient(product, mons[1]);
    if coeff_P eq 0 then return pairs; end if;
    scalar := coeff_G / coeff_P;

    if k eq 1 then
        f1 := fac[1][1]; e1_ := fac[1][2]; d1 := TotalDegree(f1);
        for m1 in [0..e1_] do
            if m1*d1 eq 2 then
                Append(~pairs, <scalar * f1^m1, f1^(e1_-m1)>);
            end if;
        end for;
    elif k eq 2 then
        f1 := fac[1][1]; e1_ := fac[1][2]; d1 := TotalDegree(f1);
        f2 := fac[2][1]; e2_ := fac[2][2]; d2 := TotalDegree(f2);
        for m1 in [0..e1_] do for m2 in [0..e2_] do
            if m1*d1 + m2*d2 eq 2 then
                Append(~pairs, <scalar * f1^m1*f2^m2, f1^(e1_-m1)*f2^(e2_-m2)>);
            end if;
        end for; end for;
    elif k eq 3 then
        f1 := fac[1][1]; e1_ := fac[1][2]; d1 := TotalDegree(f1);
        f2 := fac[2][1]; e2_ := fac[2][2]; d2 := TotalDegree(f2);
        f3 := fac[3][1]; e3_ := fac[3][2]; d3 := TotalDegree(f3);
        for m1 in [0..e1_] do for m2 in [0..e2_] do for m3 in [0..e3_] do
            if m1*d1 + m2*d2 + m3*d3 eq 2 then
                Append(~pairs, <scalar * f1^m1*f2^m2*f3^m3,
                                f1^(e1_-m1)*f2^(e2_-m2)*f3^(e3_-m3)>);
            end if;
        end for; end for; end for;
    elif k eq 4 then
        f1 := fac[1][1]; e1_ := fac[1][2]; d1 := TotalDegree(f1);
        f2 := fac[2][1]; e2_ := fac[2][2]; d2 := TotalDegree(f2);
        f3 := fac[3][1]; e3_ := fac[3][2]; d3 := TotalDegree(f3);
        f4 := fac[4][1]; e4_ := fac[4][2]; d4 := TotalDegree(f4);
        for m1 in [0..e1_] do for m2 in [0..e2_] do
        for m3 in [0..e3_] do for m4 in [0..e4_] do
            if m1*d1 + m2*d2 + m3*d3 + m4*d4 eq 2 then
                Append(~pairs, <scalar * f1^m1*f2^m2*f3^m3*f4^m4,
                  f1^(e1_-m1)*f2^(e2_-m2)*f3^(e3_-m3)*f4^(e4_-m4)>);
            end if;
        end for; end for; end for; end for;
    end if;

    // Remove duplicates: (Q1,Q3) and (Q3,Q1) give same 2-torsion class
    unique := [];
    seen := {};
    for pair in pairs do
        s1 := Sprint(pair[1]); s2 := Sprint(pair[2]);
        if s1 le s2 then key := s1 cat "|" cat s2;
        else key := s2 cat "|" cat s1; end if;
        if not (key in seen) then
            Include(~seen, key);
            Append(~unique, pair);
        end if;
    end for;
    return unique;
end function;

// =========== 2-TORSION CLASS COMPUTATION ===========

// Compute 2-torsion class from decomposition F = Q1*Q3 - Q2^2.
// On C: Q1*Q3 = Q2^2, so div(Q1) has all even multiplicities.
// 2-torsion class = [(1/2) div(q1)|_C].
// If Q2=0, use HalfPositive of div(Q1/Q3) instead.
function TorsionClass(Q1_hom, Q2_hom, Q3_hom)
    q1_aff := Evaluate(Q1_hom, [elt_t, elt_u, FF!1]);
    q2_aff := Evaluate(Q2_hom, [elt_t, elt_u, FF!1]);
    q3_aff := Evaluate(Q3_hom, [elt_t, elt_u, FF!1]);

    if q3_aff eq 0 then
        return false, Cl!0;
    end if;

    if Q2_hom eq 0 then
        if q1_aff eq 0 then return false, Cl!0; end if;
        D := Divisor(q1_aff / q3_aff);
        half_D := HalfPositive(D) - HalfPositive(-D);
        return true, half_D @@ m;
    end if;

    if q2_aff eq 0 then
        if q1_aff eq 0 then return false, Cl!0; end if;
        D := Divisor(q1_aff / q3_aff);
        half_D := HalfPositive(D) - HalfPositive(-D);
        return true, half_D @@ m;
    end if;

    // Normal case: class = [div(Q2/Q3)|_C]
    D := Divisor(q2_aff / q3_aff);
    return true, D @@ m;
end function;

// =========== HALFDIV vs HALFPOSITIVE DEMONSTRATION ===========

print "=== HALFDIV vs HALFPOSITIVE DISTINCTION ===";
print "";

// Bitangent reference
L1 := elt_t + elt_u + 1;
L2 := elt_t + elt_u - 1;
L3 := elt_t - elt_u + 1;
B1 := HalfPositive(Divisor(L1));
B2 := HalfPositive(Divisor(L2));
B3 := HalfPositive(Divisor(L3));
P12 := (B1-B2) @@ m;
P13 := (B1-B3) @@ m;
V_rat := sub<Cl | P12, P13>;
printf "V_rat order in J[2]: %o\n\n", #(V_rat meet J2);

// Test: specific decomposition showing HalfDiv gives correct class
print "Test decomposition: Q1=X^2+2XY+Y^2+Z^2, Q2=XY+Z^2, Q3=X^2+XY+Y^2+2Z^2";
Q1h := X^2 + 2*X*Y + Y^2 + Z^2;
Q2h := X*Y + Z^2;
Q3h := X^2 + X*Y + Y^2 + 2*Z^2;
assert Q1h*Q3h - Q2h^2 eq Ff;

q1 := Evaluate(Q1h, [elt_t, elt_u, FF!1]);
D_q1 := Divisor(q1);
printf "div(q1):\n";
for pl in Support(D_q1) do
    v := Valuation(D_q1, pl);
    printf "  deg-%o, mult %o\n", Degree(pl), v;
end for;
ok1, half1 := HalfDiv(D_q1);
printf "All even? %o\n", ok1;
if ok1 then
    eta1 := half1 @@ m;
    printf "(1/2)div(q1) class = %o\n", eta1;
    printf "  In J[2]? %o, Zero? %o, in V_rat? %o\n\n",
           eta1 in J2, eta1 eq Cl!0, eta1 in V_rat;
end if;

// =========== FACTORIZATION PATTERN SURVEY ===========

print "=== FACTORIZATION PATTERN SURVEY ===";
pattern_counts := AssociativeArray();

for a in Fp do
for b in Fp do
for c in Fp do
for d in Fp do
for e_ in Fp do
for f_ in Fp do
    Q2 := a*X^2 + b*Y^2 + c*Z^2 + d*X*Y + e_*X*Z + f_*Y*Z;
    if Q2 eq 0 then continue; end if;
    G := Ff + Q2^2;
    fac := Factorization(G);
    pat := Sort([<TotalDegree(f[1]), f[2]> : f in fac]);
    pat_str := Sprint(pat);
    if IsDefined(pattern_counts, pat_str) then
        pattern_counts[pat_str] +:= 1;
    else
        pattern_counts[pat_str] := 1;
    end if;
end for;
end for;
end for;
end for;
end for;
end for;

print "Factorization patterns of F + Q2^2 (by degree,mult):";
for key in Keys(pattern_counts) do
    printf "  %o: %o times\n", key, pattern_counts[key];
end for;
print "";

// Does F itself factor (Q2=0 case)?
printf "Does F = X^4+Y^4+Z^4 factor over F_%o? ", p;
fac_F := Factorization(Ff);
printf "%o\n\n", fac_F;

// =========== MAIN EXHAUSTIVE SEARCH ===========

print "=== EXHAUSTIVE SEARCH OVER F_3 ===";
print "";

classes_found := {};
class_examples := AssociativeArray();
total_decomps := 0;
total_pairings := 0;
odd_count := 0;

for a in Fp do
for b in Fp do
for c in Fp do
for d in Fp do
for e_ in Fp do
for f_ in Fp do
    Q2 := a*X^2 + b*Y^2 + c*Z^2 + d*X*Y + e_*X*Z + f_*Y*Z;
    if Q2 eq 0 then continue; end if;

    G := Ff + Q2^2;
    fac := Factorization(G);

    pairs := AllQuadricPairings(G, fac);
    if #pairs eq 0 then continue; end if;

    total_decomps +:= 1;
    total_pairings +:= #pairs;

    for pair in pairs do
        Q1 := pair[1]; Q3 := pair[2];
        assert Q1*Q3 - Q2^2 eq Ff;

        // Method 1: TorsionClass via div(Q2/Q3)
        ok, cls := TorsionClass(Q1, Q2, Q3);
        if not ok then continue; end if;

        if cls in J2 then
            cls_str := Sprint(cls);
            if not (cls in classes_found) then
                Include(~classes_found, cls);
                class_examples[cls_str] := <Q1, Q2, Q3>;
                printf "NEW CLASS: %o\n", cls;
                printf "  Q2=%o, Q1=%o, Q3=%o\n", Q2, Q1, Q3;
            end if;
        end if;

        // Method 2 (cross-check): HalfDiv of div(q1)
        q1_ := Evaluate(Q1, [elt_t, elt_u, FF!1]);
        D_q1_ := Divisor(q1_);
        ok2, half_ := HalfDiv(D_q1_);
        if ok2 then
            cls2 := half_ @@ m;
            if cls2 in J2 and not (cls2 in classes_found) then
                Include(~classes_found, cls2);
                printf "NEW (via HalfDiv): %o  [zero?%o, V_rat?%o]\n",
                       cls2, cls2 eq Cl!0, cls2 in V_rat;
            end if;
        else
            odd_count +:= 1;
        end if;
    end for;
end for;
end for;
end for;
end for;
end for;
end for;

// =========== RESULTS ===========

printf "\n=== RESULTS ===\n";
printf "Total Q2 values giving a factorization: %o\n", total_decomps;
printf "Total (Q1,Q3) pairings: %o\n", total_pairings;
printf "Odd-multiplicity cases (HalfDiv skipped): %o\n", odd_count;
printf "Distinct classes in J[2]: %o\n", #classes_found;
printf "\nClasses found:\n";
for c in classes_found do
    printf "  %o", c;
    cs := Sprint(c);
    if IsDefined(class_examples, cs) then
        ex := class_examples[cs];
        printf "  (e.g. Q1=%o, Q2=%o, Q3=%o)", ex[1], ex[2], ex[3];
    end if;
    printf "\n";
end for;

V_decomp := sub<Cl | [c : c in classes_found]>;
V_decomp_J2 := V_decomp meet J2;
printf "\nSubspace from decompositions (in J[2]): order %o\n", #V_decomp_J2;
printf "J[2] has order %o\n", #J2;

if #V_decomp_J2 eq #J2 then
    print "";
    print "ALL of J[2] reached over F_3.";
    print "This confirms Br(F_3) = 0 (expected).";
    print "";
    print "The decomposition method works. Now the key question is:";
    print "which classes are reachable over Q?";
else
    printf "\nOnly %o/%o of J[2] reached.\n", #V_decomp_J2, #J2;
    print "UNEXPECTED: Br(F_3) = 0 should make all classes reachable.";
    print "There may be a bug in the search or class computation.";
end if;

quit;
