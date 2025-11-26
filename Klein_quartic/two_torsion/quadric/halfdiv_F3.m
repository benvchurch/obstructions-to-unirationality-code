/*******************************************************************************
 * quadric_halfdiv.m
 *
 * CORRECTED 2-torsion class from quadric decomposition F = Q1*Q3 - Q2^2.
 *
 * The class is eta = [(1/2) div(q1)] where we halve ALL multiplicities
 * (both zeros and poles). This equals [D1 - H_inf] where D1 = (1/2)(zeros)
 * and H_inf = (1/2)(poles) = hyperplane section at z=0.
 *
 * Previous error: computed D1-D3 which equals div(Q2/Q3), always principal.
 ******************************************************************************/

p := 3;
Fp := GF(p);
R<X,Y,Z> := PolynomialRing(Fp, 3);
Ff := X^4 + Y^4 + Z^4;

Fpt<t> := FunctionField(Fp);
Fptu<u> := PolynomialRing(Fpt);
ff := u^4 + t^4 + 1;
FF := FunctionField(ff);
Cl, m := ClassGroup(FF);
elt_t := FF ! t;
elt_u := FF.1;

e1 := 2*Cl.1; e2 := 2*Cl.2; e3 := 2*Cl.3;
J2 := sub<Cl | e1, e2, e3>;
printf "J[2] order = %o\n", #J2;

// HalfDiv: halve ALL multiplicities (zeros AND poles)
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

function HalfPositive(D)
    B := D - D;
    for pl in Support(D) do
        v := Valuation(D, pl);
        if v gt 0 then B := B + (v div 2) * pl; end if;
    end for;
    return B;
end function;

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

// =========================================================================
// Test: specific decomposition
// =========================================================================
print "=== SPECIFIC DECOMPOSITION ===";
Q1h := X^2 + 2*X*Y + Y^2 + Z^2;
Q2h := X*Y + Z^2;
Q3h := X^2 + X*Y + Y^2 + 2*Z^2;
assert Q1h*Q3h - Q2h^2 eq Ff;

q1 := Evaluate(Q1h, [elt_t, elt_u, FF!1]);
q3 := Evaluate(Q3h, [elt_t, elt_u, FF!1]);

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
    printf "  In J[2]? %o, Zero? %o, = e3? %o, in V_rat? %o\n\n",
           eta1 in J2, eta1 eq Cl!0, eta1 eq e3, eta1 in V_rat;
end if;

D_q3 := Divisor(q3);
printf "div(q3):\n";
for pl in Support(D_q3) do
    v := Valuation(D_q3, pl);
    printf "  deg-%o, mult %o\n", Degree(pl), v;
end for;

ok3, half3 := HalfDiv(D_q3);
printf "All even? %o\n", ok3;
if ok3 then
    eta3 := half3 @@ m;
    printf "(1/2)div(q3) class = %o\n", eta3;
    printf "  = (1/2)div(q1)? %o\n\n", eta3 eq eta1;
end if;

// =========================================================================
// EXHAUSTIVE SEARCH over F_3
// =========================================================================
print "=== EXHAUSTIVE SEARCH OVER F_3 ===";

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
                Append(~pairs, <scalar*f1^m1, f1^(e1_-m1)>);
            end if;
        end for;
    elif k eq 2 then
        f1 := fac[1][1]; e1_ := fac[1][2]; d1 := TotalDegree(f1);
        f2 := fac[2][1]; e2_ := fac[2][2]; d2 := TotalDegree(f2);
        for m1 in [0..e1_] do for m2 in [0..e2_] do
            if m1*d1+m2*d2 eq 2 then
                Append(~pairs, <scalar*f1^m1*f2^m2, f1^(e1_-m1)*f2^(e2_-m2)>);
            end if;
        end for; end for;
    elif k eq 3 then
        f1 := fac[1][1]; e1_ := fac[1][2]; d1 := TotalDegree(f1);
        f2 := fac[2][1]; e2_ := fac[2][2]; d2 := TotalDegree(f2);
        f3 := fac[3][1]; e3_ := fac[3][2]; d3 := TotalDegree(f3);
        for m1 in [0..e1_] do for m2 in [0..e2_] do for m3 in [0..e3_] do
            if m1*d1+m2*d2+m3*d3 eq 2 then
                Append(~pairs, <scalar*f1^m1*f2^m2*f3^m3,
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
            if m1*d1+m2*d2+m3*d3+m4*d4 eq 2 then
                Append(~pairs, <scalar*f1^m1*f2^m2*f3^m3*f4^m4,
                  f1^(e1_-m1)*f2^(e2_-m2)*f3^(e3_-m3)*f4^(e4_-m4)>);
            end if;
        end for; end for; end for; end for;
    end if;
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

classes_found := {};
total := 0;
odd_count := 0;

for a in Fp do for b in Fp do for c in Fp do
for d in Fp do for ef in Fp do for ff_ in Fp do
    Q2 := a*X^2 + b*Y^2 + c*Z^2 + d*X*Y + ef*X*Z + ff_*Y*Z;
    if Q2 eq 0 then continue; end if;
    G := Ff + Q2^2;
    fac := Factorization(G);
    pairs := AllQuadricPairings(G, fac);
    for pair in pairs do
        Q1_ := pair[1]; Q3_ := pair[2];
        q1_ := Evaluate(Q1_, [elt_t, elt_u, FF!1]);
        D_q1_ := Divisor(q1_);
        ok, half_ := HalfDiv(D_q1_);
        total +:= 1;
        if ok then
            cls := half_ @@ m;
            if cls in J2 and not (cls in classes_found) then
                Include(~classes_found, cls);
                printf "NEW: %o  [zero?%o, e3?%o, V_rat?%o]  Q2=%o\n",
                       cls, cls eq Cl!0, cls eq e3, cls in V_rat, Q2;
            end if;
        else
            odd_count +:= 1;
        end if;
    end for;
end for; end for; end for;
end for; end for; end for;

printf "\n=== SUMMARY ===\n";
printf "Total pairings: %o, odd-mult skipped: %o\n", total, odd_count;
printf "Distinct J[2] classes found: %o\n", #classes_found;
for c in classes_found do
    printf "  %o [zero?%o, e3?%o, V_rat?%o]\n",
           c, c eq Cl!0, c eq e3, c in V_rat;
end for;

if #classes_found gt 0 then
    V_all := sub<Cl | [c : c in classes_found]>;
    V_all_J2 := V_all meet J2;
    printf "Span in J[2]: order %o / %o\n", #V_all_J2, #J2;
end if;

quit;
