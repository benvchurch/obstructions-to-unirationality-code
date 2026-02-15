/*******************************************************************************
 * identify_eta2.m — fixed: halve ALL multiplicities for eta
 ******************************************************************************/

function J2Gens(Cl, invs)
    gens := [];
    for i in [1..#invs] do
        if invs[i] ne 0 and invs[i] mod 2 eq 0 then
            Append(~gens, (invs[i] div 2) * Cl.i);
        end if;
    end for;
    return gens;
end function;

function J2Coords(h, j2_gens, Cl)
    n := #j2_gens;
    for bits in [0..2^n-1] do
        sum := Cl!0;
        for i in [1..n] do
            if (bits div 2^(i-1)) mod 2 eq 1 then
                sum := sum + j2_gens[i];
            end if;
        end for;
        if sum eq h then
            return Vector(GF(2), [GF(2)!((bits div 2^(i-1)) mod 2) : i in [1..n]]);
        end if;
    end for;
    return false;
end function;

function PlaceKey(P, FF, t_var, u_var, k)
    if Valuation(FF!t_var, P) ge 0 and Valuation(u_var, P) ge 0 then
        return <false, k!Evaluate(FF!t_var, P), k!Evaluate(u_var, P)>;
    else
        return <true, k!Evaluate(u_var / (FF!t_var), P), k!0>;
    end if;
end function;

function BuildUnifiedLookup(places, FF, t_var, u_var, k)
    tab := AssociativeArray();
    for P in places do
        key := PlaceKey(P, FF, t_var, u_var, k);
        tab[Sprint(key)] := P;
    end for;
    return tab;
end function;

function HalfDivisor(D)
    // Halve ALL multiplicities (positive and negative)
    B := D - D;  // zero divisor
    for P in Support(D) do
        v := Valuation(D, P);
        assert v mod 2 eq 0;
        B := B + (v div 2) * (1*P);
    end for;
    return B;
end function;

function HalfPositive(D)
    B := D - D;
    for pl in Support(D) do
        v := Valuation(D, pl);
        if v gt 0 then B := B + (v div 2) * pl; end if;
    end for;
    return B;
end function;

// ======================================================================
F49<w49> := GF(49);
sq3 := Sqrt(F49!(-3));
z8 := 0;
for x in F49 do
    if x ne 0 and x^4 eq F49!(-1) then z8 := x; break; end if;
end for;
iz8 := 1/z8;
printf "F_49: sqrt(-3) = %o, zeta_8 = %o\n\n", sq3, z8;

// C1 over F_49
K1<t1> := FunctionField(F49);
R1<U1> := PolynomialRing(K1);
FF1<u1> := FunctionField(U1^4 + t1^4 + 1);
Cl1, m1 := ClassGroup(FF1);
inv1 := Invariants(Cl1);
j2g1 := J2Gens(Cl1, inv1);
n1 := #j2g1;
pls1 := Places(FF1, 1);

// C2 over F_49
K2<t2> := FunctionField(F49);
R2<U2> := PolynomialRing(K2);
FF2<u2> := FunctionField(U2^4 + t2^4 - 1);
Cl2, m2 := ClassGroup(FF2);
inv2 := Invariants(Cl2);
j2g2 := J2Gens(Cl2, inv2);
n2 := #j2g2;
pls2 := Places(FF2, 1);

lookup1 := BuildUnifiedLookup(pls1, FF1, t1, u1, F49);
lookup2 := BuildUnifiedLookup(pls2, FF2, t2, u2, F49);

printf "C1/F_49: #J[2] gens = %o, #deg1 = %o\n", n1, #pls1;
printf "C2/F_49: #J[2] gens = %o, #deg1 = %o\n\n", n2, #pls2;

// ======================================================================
// Compute eta: halve ALL multiplicities of div(q1)
// q1 = 2x^2 + (1-w)y^2 + (1+w)z^2, w = sqrt(-3)
// ======================================================================
print "=== ETA FROM QUADRATIC DECOMPOSITION ===";
elt_t1 := FF1!t1;
elt_u1 := FF1.1;

q1 := 2*elt_t1^2 + (1-sq3)*elt_u1^2 + (1+sq3);
Dq1 := Divisor(q1);

// Check all valuations are even
for P in Support(Dq1) do
    v := Valuation(Dq1, P);
    printf "  val = %o at deg-%o place\n", v, Degree(P);
end for;

half_Dq1 := HalfDivisor(Dq1);
eta_cls := half_Dq1 @@ m1;
printf "\neta class: %o\n", eta_cls;
printf "2*eta = 0? %o\n", 2*eta_cls eq Cl1!0;

eta_coords := J2Coords(eta_cls, j2g1, Cl1);
if Type(eta_coords) eq BoolElt then
    printf "eta not in J[2]! Trying negative...\n";
    eta_cls2 := (-half_Dq1) @@ m1;
    printf "neg eta class: %o, 2*eta=0? %o\n", eta_cls2, 2*eta_cls2 eq Cl1!0;
    eta_coords := J2Coords(eta_cls2, j2g1, Cl1);
    if Type(eta_coords) ne BoolElt then
        eta_cls := eta_cls2;
    end if;
end if;
printf "eta coords: %o\n\n", eta_coords;

// ======================================================================
// V_rat basis
// ======================================================================
print "=== V_RAT ===";
L1 := elt_t1 + elt_u1 + 1;
L2 := elt_t1 + elt_u1 - 1;
L3 := elt_t1 - elt_u1 + 1;
B1 := HalfPositive(Divisor(L1));
B2 := HalfPositive(Divisor(L2));
B3 := HalfPositive(Divisor(L3));
P12 := (B1-B2) @@ m1;
P13 := (B1-B3) @@ m1;
c12 := J2Coords(P12, j2g1, Cl1);
c13 := J2Coords(P13, j2g1, Cl1);
printf "P12: %o\nP13: %o\n", c12, c13;

V2 := VectorSpace(GF(2), n1);
Vrat := sub<V2 | c12, c13>;
printf "V_rat dim = %o\n", Dimension(Vrat);
if Type(eta_coords) ne BoolElt then
    printf "eta in V_rat? %o\n\n", eta_coords in Vrat;
end if;

// ======================================================================
// Frob_7 on both curves
// ======================================================================
print "=== FROBENIUS_7 ===";
Frob1 := ZeroMatrix(GF(2), n1, n1);
frob1_ok := true;
for idx in [1..n1] do
    g := j2g1[idx];
    D := m1(g);
    imgD := DivisorGroup(FF1) ! 0;
    all_ok := true;
    for P in Support(D) do
        val := Valuation(D, P);
        if Degree(P) ne 1 then all_ok := false; break; end if;
        sk := PlaceKey(P, FF1, t1, u1, F49);
        if not sk[1] then tk := <false, sk[2]^7, sk[3]^7>;
        else tk := <true, sk[2]^7, F49!0>; end if;
        if not IsDefined(lookup1, Sprint(tk)) then all_ok := false; break; end if;
        imgD := imgD + val * (1*lookup1[Sprint(tk)]);
    end for;
    if not all_ok then frob1_ok := false; continue; end if;
    co := J2Coords(imgD @@ m1, j2g1, Cl1);
    if Type(co) eq BoolElt then frob1_ok := false; continue; end if;
    for j in [1..n1] do Frob1[idx][j] := co[j]; end for;
end for;

Frob2 := ZeroMatrix(GF(2), n2, n2);
frob2_ok := true;
for idx in [1..n2] do
    g := j2g2[idx];
    D := m2(g);
    imgD := DivisorGroup(FF2) ! 0;
    all_ok := true;
    for P in Support(D) do
        val := Valuation(D, P);
        if Degree(P) ne 1 then all_ok := false; break; end if;
        sk := PlaceKey(P, FF2, t2, u2, F49);
        if not sk[1] then tk := <false, sk[2]^7, sk[3]^7>;
        else tk := <true, sk[2]^7, F49!0>; end if;
        if not IsDefined(lookup2, Sprint(tk)) then all_ok := false; break; end if;
        imgD := imgD + val * (1*lookup2[Sprint(tk)]);
    end for;
    if not all_ok then frob2_ok := false; continue; end if;
    co := J2Coords(imgD @@ m2, j2g2, Cl2);
    if Type(co) eq BoolElt then frob2_ok := false; continue; end if;
    for j in [1..n2] do Frob2[idx][j] := co[j]; end for;
end for;

if frob1_ok then
    I1 := IdentityMatrix(GF(2), n1);
    fixed1 := NullSpace(Frob1 + I1);
    printf "J[2](C1/F_7) dim = %o\n", Dimension(fixed1);
else
    printf "Frob_7 on C1 failed\n";
end if;

if frob2_ok then
    I2 := IdentityMatrix(GF(2), n2);
    fixed2 := NullSpace(Frob2 + I2);
    printf "J[2](C2/F_7) dim = %o\n\n", Dimension(fixed2);
else
    printf "Frob_7 on C2 failed\n";
end if;

// ======================================================================
// Phi over F_49
// ======================================================================
Phi := ZeroMatrix(GF(2), n1, n2);
phi_ok := true;
for idx in [1..n1] do
    g := j2g1[idx];
    D := m1(g);
    imgD := DivisorGroup(FF2) ! 0;
    all_ok := true;
    for P in Support(D) do
        val := Valuation(D, P);
        if Degree(P) ne 1 then all_ok := false; break; end if;
        sk := PlaceKey(P, FF1, t1, u1, F49);
        if not sk[1] then tk := <false, sk[2]*iz8, sk[3]*iz8>;
        else tk := <true, sk[2], F49!0>; end if;
        if not IsDefined(lookup2, Sprint(tk)) then all_ok := false; break; end if;
        imgD := imgD + val * (1*lookup2[Sprint(tk)]);
    end for;
    if not all_ok then phi_ok := false; continue; end if;
    co := J2Coords(imgD @@ m2, j2g2, Cl2);
    if Type(co) eq BoolElt then phi_ok := false; continue; end if;
    for j in [1..n2] do Phi[idx][j] := co[j]; end for;
end for;

// ======================================================================
// ANSWER
// ======================================================================
print "================================================================";
print "ANSWER: Is phi(eta) in J[2](C2)(Q)?";
print "================================================================";

if Type(eta_coords) ne BoolElt and phi_ok and frob2_ok then
    phi_eta := eta_coords * Phi;
    printf "eta on C1:     %o\n", eta_coords;
    printf "phi(eta) on C2: %o\n", phi_eta;
    printf "phi(eta) in J[2](C2/F_7)? %o\n\n", phi_eta in fixed2;

    // 2-rank(C2) at p=7 is 3 (from table), so J[2](C2/F_7) = J[2](C2)(Q).
    printf "Since 2-rank(C2,p=7) = 3 = dim J[2](Q), we have J[2](C2/F_7) = J[2](C2)(Q).\n\n";

    if phi_eta in fixed2 then
        print "*** YES: The specific eta (from Q_1 decomposition) STAYS RATIONAL on C2. ***";
    else
        print "*** NO: The specific eta (from Q_1 decomposition) is NOT RATIONAL on C2. ***";
    end if;

    // Also show all coset elements
    printf "\nAll elements of J[2](C1)(Q) \\ V_rat and their phi-images:\n";
    if frob1_ok then
        for v in fixed1 do
            if v ne V2!0 and not (v in Vrat) then
                pv := v * Phi;
                rat := pv in fixed2;
                is_eta := (Type(eta_coords) ne BoolElt) and (v eq eta_coords);
                tag := "";
                if is_eta then tag := " <-- THIS IS ETA"; end if;
                printf "  %o -> %o  rational? %o%o\n", v, pv, rat, tag;
            end if;
        end for;
    end if;
else
    if Type(eta_coords) eq BoolElt then print "Could not identify eta in J[2] basis."; end if;
    if not phi_ok then print "Phi computation failed."; end if;
    if not frob2_ok then print "Frob_7 on C2 failed."; end if;
end if;

quit;
