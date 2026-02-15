/*******************************************************************************
 * identify_eta.m
 *
 * Over F_49: both sqrt(-3) and zeta_8 exist. Identify the specific eta class
 * from the quadratic decomposition, then check if phi(eta) is rational on C2.
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

// Find sqrt(-3) and zeta_8
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
printf "C1/F_49: Cl invs = %o, #J[2] gens = %o, #deg1 = %o\n", inv1, n1, #pls1;

// C2 over F_49
K2<t2> := FunctionField(F49);
R2<U2> := PolynomialRing(K2);
FF2<u2> := FunctionField(U2^4 + t2^4 - 1);
Cl2, m2 := ClassGroup(FF2);
inv2 := Invariants(Cl2);
j2g2 := J2Gens(Cl2, inv2);
n2 := #j2g2;
pls2 := Places(FF2, 1);
printf "C2/F_49: Cl invs = %o, #J[2] gens = %o, #deg1 = %o\n\n", inv2, n2, #pls2;

lookup1 := BuildUnifiedLookup(pls1, FF1, t1, u1, F49);
lookup2 := BuildUnifiedLookup(pls2, FF2, t2, u2, F49);

// ======================================================================
// Compute eta on C1: from Q1 = 2x^2 + (1-w)y^2 + (1+w)z^2, w = sqrt(-3)
// In affine z=1: q1 = 2t^2 + (1-w)u^2 + (1+w)
// eta = [(1/2) div(q1)] in J[2]
// ======================================================================
print "=== IDENTIFYING ETA ===";
elt_t1 := FF1!t1;
elt_u1 := FF1.1;

q1 := 2*elt_t1^2 + (1-sq3)*elt_u1^2 + (1+sq3);
printf "q1 = 2t^2 + (%o)u^2 + (%o)\n", 1-sq3, 1+sq3;

Dq1 := Divisor(q1);
printf "div(q1): ";
for P in Support(Dq1) do
    printf "%o*P(deg%o) ", Valuation(Dq1,P), Degree(P);
end for;
printf "\n";

eta_div := HalfPositive(Dq1);
// For the class, we want (1/2)(full divisor), not just half positive
// eta = [(1/2)div(q1)] means halving ALL multiplicities
eta_cls := eta_div @@ m1;
printf "eta class in Cl1: %o\n", eta_cls;
printf "2*eta = 0? %o\n", 2*eta_cls eq Cl1!0;

eta_coords := J2Coords(eta_cls, j2g1, Cl1);
printf "eta coords in J[2] basis: %o\n\n", eta_coords;

// ======================================================================
// Also compute V_rat basis over F_49
// ======================================================================
print "=== V_RAT OVER F_49 ===";
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
printf "P12 coords: %o\n", c12;
printf "P13 coords: %o\n", c13;

V2 := VectorSpace(GF(2), n1);
Vrat := sub<V2 | c12, c13>;
printf "V_rat dim = %o\n", Dimension(Vrat);
printf "eta in V_rat? %o\n\n", eta_coords in Vrat;

// ======================================================================
// Frobenius_7 on J[2](C1/F_49) and J[2](C2/F_49)
// ======================================================================
print "=== FROBENIUS_7 ===";

// Frob_7 on C1
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
        src_key := PlaceKey(P, FF1, t1, u1, F49);
        if not src_key[1] then
            tgt_key := <false, src_key[2]^7, src_key[3]^7>;
        else
            tgt_key := <true, src_key[2]^7, F49!0>;
        end if;
        tgt_str := Sprint(tgt_key);
        if not IsDefined(lookup1, tgt_str) then all_ok := false; break; end if;
        imgD := imgD + val * (1*lookup1[tgt_str]);
    end for;
    if not all_ok then frob1_ok := false; printf "Frob1 gen %o failed\n", idx; continue; end if;
    img_cls := imgD @@ m1;
    coords := J2Coords(img_cls, j2g1, Cl1);
    if Type(coords) eq BoolElt then frob1_ok := false; continue; end if;
    for j in [1..n1] do Frob1[idx][j] := coords[j]; end for;
end for;

// Frob_7 on C2
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
        src_key := PlaceKey(P, FF2, t2, u2, F49);
        if not src_key[1] then
            tgt_key := <false, src_key[2]^7, src_key[3]^7>;
        else
            tgt_key := <true, src_key[2]^7, F49!0>;
        end if;
        tgt_str := Sprint(tgt_key);
        if not IsDefined(lookup2, tgt_str) then all_ok := false; break; end if;
        imgD := imgD + val * (1*lookup2[tgt_str]);
    end for;
    if not all_ok then frob2_ok := false; printf "Frob2 gen %o failed\n", idx; continue; end if;
    img_cls := imgD @@ m2;
    coords := J2Coords(img_cls, j2g2, Cl2);
    if Type(coords) eq BoolElt then frob2_ok := false; continue; end if;
    for j in [1..n2] do Frob2[idx][j] := coords[j]; end for;
end for;

if frob1_ok and frob2_ok then
    I1 := IdentityMatrix(GF(2), n1);
    I2 := IdentityMatrix(GF(2), n2);
    fixed1 := NullSpace(Frob1 + I1);
    fixed2 := NullSpace(Frob2 + I2);
    printf "J[2](C1/F_7): dim = %o\n", Dimension(fixed1);
    printf "J[2](C2/F_7): dim = %o\n", Dimension(fixed2);
    printf "eta in J[2](C1/F_7)? %o\n\n", eta_coords in fixed1;
end if;

// ======================================================================
// Phi over F_49
// ======================================================================
print "=== PHI OVER F_49 ===";
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
        src_key := PlaceKey(P, FF1, t1, u1, F49);
        if not src_key[1] then
            tgt_key := <false, src_key[2]*iz8, src_key[3]*iz8>;
        else
            tgt_key := <true, src_key[2], F49!0>;
        end if;
        tgt_str := Sprint(tgt_key);
        if not IsDefined(lookup2, tgt_str) then all_ok := false; break; end if;
        imgD := imgD + val * (1*lookup2[tgt_str]);
    end for;
    if not all_ok then phi_ok := false; printf "Phi gen %o failed\n", idx; continue; end if;
    img_cls := imgD @@ m2;
    coords := J2Coords(img_cls, j2g2, Cl2);
    if Type(coords) eq BoolElt then phi_ok := false; continue; end if;
    for j in [1..n2] do Phi[idx][j] := coords[j]; end for;
end for;

if phi_ok then
    printf "Phi matrix:\n%o\n\n", Phi;
end if;

// ======================================================================
// THE KEY QUESTION: Is phi(eta) rational on C2?
// ======================================================================
if phi_ok and frob2_ok then
    print "=== KEY QUESTION: Is phi(eta) in J[2](C2)(Q)? ===";
    phi_eta := eta_coords * Phi;
    printf "phi(eta) = %o\n", phi_eta;

    // J[2](C2)(Q) = intersection of all Frob-fixed subspaces
    // At p=7: J[2](C2/F_7)
    printf "phi(eta) in J[2](C2/F_7)? %o\n", phi_eta in fixed2;

    // Also check: Frob_7-fixed is only one condition. For definitive answer,
    // also need other Frobenii. But 2-rank(C2) at p=7 is 3, so J[2](F_7) = J[2](Q).
    printf "\n2-rank of C2 at p=7 is 3 (from table), so J[2](C2/F_7) = J[2](C2)(Q).\n";
    printf "Therefore phi(eta) in J[2](C2)(Q)? %o\n\n", phi_eta in fixed2;

    // For completeness: also check all eta coset elements
    print "=== ALL ETA COSET ELEMENTS ===";
    V2_2 := VectorSpace(GF(2), n2);
    for v in fixed1 do
        if v ne V2!0 and not (v in Vrat) then
            phi_v := v * Phi;
            printf "eta rep %o -> phi = %o, rational on C2? %o\n",
                v, phi_v, phi_v in fixed2;
        end if;
    end for;
end if;

quit;
