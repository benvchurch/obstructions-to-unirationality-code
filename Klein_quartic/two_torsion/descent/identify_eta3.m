/*******************************************************************************
 * identify_eta3.m — minimal: just push eta through phi and check rationality
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
    B := D - D;
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

// C1 and C2 over F_49
K1<t1> := FunctionField(F49);
R1<U1> := PolynomialRing(K1);
FF1<u1> := FunctionField(U1^4 + t1^4 + 1);
Cl1, m1 := ClassGroup(FF1);
inv1 := Invariants(Cl1);
j2g1 := J2Gens(Cl1, inv1);
n1 := #j2g1;
pls1 := Places(FF1, 1);

K2<t2> := FunctionField(F49);
R2<U2> := PolynomialRing(K2);
FF2<u2> := FunctionField(U2^4 + t2^4 - 1);
Cl2, m2 := ClassGroup(FF2);
inv2 := Invariants(Cl2);
j2g2 := J2Gens(Cl2, inv2);
n2 := #j2g2;
pls2 := Places(FF2, 1);

lookup2 := BuildUnifiedLookup(pls2, FF2, t2, u2, F49);

// ======================================================================
// Compute eta = [(1/2)div(q1)] where q1 = 2t^2 + (1-sqrt(-3))u^2 + (1+sqrt(-3))
// ======================================================================
elt_t1 := FF1!t1; elt_u1 := FF1.1;
q1 := 2*elt_t1^2 + (1-sq3)*elt_u1^2 + (1+sq3);
Dq1 := Divisor(q1);
half_Dq1 := HalfDivisor(Dq1);
eta_cls := half_Dq1 @@ m1;
assert 2*eta_cls eq Cl1!0;

eta_coords := J2Coords(eta_cls, j2g1, Cl1);
printf "eta = %o\n", eta_coords;

// V_rat
L1 := elt_t1+elt_u1+1; L2 := elt_t1+elt_u1-1; L3 := elt_t1-elt_u1+1;
B1 := HalfPositive(Divisor(L1)); B2 := HalfPositive(Divisor(L2)); B3 := HalfPositive(Divisor(L3));
c12 := J2Coords((B1-B2) @@ m1, j2g1, Cl1);
c13 := J2Coords((B1-B3) @@ m1, j2g1, Cl1);
V2 := VectorSpace(GF(2), n1);
Vrat := sub<V2 | c12, c13>;
printf "V_rat = <%o, %o>\n", c12, c13;
printf "eta in V_rat? %o\n\n", eta_coords in Vrat;

// ======================================================================
// Push eta directly through phi (divisor-level, not matrix)
// phi: (t,u) on C1 -> (t/z8, u/z8) on C2
// ======================================================================
print "=== PUSHING ETA THROUGH PHI ===";

// The divisor half_Dq1 represents eta on C1
// Push each place through phi
imgD := DivisorGroup(FF2) ! 0;
all_ok := true;
for P in Support(half_Dq1) do
    val := Valuation(half_Dq1, P);
    if Degree(P) ne 1 then
        printf "Problem: degree-%o place in eta support\n", Degree(P);
        all_ok := false;
        break;
    end if;
    sk := PlaceKey(P, FF1, t1, u1, F49);
    if not sk[1] then
        tk := <false, sk[2]*iz8, sk[3]*iz8>;
    else
        tk := <true, sk[2], F49!0>;
    end if;
    tgt_str := Sprint(tk);
    if not IsDefined(lookup2, tgt_str) then
        printf "Problem: phi target %o not found\n", tgt_str;
        all_ok := false;
        break;
    end if;
    imgD := imgD + val * (1*lookup2[tgt_str]);
end for;

if all_ok then
    phi_eta_cls := imgD @@ m2;
    phi_eta := J2Coords(phi_eta_cls, j2g2, Cl2);
    printf "phi(eta) = %o\n\n", phi_eta;
else
    print "Direct pushforward failed.";
end if;

// ======================================================================
// Is phi(eta) rational? Check via Frob_7 on C2
// ======================================================================
print "=== RATIONALITY CHECK VIA FROB_7 ON C2 ===";

// Compute Frob_7 on the single element phi(eta)
// Frob_7 on imgD: (t0,u0) -> (t0^7, u0^7)
frobD := DivisorGroup(FF2) ! 0;
frob_ok := true;
for P in Support(imgD) do
    val := Valuation(imgD, P);
    if Degree(P) ne 1 then frob_ok := false; break; end if;
    sk := PlaceKey(P, FF2, t2, u2, F49);
    if not sk[1] then
        tk := <false, sk[2]^7, sk[3]^7>;
    else
        tk := <true, sk[2]^7, F49!0>;
    end if;
    tgt_str := Sprint(tk);
    if not IsDefined(lookup2, tgt_str) then frob_ok := false; break; end if;
    frobD := frobD + val * (1*lookup2[tgt_str]);
end for;

if all_ok and frob_ok then
    frob_phi_eta := J2Coords(frobD @@ m2, j2g2, Cl2);
    printf "Frob_7(phi(eta)) = %o\n", frob_phi_eta;
    printf "phi(eta) = %o\n", phi_eta;
    printf "Frob_7 fixes phi(eta)? %o\n\n", frob_phi_eta eq phi_eta;

    // 2-rank(C2, p=7) = 3 from our table, so Frob_7-fixed = J[2](C2)(Q).
    if frob_phi_eta eq phi_eta then
        print "phi(eta) is fixed by Frob_7 => phi(eta) IN J[2](C2)(Q).";
        print "*** The Brauer-obstructed class STAYS RATIONAL on C2. ***";
    else
        print "phi(eta) is NOT fixed by Frob_7 => phi(eta) NOT in J[2](C2)(Q).";
        print "*** The Brauer-obstructed class does NOT stay rational on C2. ***";
    end if;
else
    print "Frobenius pushforward failed.";
end if;

// ======================================================================
// Double-check: also verify with Frob_3 using F_9 embedding
// ======================================================================
print "\n=== CROSS-CHECK: USE F_9 DATA ===";
print "From F_9 run: Phi matrix (rows are images of J[2] gens):";
print "[1 0 0 0 1 1]";
print "[0 0 0 0 0 1]";
print "[1 1 0 0 1 0]";
print "[1 0 1 0 1 0]";
print "[0 1 0 1 1 0]";
print "[1 0 0 1 1 1]";
print "";
print "From F_9 run: J[2](C2/F_3) basis: (1 0 0 0 0 0), (0 1 0 0 0 1), (0 0 0 1 1 1)";
print "";
print "But the F_9 and F_49 bases are DIFFERENT. Cannot directly compare.";
print "The F_49 computation is self-consistent and definitive for Frob_7.";

quit;
