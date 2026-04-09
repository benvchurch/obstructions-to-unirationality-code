/*******************************************************************************
 * check_Vrat_intersection.m
 *
 * Check: is the 2-dim intersection phi(J[2](C1)(Q)) ∩ J[2](C2)(Q)
 * exactly phi(V_rat(C1))?
 *
 * V_rat(C1) = subspace of J[2](C1)(Q) spanned by Q-rational bitangent diffs.
 * The 4 Q-rational bitangent lines of C1: x+y+z, x+y-z, x-y+z, -x+y+z.
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
        if v gt 0 then
            B := B + (v div 2) * pl;
        end if;
    end for;
    return B;
end function;

// ======================================================================
// Setup over F_9
// ======================================================================
F9<a> := GF(9);
z8 := PrimitiveElement(F9);
iz8 := 1/z8;

// C1
K1<t1> := FunctionField(F9);
R1<U1> := PolynomialRing(K1);
FF1<u1> := FunctionField(U1^4 + t1^4 + 1);
Cl1, m1 := ClassGroup(FF1);
inv1 := Invariants(Cl1);
j2g1 := J2Gens(Cl1, inv1);
n1 := #j2g1;

// C2
K2<t2> := FunctionField(F9);
R2<U2> := PolynomialRing(K2);
FF2<u2> := FunctionField(U2^4 + t2^4 - 1);
Cl2, m2 := ClassGroup(FF2);
inv2 := Invariants(Cl2);
j2g2 := J2Gens(Cl2, inv2);
n2 := #j2g2;

pls1 := Places(FF1, 1);
pls2 := Places(FF2, 1);
lookup1 := BuildUnifiedLookup(pls1, FF1, t1, u1, F9);
lookup2 := BuildUnifiedLookup(pls2, FF2, t2, u2, F9);

// ======================================================================
// Compute V_rat(C1): bitangent differences from x+y+z, x+y-z, x-y+z, -x+y+z
// In affine z=1: L1=t+u+1, L2=t+u-1, L3=t-u+1, L4=-t+u+1
// ======================================================================
print "=== V_rat(C1) from Q-rational bitangent lines ===";
elt_t1 := FF1 ! t1;
elt_u1 := FF1.1;

L1 := elt_t1 + elt_u1 + 1;   // x+y+z
L2 := elt_t1 + elt_u1 - 1;   // x+y-z
L3 := elt_t1 - elt_u1 + 1;   // x-y+z
L4 := -elt_t1 + elt_u1 + 1;  // -x+y+z

B1 := HalfPositive(Divisor(L1));
B2 := HalfPositive(Divisor(L2));
B3 := HalfPositive(Divisor(L3));
B4 := HalfPositive(Divisor(L4));

P12 := (B1 - B2) @@ m1;  // class of B1 - B2
P13 := (B1 - B3) @@ m1;
P14 := (B1 - B4) @@ m1;

printf "P12 = %o\n", P12;
printf "P13 = %o\n", P13;
printf "P14 = %o\n", P14;

// Check these are in J[2]
printf "P12 in J[2]? %o\n", 2*P12 eq Cl1!0;
printf "P13 in J[2]? %o\n", 2*P13 eq Cl1!0;
printf "P14 in J[2]? %o\n\n", 2*P14 eq Cl1!0;

// Express in J[2] basis
c12 := J2Coords(P12, j2g1, Cl1);
c13 := J2Coords(P13, j2g1, Cl1);
c14 := J2Coords(P14, j2g1, Cl1);
printf "P12 coords: %o\n", c12;
printf "P13 coords: %o\n", c13;
printf "P14 coords: %o\n\n", c14;

V2_1 := VectorSpace(GF(2), n1);
Vrat1 := sub<V2_1 | c12, c13, c14>;
printf "V_rat(C1) dim = %o, basis = %o\n\n", Dimension(Vrat1), Basis(Vrat1);

// ======================================================================
// Recompute Phi and Frob matrices (same as before)
// ======================================================================
print "=== Recomputing Frob_3 and Phi matrices ===";

// Frob_3 on C1
Frob1 := ZeroMatrix(GF(2), n1, n1);
for idx in [1..n1] do
    g := j2g1[idx];
    D := m1(g);
    imgD := DivisorGroup(FF1) ! 0;
    for P in Support(D) do
        val := Valuation(D, P);
        src_key := PlaceKey(P, FF1, t1, u1, F9);
        if not src_key[1] then
            tgt_key := <false, src_key[2]^3, src_key[3]^3>;
        else
            tgt_key := <true, src_key[2]^3, F9!0>;
        end if;
        imgD := imgD + val * (1*lookup1[Sprint(tgt_key)]);
    end for;
    img_cls := imgD @@ m1;
    coords := J2Coords(img_cls, j2g1, Cl1);
    for j in [1..n1] do Frob1[idx][j] := coords[j]; end for;
end for;

// Frob_3 on C2
Frob2 := ZeroMatrix(GF(2), n2, n2);
for idx in [1..n2] do
    g := j2g2[idx];
    D := m2(g);
    imgD := DivisorGroup(FF2) ! 0;
    for P in Support(D) do
        val := Valuation(D, P);
        src_key := PlaceKey(P, FF2, t2, u2, F9);
        if not src_key[1] then
            tgt_key := <false, src_key[2]^3, src_key[3]^3>;
        else
            tgt_key := <true, src_key[2]^3, F9!0>;
        end if;
        imgD := imgD + val * (1*lookup2[Sprint(tgt_key)]);
    end for;
    img_cls := imgD @@ m2;
    coords := J2Coords(img_cls, j2g2, Cl2);
    for j in [1..n2] do Frob2[idx][j] := coords[j]; end for;
end for;

// Phi: C1 -> C2
Phi := ZeroMatrix(GF(2), n1, n2);
for idx in [1..n1] do
    g := j2g1[idx];
    D := m1(g);
    imgD := DivisorGroup(FF2) ! 0;
    for P in Support(D) do
        val := Valuation(D, P);
        src_key := PlaceKey(P, FF1, t1, u1, F9);
        if not src_key[1] then
            tgt_key := <false, src_key[2]*iz8, src_key[3]*iz8>;
        else
            tgt_key := <true, src_key[2], F9!0>;
        end if;
        imgD := imgD + val * (1*lookup2[Sprint(tgt_key)]);
    end for;
    img_cls := imgD @@ m2;
    coords := J2Coords(img_cls, j2g2, Cl2);
    for j in [1..n2] do Phi[idx][j] := coords[j]; end for;
end for;

I1 := IdentityMatrix(GF(2), n1);
I2 := IdentityMatrix(GF(2), n2);
fixed1 := NullSpace(Frob1 + I1);
fixed2 := NullSpace(Frob2 + I2);
printf "J[2](C1/F_3) dim = %o\n", Dimension(fixed1);
printf "J[2](C2/F_3) dim = %o\n\n", Dimension(fixed2);

// ======================================================================
// Push V_rat(C1) through Phi and compare with intersection
// ======================================================================
print "=== COMPARISON ===";

V2_2 := VectorSpace(GF(2), n2);

// Push V_rat through Phi
phi_Vrat_basis := [v * Phi : v in Basis(Vrat1)];
phi_Vrat := sub<V2_2 | phi_Vrat_basis>;
printf "Phi(V_rat(C1)) dim = %o\n", Dimension(phi_Vrat);
printf "Phi(V_rat(C1)) basis = %o\n\n", Basis(phi_Vrat);

// Push full J[2](C1/F_3) through Phi
phi_fixed1_basis := [v * Phi : v in Basis(fixed1)];
phi_fixed1 := sub<V2_2 | phi_fixed1_basis>;

// Intersection
inter := phi_fixed1 meet fixed2;
printf "Phi(J[2](C1/F_3)) ∩ J[2](C2/F_3) dim = %o\n", Dimension(inter);
printf "intersection basis = %o\n\n", Basis(inter);

// THE KEY TEST
same := phi_Vrat eq inter;
printf "*** Phi(V_rat(C1)) = intersection? %o ***\n\n", same;

if same then
    print "YES: The 2-dim intersection is exactly Phi(V_rat(C1)).";
    print "The kernel of the Brauer obstruction is the part that 'survives' the twist.";
else
    print "NO: The intersection differs from Phi(V_rat(C1)).";
    printf "Phi(V_rat) ∩ inter dim = %o\n", Dimension(phi_Vrat meet inter);
end if;

// Also check: is V_rat(C1) inside J[2](C1/F_3)?
printf "\nV_rat(C1) ⊂ J[2](C1/F_3)? %o\n", Vrat1 subset fixed1;

// And what about the eta class?
// eta = e1+e2+e3 is the unique element of J[2](C1)(Q) \ V_rat(C1)
// (up to V_rat translates). Find it.
print "\n=== ETA CLASS ===";
for v in fixed1 do
    if v ne V2_1!0 and not (v in Vrat1) then
        printf "eta candidate: %o\n", v;
        phi_eta := v * Phi;
        printf "Phi(eta) = %o\n", phi_eta;
        printf "Phi(eta) in J[2](C2/F_3)? %o\n\n", phi_eta in fixed2;
    end if;
end for;

quit;
