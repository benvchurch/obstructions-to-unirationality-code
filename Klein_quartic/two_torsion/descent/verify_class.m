/*******************************************************************************
 * verify_sqrt3_class.m
 *
 * Verify that the Q(sqrt(-3)) decomposition reduces mod 3 to the one
 * giving the non-V_rat 2-torsion class.
 ******************************************************************************/

p := 3;
Fp := GF(p);
R<X,Y,Z> := PolynomialRing(Fp, 3);
Ff := X^4 + Y^4 + Z^4;

// The Q(sqrt(-3)) decomposition, reduced mod 3 (w -> 0)
// Then apply (X,Y,Z) -> (Y,Z,X) to match F_3 form
Q2_red := Y^2 + Z^2;
Q1_red := X^2 + Y^2 + 2*Z^2;
Q3_red := X^2 + 2*Y^2 + Z^2;
assert Q1_red * Q3_red - Q2_red^2 eq Ff;
print "Reduction mod 3 verified: F = Q1*Q3 - Q2^2";
printf "  Q1 = %o, Q2 = %o, Q3 = %o\n\n", Q1_red, Q2_red, Q3_red;

// Now compute the 2-torsion class
Fpt<t> := FunctionField(Fp);
Fptu<u> := PolynomialRing(Fpt);
ff := u^4 + t^4 + 1;
FF := FunctionField(ff);
Cl, m := ClassGroup(FF);
elt_t := FF ! t;
elt_u := FF.1;

e1 := 2*Cl.1; e2 := 2*Cl.2; e3 := 2*Cl.3;
J2 := sub<Cl | e1, e2, e3>;

function HalfDiv(D)
    B := D - D;
    for pl in Support(D) do
        v := Valuation(D, pl);
        if v mod 2 ne 0 then return false, B; end if;
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

// Evaluate on C (z=1, x=t, y=u)
q1 := Evaluate(Q1_red, [elt_t, elt_u, FF!1]);
D_q1 := Divisor(q1);
ok, half := HalfDiv(D_q1);
printf "div(q1) all even? %o\n", ok;

if ok then
    eta := half @@ m;
    printf "(1/2)div(q1) = %o\n", eta;
    printf "  In J[2]? %o\n", eta in J2;
    printf "  Zero? %o\n", eta eq Cl!0;
    printf "  In V_rat? %o\n", eta in V_rat;
    printf "  = e3? %o\n", eta eq e3;
    printf "  = e1+e2+e3? %o\n", eta eq e1+e2+e3;
end if;

quit;
