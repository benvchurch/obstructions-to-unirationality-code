/*******************************************************************************
 * phantom_Qi_check.m
 *
 * For f = A^2+3B^2+3D^2 (phantom quartic), Brauer class = (-1,-3)_Q.
 * Local invariants: inv_inf = 1/2, inv_3 = 1/2, all others 0.
 *
 * Q(i) splits this: Q_3(i)/Q_3 is unramified quad ext, kills inv_3.
 * Verify: eta becomes principal over F_49 = F_7(i) but not over F_7.
 *
 * Also check over F_3 vs F_9 = F_3(i) (since 3 is the bad prime).
 ******************************************************************************/

Q := Rationals();
Poly3<x,y,z> := PolynomialRing(Q, 3);

A := x^2-x*y-x*z+y^2-y*z+z^2;
B := x*y;
D := x^2-z^2;
f := A^2 + 3*B^2 + 3*D^2;

printf "=== Brauer class (-1,-3)_Q for phantom quartic ===\n\n";
printf "Local invariants:\n";
printf "  inf: inv = 1/2 (both -1,-3 negative)\n";
printf "  3:   inv = 1/2 (-1 is QNR mod 3)\n";
printf "  2:   inv = 0   (product formula)\n";
printf "  p>=5: inv = 0\n\n";

function HalfDiv(D)
    B := D - D;
    for pl in Support(D) do
        v := Valuation(D, pl);
        if v mod 2 ne 0 then return false, B; end if;
        B := B + (v div 2) * pl;
    end for;
    return true, B;
end function;

// === Test 1: F_7 (i not in F_7, sqrt(-3) = 2 in F_7) ===
printf "=== F_7: i NOT in F_7, sqrt(-3) = 2 ===\n";
p := 7;
Fp := GF(p);
w7 := Fp!2;  // 2^2 = 4 = -3 mod 7
printf "sqrt(-3) = %o, check: %o^2 = %o = %o\n", w7, w7, w7^2, Fp!(-3);

Fpx<t> := FunctionField(Fp);
Fpxy<u> := PolynomialRing(Fpx);
fp_aff := u^4+(-2*t-2)*u^3+(6*t^2+3)*u^2+(-2*t^3-2)*u+(4*t^4-2*t^3-3*t^2-2*t+4);
FF<uu> := FunctionField(fp_aff);
elt_t := FF!t;
elt_u := uu;

Aval := elt_t^2-elt_t*elt_u-elt_t+elt_u^2-elt_u+1;
Bval := elt_t*elt_u;
q1 := Aval + w7*Bval;

D_q1 := Divisor(q1);
printf "div(q1):\n";
for pl in Support(D_q1) do
    printf "  deg-%o, mult %o\n", Degree(pl), Valuation(D_q1, pl);
end for;

ok, D_half := HalfDiv(D_q1);
printf "All even: %o\n", ok;

if ok then
    V, _ := RiemannRochSpace(D_half);
    printf "dim L((1/2)div(q1)) = %o\n", Dimension(V);
    if Dimension(V) eq 0 then
        printf "=> eta != 0 over F_7\n\n";
    else
        printf "=> eta = 0 over F_7\n\n";
    end if;
end if;

// === Test 2: F_49 = F_7(i) ===
printf "=== F_49 = F_7(i): i exists here ===\n";
Fq := GF(49);
// Find sqrt(-1) in F_49
i49 := Fq!0;
for a in Fq do
    if a^2 eq Fq!(-1) then i49 := a; break; end if;
end for;
printf "i = %o, check: i^2 = %o\n", i49, i49^2;

// sqrt(-3) in F_49: same as in F_7 subset
w49 := Fq!2;
printf "sqrt(-3) = %o\n", w49;

Fqx<t2> := FunctionField(Fq);
Fqxy<u2> := PolynomialRing(Fqx);
fp2 := u2^4+(-2*t2-2)*u2^3+(6*t2^2+3)*u2^2+(-2*t2^3-2)*u2+(4*t2^4-2*t2^3-3*t2^2-2*t2+4);
FF2<uu2> := FunctionField(fp2);
elt_t2 := FF2!t2;
elt_u2 := uu2;

Aval2 := elt_t2^2-elt_t2*elt_u2-elt_t2+elt_u2^2-elt_u2+1;
Bval2 := elt_t2*elt_u2;
q1_49 := Aval2 + w49*Bval2;

D_q1_49 := Divisor(q1_49);
printf "div(q1):\n";
for pl in Support(D_q1_49) do
    printf "  deg-%o, mult %o\n", Degree(pl), Valuation(D_q1_49, pl);
end for;

ok49, D_half_49 := HalfDiv(D_q1_49);
printf "All even: %o\n", ok49;

if ok49 then
    V49, _ := RiemannRochSpace(D_half_49);
    printf "dim L((1/2)div(q1)) = %o\n", Dimension(V49);
    if Dimension(V49) ge 1 then
        printf "=> eta = 0 over F_49 (REPRESENTABLE!)\n\n";
    else
        printf "=> eta != 0 over F_49\n\n";
    end if;
end if;

// === Test 3: F_11 (i in F_11 since 11 = 3 mod 4? NO, 11=3 mod 4 => -1 QNR) ===
// Actually 11 mod 4 = 3, so -1 is QNR mod 11. i not in F_11.
// But sqrt(-3): (-3) mod 11 = 8. Is 8 a QR mod 11? 8 = 3^2? No: 1,4,9,5,3 are QR mod 11. 8 not QR.
// So sqrt(-3) not in F_11 either. Skip.

// === Test 4: F_5 (i in F_5? 5=1 mod 4, yes! sqrt(-1)=2 in F_5) ===
// sqrt(-3) mod 5: -3=2 mod 5. Is 2 a QR mod 5? QR mod 5: 1,4. No. sqrt(-3) not in F_5.
// Bad: f has bad reduction at 5? Let's check.
printf "=== F_5: checking ===\n";
p5 := 5;
Fp5 := GF(p5);
P2_5<xp,yp,zp> := ProjectiveSpace(Fp5, 2);
fp5 := Evaluate(f, [xp,yp,zp]);
Cp5 := Curve(P2_5, fp5);
printf "F_5 smooth: %o\n", IsNonsingular(Cp5);
// sqrt(-1) in F_5 = 2
printf "sqrt(-1) in F_5 = %o (check: %o)\n", Fp5!2, (Fp5!2)^2;
// sqrt(-3) not in F_5: check
printf "-3 mod 5 = %o, is QR: %o\n\n", Fp5!(-3), IsSquare(Fp5!(-3));

// === Test 5: F_13 (both i and sqrt(-3) in F_13) ===
printf "=== F_13: both i and sqrt(-3) exist ===\n";
p13 := 13;
Fp13 := GF(p13);
i13 := Fp13!5;  // 5^2=25=12=-1
w13 := Fp13!7;  // 7^2=49=10=-3
printf "i=%o (i^2=%o), sqrt(-3)=%o (w^2=%o)\n", i13, i13^2, w13, w13^2;

P2_13<xp,yp,zp> := ProjectiveSpace(Fp13, 2);
fp13 := Evaluate(f, [xp,yp,zp]);
Cp13 := Curve(P2_13, fp13);
printf "F_13 smooth: %o\n", IsNonsingular(Cp13);

Fp13x<t3> := FunctionField(Fp13);
Fp13y<u3> := PolynomialRing(Fp13x);
fp13_aff := u3^4+(-2*t3-2)*u3^3+(6*t3^2+3)*u3^2+(-2*t3^3-2)*u3+(4*t3^4-2*t3^3-3*t3^2-2*t3+4);
FF3<uu3> := FunctionField(fp13_aff);
elt_t3 := FF3!t3;
elt_u3 := uu3;

Aval3 := elt_t3^2-elt_t3*elt_u3-elt_t3+elt_u3^2-elt_u3+1;
Bval3 := elt_t3*elt_u3;
q1_13 := Aval3 + w13*Bval3;

D_q1_13 := Divisor(q1_13);
ok13, D_half_13 := HalfDiv(D_q1_13);
printf "Over F_13: (1/2)div(q1) defined: %o\n", ok13;

if ok13 then
    V13, _ := RiemannRochSpace(D_half_13);
    printf "dim L((1/2)div(q1)) = %o\n", Dimension(V13);
    if Dimension(V13) ge 1 then
        printf "=> eta = 0 over F_13 (principal)\n";
    else
        printf "=> eta != 0 over F_13\n";
    end if;
end if;

// Since both i and sqrt(-3) are in F_13, eta SHOULD be 0 if both
// Q(i) and Q(sqrt(-3)) split the Brauer class. But the Brauer class
// is (-1,-3) with inv at inf and 3 only. Over F_p there's no archimedean
// place, so the "obstruction" only exists at the bad prime p=3.
// At p=13, the class group is finite and the obstruction may or may not persist.

printf "\n=== SUMMARY ===\n";
printf "Brauer class: (-1, -3)_Q, ramified at inf and 3\n";
printf "Q(i) splits: Q_3(i)/Q_3 unramified quad ext kills inv_3\n";
printf "Expected: eta principal over F_49=F_7(i) but not F_7\n";
printf "  (since F_7 has sqrt(-3) but not i, and\n";
printf "   the class group reduction captures the 3-local obstruction)\n";

printf "\nDone.\n";
quit;
