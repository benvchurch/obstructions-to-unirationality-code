/*******************************************************************************
 * compare_twists.m
 *
 * Task 3: Compare 2-torsion of C1: x^4+y^4+z^4=0 and C2: x^4+y^4-z^4=0.
 * C2 is the Q(i)-twist of C1 (via z -> iz) and has Q-point (1:0:1).
 *
 * Questions:
 * - How does J(C2)[2](Q) compare with J(C1)[2](Q)?
 * - Does the problematic class eta transport to V_rat(C2)?
 * - What are the Q-rational bitangent lines of C2?
 ******************************************************************************/

// =========================================================================
// Part A: 2-rank comparison across primes
// =========================================================================
print "=== PART A: 2-RANK COMPARISON ===";
printf "%-5o %-6o %-6o %-10o %-10o\n", "p", "p%4", "p%8", "2rk(C1)", "2rk(C2)";

for p in [3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97] do
    Fp := GF(p);
    Fpt<t> := FunctionField(Fp);
    Fptu<u> := PolynomialRing(Fpt);

    // C1: u^4 + t^4 + 1 = 0
    f1 := u^4 + t^4 + 1;
    if not IsIrreducible(f1) then
        printf "%-5o %-6o %-6o C1 red\n", p, p mod 4, p mod 8;
        continue;
    end if;
    FF1 := FunctionField(f1);
    Cl1 := ClassGroup(FF1);
    invs1 := Invariants(Cl1);
    rk1 := #[d : d in invs1 | d mod 2 eq 0];

    // C2: u^4 + t^4 - 1 = 0
    f2 := u^4 + t^4 - 1;
    if not IsIrreducible(f2) then
        printf "%-5o %-6o %-6o %-10o C2 red\n", p, p mod 4, p mod 8, rk1;
        continue;
    end if;
    FF2 := FunctionField(f2);
    Cl2 := ClassGroup(FF2);
    invs2 := Invariants(Cl2);
    rk2 := #[d : d in invs2 | d mod 2 eq 0];

    printf "%-5o %-6o %-6o %-10o %-10o\n", p, p mod 4, p mod 8, rk1, rk2;
end for;

// =========================================================================
// Part B: Detailed analysis at p=5 (smallest p ≡ 1 mod 4)
// At p ≡ 1 mod 4, sqrt(-1) exists so C1 ≅ C2 over F_p.
// =========================================================================
print "\n=== PART B: EXPLICIT ISOMORPHISM AT p=5 ===";
p := 5; Fp := GF(p);
ii := Sqrt(Fp!(-1));  // i in F_5
printf "p = %o, i = sqrt(-1) = %o\n", p, ii;

Fpt<t> := FunctionField(Fp);
Fptu<u> := PolynomialRing(Fpt);

// C1: u^4 + t^4 + 1 (affine z=1, so x=t, y=u)
f1 := u^4 + t^4 + 1;
assert IsIrreducible(f1);
FF1<uu1> := FunctionField(f1);
Cl1, m1 := ClassGroup(FF1);
invs1 := Invariants(Cl1);
printf "Cl(C1/F_%o) = ", p;
for i in [1..#invs1] do
    if i gt 1 then printf " x "; end if;
    printf "Z/%oZ", invs1[i];
end for;
printf "\n";

// J[2] basis for C1
e1_1 := 2*Cl1.1; e2_1 := 2*Cl1.2; e3_1 := 2*Cl1.3;
J2_1 := sub<Cl1 | e1_1, e2_1, e3_1>;
printf "J(C1)[2] has order %o\n", #J2_1;

// C2: u^4 + t^4 - 1 (affine z=1, so x=t, y=u)
f2 := u^4 + t^4 - 1;
assert IsIrreducible(f2);
FF2<uu2> := FunctionField(f2);
Cl2, m2 := ClassGroup(FF2);
invs2 := Invariants(Cl2);
printf "\nCl(C2/F_%o) = ", p;
for i in [1..#invs2] do
    if i gt 1 then printf " x "; end if;
    printf "Z/%oZ", invs2[i];
end for;
printf "\n";

e1_2 := 2*Cl2.1; e2_2 := 2*Cl2.2; e3_2 := 2*Cl2.3;
J2_2 := sub<Cl2 | e1_2, e2_2, e3_2>;
printf "J(C2)[2] has order %o\n", #J2_2;

// =========================================================================
// Q-rational bitangent analysis for C1 (reference)
// Bitangent lines of C1: x+y+z, x+y-z, x-y+z, -x+y+z
// In affine (z=1): L = t+u+1, t+u-1, t-u+1, -t+u+1
// =========================================================================
print "\n--- C1 bitangent classes ---";
elt_t1 := FF1 ! t; elt_u1 := FF1.1;

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

L1_1 := elt_t1 + elt_u1 + 1;  // x+y+z
L2_1 := elt_t1 + elt_u1 - 1;  // x+y-z
L3_1 := elt_t1 - elt_u1 + 1;  // x-y+z
L4_1 := -elt_t1 + elt_u1 + 1; // -x+y+z

B1_1 := HalfPositive(Divisor(L1_1));
B2_1 := HalfPositive(Divisor(L2_1));
B3_1 := HalfPositive(Divisor(L3_1));
B4_1 := HalfPositive(Divisor(L4_1));

P12_1 := (B1_1 - B2_1) @@ m1;
P13_1 := (B1_1 - B3_1) @@ m1;
P14_1 := (B1_1 - B4_1) @@ m1;

printf "P12 = %o, P13 = %o, P14 = %o\n", P12_1, P13_1, P14_1;
V_rat_1 := sub<Cl1 | P12_1, P13_1>;
printf "V_rat(C1) order = %o\n", #(V_rat_1 meet J2_1);

// The problematic class eta = e1+e2+e3 (in J[2] \ V_rat)
// Find it: any element of J2 not in V_rat
printf "\nJ[2] \\ V_rat classes:\n";
for g in J2_1 do
    if g ne Cl1!0 and not (g in V_rat_1) then
        printf "  %o\n", g;
    end if;
end for;

// =========================================================================
// Q-rational bitangent analysis for C2
// Under twist z -> iz: bitangent x+y+z=0 of C1 -> x+y+iz=0 of C2
// In affine z=1: t+u+i for C2 (not F_p-rational when p ≡ 3 mod 4)
// But C2 may have its OWN Q-rational bitangent lines.
// =========================================================================
print "\n--- C2 bitangent analysis ---";
elt_t2 := FF2 ! t; elt_u2 := FF2.1;

// First, check the TWISTED bitangent lines (from C1's Q-rational bitangents)
// These are: x+y+iz=0, x+y-iz=0, x-y+iz=0, -x+y+iz=0
// In affine (z=1): t+u+i, t+u-i, t-u+i, -t+u+i
// At p=5 where i exists, these ARE F_p-rational.

Lt1 := elt_t2 + elt_u2 + ii;   // x+y+iz
Lt2 := elt_t2 + elt_u2 - ii;   // x+y-iz
Lt3 := elt_t2 - elt_u2 + ii;   // x-y+iz
Lt4 := -elt_t2 + elt_u2 + ii;  // -x+y+iz

printf "Twisted bitangent lines (from C1 via z->iz):\n";
for idx in [1..4] do
    L := [Lt1, Lt2, Lt3, Lt4][idx];
    D := Divisor(L);
    supp := Support(D);
    degs := [Degree(pl) : pl in supp];
    vals := [Valuation(D, pl) : pl in supp];
    printf "  L%o: support degs = %o, vals = %o\n", idx, degs, vals;
end for;

Bt1 := HalfPositive(Divisor(Lt1));
Bt2 := HalfPositive(Divisor(Lt2));
Bt3 := HalfPositive(Divisor(Lt3));
Bt4 := HalfPositive(Divisor(Lt4));

Pt12 := (Bt1 - Bt2) @@ m2;
Pt13 := (Bt1 - Bt3) @@ m2;
Pt14 := (Bt1 - Bt4) @@ m2;

printf "\nTwisted bitangent classes in J(C2)[2]:\n";
printf "Pt12 = %o, Pt13 = %o, Pt14 = %o\n", Pt12, Pt13, Pt14;
V_twist := sub<Cl2 | Pt12, Pt13>;
printf "Span of twisted bitangent diffs: order %o\n", #(V_twist meet J2_2);

// Now search for Q-RATIONAL bitangent lines of C2 directly
// These would be lines ax+by+cz=0 with a,b,c in Q that are bitangent to C2.
// In affine: at+bu+c. Search over F_p coefficients.
print "\n--- Searching for bitangent lines of C2 over F_5 ---";
bitangent_classes := {};
bitangent_lines := [];

for a in Fp do
for b in Fp do
for c in Fp do
    if <a,b,c> eq <0,0,0> then continue; end if;
    L := a*elt_t2 + b*elt_u2 + c;
    if L eq 0 then continue; end if;
    D := Divisor(L);
    // A bitangent line meets C in 2 degree-1 places, each with multiplicity 2
    // So div(L) on C should have support with all valuations even
    supp := Support(D);
    vals := [Valuation(D, pl) : pl in supp];
    pos_vals := [v : v in vals | v gt 0];
    if #pos_vals ge 2 and forall{v : v in pos_vals | v mod 2 eq 0} then
        all_deg1 := forall{pl : pl in supp | Valuation(D,pl) le 0 or Degree(pl) eq 1};
        if all_deg1 then
            Bh := HalfPositive(D);
            // Reference: use first bitangent found
            if #bitangent_lines eq 0 then
                Append(~bitangent_lines, <a,b,c>);
                printf "  Bitangent: %o*x + %o*y + %o*z (reference)\n", a, b, c;
            else
                cls := (Bh - HalfPositive(Divisor(bitangent_lines[1][1]*elt_t2 + bitangent_lines[1][2]*elt_u2 + bitangent_lines[1][3]))) @@ m2;
                if cls in J2_2 then
                    Include(~bitangent_classes, cls);
                    Append(~bitangent_lines, <a,b,c>);
                    printf "  Bitangent: %o*x + %o*y + %o*z, class = %o\n", a, b, c, cls;
                end if;
            end if;
        end if;
    end if;
end for;
end for;
end for;

printf "\nTotal bitangent lines found over F_%o: %o\n", p, #bitangent_lines;
printf "Distinct J[2] classes from bitangents: %o\n", #bitangent_classes;

// =========================================================================
// Part C: Transport eta from C1 to C2
// The isomorphism phi: C1 -> C2 is (x:y:z) -> (x:y:iz)
// In affine z=1: (t,u) on C1 maps to (t/iz, u/iz) = (t/(iz), u/(iz)) on C2
// Wait: if (x:y:z) -> (x:y:iz), then in affine z=1:
//   C1 point (t,u,1) -> (t:u:i) = (t/i : u/i : 1) on C2
//   So t_C2 = t/i = -it, u_C2 = u/i = -iu
// =========================================================================
print "\n=== PART C: TRANSPORT eta VIA ISOMORPHISM ===";

// The quadric Q1 on C1 that defines D: Q1 = 2x^2 + (1-w)y^2 + (1+w)z^2
// where w = sqrt(-3). In affine z=1: q1 = 2t^2 + (1-w)u^2 + (1+w).
// eta = [(1/2)div(q1)] in J(C1)[2].

if IsSquare(Fp!(-3)) then
    w := Sqrt(Fp!(-3));
    printf "w = sqrt(-3) = %o\n", w;

    q1_C1 := 2*elt_t1^2 + (1-w)*elt_u1^2 + (1+w);
    printf "q1 on C1: %o\n", q1_C1;
    Dq1 := Divisor(q1_C1);
    eta_div := HalfPositive(Dq1) - HalfPositive(-Dq1);
    eta := eta_div @@ m1;
    printf "eta in J(C1)[2]: %o\n", eta;
    printf "eta in V_rat(C1)? %o\n", eta in V_rat_1;
    printf "eta in J[2]? %o\n", eta in J2_1;

    // Transport q1 to C2 via phi: (t,u) -> (-it, -iu) on C2
    // q1(t,u) = 2t^2 + (1-w)u^2 + (1+w)
    // q1(phi^{-1}(t',u')) where phi^{-1}: (t',u') -> (it', iu')
    // = 2(it')^2 + (1-w)(iu')^2 + (1+w)
    // = -2t'^2 - (1-w)u'^2 + (1+w)
    q1_C2 := -2*elt_t2^2 - (1-w)*elt_u2^2 + (1+w);
    printf "\nq1 transported to C2: %o\n", q1_C2;
    Dq1_2 := Divisor(q1_C2);
    eta_div_2 := HalfPositive(Dq1_2) - HalfPositive(-Dq1_2);
    eta_2 := eta_div_2 @@ m2;
    printf "eta transported to J(C2)[2]: %o\n", eta_2;
    printf "eta_2 in J(C2)[2]? %o\n", eta_2 in J2_2;

    // Is the transported eta in V_twist (the span of twisted bitangent diffs)?
    printf "eta_2 in V_twist? %o\n", eta_2 in V_twist;
else
    printf "sqrt(-3) does not exist in F_%o, skipping Part C.\n", p;
end if;

// =========================================================================
// Part D: Repeat at p=13 (both sqrt(-1) and sqrt(-3) exist)
// =========================================================================
print "\n=== PART D: SAME ANALYSIS AT p=13 ===";
p := 13; Fp := GF(p);
ii := Sqrt(Fp!(-1));
w := Sqrt(Fp!(-3));
printf "p=%o, i=%o, w=sqrt(-3)=%o\n", p, ii, w;

Fpt<t> := FunctionField(Fp);
Fptu<u> := PolynomialRing(Fpt);

// C1
FF1<uu1> := FunctionField(u^4 + t^4 + 1);
Cl1, m1 := ClassGroup(FF1);
invs1 := Invariants(Cl1);
elt_t1 := FF1 ! t; elt_u1 := FF1.1;
e1_1 := 2*Cl1.1; e2_1 := 2*Cl1.2; e3_1 := 2*Cl1.3;
J2_1 := sub<Cl1 | e1_1, e2_1, e3_1>;

// V_rat(C1)
L1_1 := elt_t1+elt_u1+1; L2_1 := elt_t1+elt_u1-1;
L3_1 := elt_t1-elt_u1+1; L4_1 := -elt_t1+elt_u1+1;
B1_1 := HalfPositive(Divisor(L1_1)); B2_1 := HalfPositive(Divisor(L2_1));
B3_1 := HalfPositive(Divisor(L3_1));
P12_1 := (B1_1-B2_1) @@ m1; P13_1 := (B1_1-B3_1) @@ m1;
V_rat_1 := sub<Cl1 | P12_1, P13_1>;

// eta on C1
q1_C1 := 2*elt_t1^2 + (1-w)*elt_u1^2 + (1+w);
Dq1 := Divisor(q1_C1);
eta := (HalfPositive(Dq1) - HalfPositive(-Dq1)) @@ m1;
printf "C1: eta = %o, in V_rat? %o, in J[2]? %o\n", eta, eta in V_rat_1, eta in J2_1;

// C2
FF2<uu2> := FunctionField(u^4 + t^4 - 1);
Cl2, m2 := ClassGroup(FF2);
elt_t2 := FF2 ! t; elt_u2 := FF2.1;
e1_2 := 2*Cl2.1; e2_2 := 2*Cl2.2; e3_2 := 2*Cl2.3;
J2_2 := sub<Cl2 | e1_2, e2_2, e3_2>;

// Twisted bitangent V_rat
Lt1 := elt_t2+elt_u2+ii; Lt2 := elt_t2+elt_u2-ii;
Lt3 := elt_t2-elt_u2+ii;
Bt1 := HalfPositive(Divisor(Lt1)); Bt2 := HalfPositive(Divisor(Lt2));
Bt3 := HalfPositive(Divisor(Lt3));
Pt12 := (Bt1-Bt2) @@ m2; Pt13 := (Bt1-Bt3) @@ m2;
V_twist := sub<Cl2 | Pt12, Pt13>;

// Transport eta to C2
q1_C2 := -2*elt_t2^2 - (1-w)*elt_u2^2 + (1+w);
Dq1_2 := Divisor(q1_C2);
eta_2 := (HalfPositive(Dq1_2) - HalfPositive(-Dq1_2)) @@ m2;
printf "C2: eta_transported = %o, in V_twist? %o, in J(C2)[2]? %o\n",
    eta_2, eta_2 in V_twist, eta_2 in J2_2;

// Compare: does the twist change whether eta is in V_rat?
printf "\nConclusion at p=%o:\n", p;
printf "  eta in V_rat(C1)? %o\n", eta in V_rat_1;
printf "  eta_transported in V_twist(C2)? %o\n", eta_2 in V_twist;

quit;
