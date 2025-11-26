/*******************************************************************************
 * two_ranks.m
 *
 * Compute the 2-rank of J(C)(F_p) and J(C_twist)(F_p) using function field
 * class groups. The 2-rank = dim_{F_2} J(F_p)[2] tells us the dimension
 * of the Frobenius fixed space on J[2].
 ******************************************************************************/

// =============================================================================
// Klein quartic C: x^3*y + y^3*z + z^3*x = 0
// Affine model (z=1): x^3*y + y^3 + x = 0
// Function field: F_p(t)[u]/(u^3 + t^3*u + t)
// =============================================================================
print "=== 2-RANK OF J(C)(F_p) ===";
printf "%-5o %-6o %-40o %-8o\n", "p", "p%7", "J(C)(F_p)", "2-rank";

for p in [3, 5, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71] do
    if p eq 7 then continue; end if;
    Fp := GF(p);
    Fpt<t> := FunctionField(Fp);
    Fptu<u> := PolynomialRing(Fpt);
    f := u^3 + t^3*u + t;

    try
        FF := FunctionField(f);
        Cl := ClassGroup(FF);
        invs := Invariants(Cl);
        two_rank := #[d : d in invs | d mod 2 eq 0];

        s := "";
        for i in [1..#invs] do
            if i gt 1 then s cat:= " x "; end if;
            s cat:= Sprintf("Z/%oZ", invs[i]);
        end for;

        printf "%-5o %-6o %-40o %-8o\n", p, p mod 7, s, two_rank;
    catch e
        printf "%-5o %-6o ERROR: %o\n", p, p mod 7, e`Object;
    end try;
end for;

// =============================================================================
// C_twist: x^4+y^4+z^4+6(xy^3+yz^3+zx^3)-3(x^2y^2+y^2z^2+z^2x^2)+3xyz(x+y+z)
// Affine model (z=1):
//   y^4 + 6x*y^3 + (-3x^2+3x-3)*y^2 + (3x^2+3x+6)*y + (x^4+6x^3-3x^2+1)
// Function field: F_p(t)[u]/(above polynomial in u)
// =============================================================================
print "\n=== 2-RANK OF J(C_twist)(F_p) ===";
printf "%-5o %-6o %-40o %-8o\n", "p", "p%7", "J(C_tw)(F_p)", "2-rank";

for p in [3, 5, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71] do
    if p eq 7 then continue; end if;
    Fp := GF(p);
    Fpt<t> := FunctionField(Fp);
    Fptu<u> := PolynomialRing(Fpt);

    c0 := Fpt!(t^4 + 6*t^3 - 3*t^2 + 1);
    c1 := Fpt!(3*t^2 + 3*t + 6);
    c2 := Fpt!(-3*t^2 + 3*t - 3);
    c3 := Fpt!(6*t);
    c4 := Fpt!1;

    g := u^4 + c3*u^3 + c2*u^2 + c1*u + c0;

    try
        // Check if polynomial is irreducible
        if not IsIrreducible(g) then
            printf "%-5o %-6o REDUCIBLE\n", p, p mod 7;
            continue;
        end if;

        FF := FunctionField(g);
        Cl := ClassGroup(FF);
        invs := Invariants(Cl);
        two_rank := #[d : d in invs | d mod 2 eq 0];

        s := "";
        for i in [1..#invs] do
            if i gt 1 then s cat:= " x "; end if;
            s cat:= Sprintf("Z/%oZ", invs[i]);
        end for;

        printf "%-5o %-6o %-40o %-8o\n", p, p mod 7, s, two_rank;
    catch e
        printf "%-5o %-6o ERROR: %o\n", p, p mod 7, e`Object;
    end try;
end for;

// =============================================================================
// Summary table: compare 2-ranks
// =============================================================================
print "\n=== COMPARISON TABLE ===";
printf "%-5o %-6o %-10o %-10o\n", "p", "p%7", "2rk(C)", "2rk(Ctw)";

for p in [3, 5, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43] do
    if p eq 7 then continue; end if;
    Fp := GF(p);
    Fpt<t> := FunctionField(Fp);
    Fptu<u> := PolynomialRing(Fpt);

    // C
    f := u^3 + t^3*u + t;
    FF_C := FunctionField(f);
    Cl_C := ClassGroup(FF_C);
    invs_C := Invariants(Cl_C);
    rk_C := #[d : d in invs_C | d mod 2 eq 0];

    // C_twist
    c0 := Fpt!(t^4 + 6*t^3 - 3*t^2 + 1);
    c1 := Fpt!(3*t^2 + 3*t + 6);
    c2 := Fpt!(-3*t^2 + 3*t - 3);
    c3 := Fpt!(6*t);
    g := u^4 + c3*u^3 + c2*u^2 + c1*u + c0;

    rk_tw := -1;
    try
        if IsIrreducible(g) then
            FF_tw := FunctionField(g);
            Cl_tw := ClassGroup(FF_tw);
            invs_tw := Invariants(Cl_tw);
            rk_tw := #[d : d in invs_tw | d mod 2 eq 0];
        end if;
    catch e
        rk_tw := -1;
    end try;

    printf "%-5o %-6o %-10o %-10o\n", p, p mod 7, rk_C, rk_tw;
end for;

quit;
