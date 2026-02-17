/*******************************************************************************
 * stab_eta_direct.m
 *
 * Directly compute Stab_{Aut(C)}(eta) where eta = (1/2)div(q1) in J[2].
 *
 * Criterion: sigma fixes eta iff sigma*(q1)/q1 has all-even valuations
 * AND the half-divisor is principal. Equivalently, sigma*(q1)/q1 = c*h^2
 * for some constant c and function h.
 *
 * Use p = 97 (≡ 1 mod 24, so has 4th roots of unity AND sqrt(-3)).
 ******************************************************************************/

p := 97;
Fp := GF(p);
i_val := Sqrt(Fp!(-1));
w := Sqrt(Fp!(-3));
roots4 := [Fp!1, i_val, Fp!(-1), -i_val];

printf "p = %o, i = %o, w = sqrt(-3) = %o\n\n", p, i_val, w;

// Function field of C: u^4 + t^4 + 1 = 0
Fpt<t> := FunctionField(Fp);
Ku<u> := PolynomialRing(Fpt);
FF<uu> := FunctionField(u^4 + t^4 + 1);
elt_t := FF!t;
elt_u := uu;

// Class group (needed to check if half-divisor is principal)
Cl, m := ClassGroup(FF);
printf "Class group invariants: %o\n\n", Invariants(Cl);

// q1 = 2t^2 + (1-w)*u^2 + (1+w)
q1 := 2*elt_t^2 + (1-w)*elt_u^2 + (1+w);

// Verify q1 gives etale cover
dq1 := Divisor(q1);
supp_q1 := Support(dq1);
all_even := &and[Valuation(q1, P) mod 2 eq 0 : P in supp_q1];
printf "div(q1) all-even? %o (etale cover check)\n\n", all_even;

// ==========================================================================
// Enumerate the 96 automorphisms
// ==========================================================================
S3_perms := [
    <"id",    Matrix(Fp, 3, 3, [1,0,0, 0,1,0, 0,0,1])>,
    <"(12)",  Matrix(Fp, 3, 3, [0,1,0, 1,0,0, 0,0,1])>,
    <"(13)",  Matrix(Fp, 3, 3, [0,0,1, 0,1,0, 1,0,0])>,
    <"(23)",  Matrix(Fp, 3, 3, [1,0,0, 0,0,1, 0,1,0])>,
    <"(123)", Matrix(Fp, 3, 3, [0,0,1, 1,0,0, 0,1,0])>,
    <"(132)", Matrix(Fp, 3, 3, [0,1,0, 0,0,1, 1,0,0])>
];

aut_list := [];
for sp in S3_perms do
    for beta in roots4 do
        for gamma in roots4 do
            M := sp[2] * DiagonalMatrix(Fp, [1, beta, gamma]);
            label := Sprintf("%o * diag(1,%o,%o)", sp[1], beta, gamma);
            Append(~aut_list, <M, label>);
        end for;
    end for;
end for;
assert #aut_list eq 96;

// ==========================================================================
// For each automorphism, compute sigma*(q1)/q1 and check criterion
// ==========================================================================

// sigma acts on (x:y:z) -> M*(x:y:z). In affine coords (t=x/z, u=y/z):
// sigma*(t) = (M11*t + M12*u + M13) / (M31*t + M32*u + M33)
// sigma*(u) = (M21*t + M22*u + M23) / (M31*t + M32*u + M33)
// sigma*(q1) = 2*sigma*(t)^2 + (1-w)*sigma*(u)^2 + (1+w)

stab_indices := [];
non_stab_info := [];

printf "=== CHECKING EACH AUTOMORPHISM ===\n\n";

for k in [1..96] do
    M := aut_list[k][1];

    // Compute sigma*(t) and sigma*(u) in FF
    num_t := M[1,1]*elt_t + M[1,2]*elt_u + FF!M[1,3];
    num_u := M[2,1]*elt_t + M[2,2]*elt_u + FF!M[2,3];
    den   := M[3,1]*elt_t + M[3,2]*elt_u + FF!M[3,3];

    sigma_t := num_t / den;
    sigma_u := num_u / den;

    sigma_q1 := 2*sigma_t^2 + (1-w)*sigma_u^2 + (1+w);

    ratio := sigma_q1 / q1;

    // Check if all valuations of ratio are even
    D := Divisor(ratio);
    supp_D := Support(D);
    if #supp_D eq 0 then
        // ratio is a constant — all valuations are 0 (trivially even)
        // and half-divisor is 0 which is principal
        Append(~stab_indices, k);
        if k le 16 or #stab_indices le 20 then
            printf "Aut #%2o: %o — ratio is CONSTANT, fixes eta ✓\n", k, aut_list[k][2];
        end if;
        continue;
    end if;

    vals_even := &and[Valuation(ratio, P) mod 2 eq 0 : P in supp_D];

    if not vals_even then
        // Odd valuations => does NOT fix eta
        if k le 16 then
            printf "Aut #%2o: %o — ODD valuations, does NOT fix eta ✗\n", k, aut_list[k][2];
        end if;
        Append(~non_stab_info, <k, "odd_vals">);
        continue;
    end if;

    // All valuations even. Compute half-divisor and check if principal.
    half_D := D div 2;
    cls := half_D @@ m;
    if cls eq Cl!0 then
        Append(~stab_indices, k);
        if k le 16 or #stab_indices le 20 then
            printf "Aut #%2o: %o — even vals, half principal, fixes eta ✓\n", k, aut_list[k][2];
        end if;
    else
        if k le 16 then
            printf "Aut #%2o: %o — even vals, half NOT principal ✗\n", k, aut_list[k][2];
        end if;
        Append(~non_stab_info, <k, "half_not_principal">);
    end if;
end for;

printf "\n=== STABILIZER RESULTS ===\n";
printf "|Stab_{Aut(C)}(eta)| = %o\n", #stab_indices;
printf "|Orbit of eta| = %o (= 96 / %o)\n", 96 div #stab_indices, #stab_indices;
printf "Expected |Aut(D)| = 2 * |Stab| = %o\n\n", 2 * #stab_indices;

printf "Stabilizer elements (%o total):\n", #stab_indices;
for k in stab_indices do
    printf "  %o\n", aut_list[k][2];
end for;

// Analyze stabilizer structure
printf "\n=== STABILIZER STRUCTURE ===\n";
// Collect the PGL(3) matrices
stab_PGL := [aut_list[k][1] : k in stab_indices];
// Check which permutations appear
perm_types := {};
for k in stab_indices do
    M := aut_list[k][1];
    // Determine the permutation type from the matrix
    lab := aut_list[k][2];
    perm := lab[1..Regexp("\\*", lab) - 2];
    Include(~perm_types, perm);
end for;
printf "Permutation types in stabilizer: %o\n", perm_types;

// Count elements by permutation type
for perm in ["id", "(12)", "(13)", "(23)", "(123)", "(132)"] do
    cnt := #[k : k in stab_indices | Regexp(perm, aut_list[k][2]) ge 1];
    if cnt gt 0 then
        printf "  %o: %o elements\n", perm, cnt;
    end if;
end for;

// Also analyze non-stabilizer elements
printf "\nNon-stabilizer breakdown:\n";
n_odd := #[x : x in non_stab_info | x[2] eq "odd_vals"];
n_half := #[x : x in non_stab_info | x[2] eq "half_not_principal"];
printf "  Odd valuations: %o\n", n_odd;
printf "  Even vals but half not principal: %o\n", n_half;
printf "  Total non-stabilizer: %o\n", n_odd + n_half;

printf "\n=== COMPARISON WITH PREVIOUS Aut(D) RESULT ===\n";
printf "Previous: |Aut(D)| = 96, Aut(D) ≅ C2^2.SL(2,3)\n";
printf "Previous: Aut(D)/<iota> ≅ C4^2:C3, |Aut(D)/<iota>| = 48\n";
printf "Current:  |Stab_{Aut(C)}(eta)| = %o\n", #stab_indices;
printf "Expected: |Stab| should equal |Aut(D)|/2 = 48\n";
printf "Match? %o\n", #stab_indices eq 48;

quit;
