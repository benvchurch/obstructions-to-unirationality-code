/*******************************************************************************
 * lift_constants.m
 *
 * For each sigma in Aut(C), compute the "lifting constant" c_sigma:
 *   sigma*(q1)/q1 = c_sigma * h_sigma^2
 * The lift sigma -> Aut(D) exists over F_p iff c_sigma is a square.
 *
 * Prediction: exactly 48 out of 96 have c_sigma square at p ≡ 1 mod 12,
 * giving |Aut(D/F_p)| = 2*48 = 96.
 ******************************************************************************/

p := 13;
Fp := GF(p);
i_val := Sqrt(Fp!(-1));
w := Sqrt(Fp!(-3));
roots4 := [Fp!1, i_val, Fp!(-1), -i_val];

printf "p = %o, i = %o, w = sqrt(-3) = %o\n", p, i_val, w;
printf "Non-square in F_%o: e.g. %o\n\n", p, PrimitiveElement(Fp);

Fpt<t> := FunctionField(Fp);
Ku<u> := PolynomialRing(Fpt);
FF<uu> := FunctionField(u^4 + t^4 + 1);
elt_t := FF!t;
elt_u := uu;

q1 := 2*elt_t^2 + (1-w)*elt_u^2 + (1+w);

// Get degree-1 places for evaluation
deg1 := Places(FF, 1);
printf "Number of degree-1 places: %o\n", #deg1;

// Automorphisms
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

// For each automorphism, compute ratio = sigma*(q1)/q1
// Then evaluate at a place NOT in the support of div(ratio)
// to determine the square class of the lifting constant c.

n_square := 0;
n_nonsq := 0;
square_labels := [];
nonsq_labels := [];

for k in [1..96] do
    M := aut_list[k][1];

    num_t := M[1,1]*elt_t + M[1,2]*elt_u + FF!M[1,3];
    num_u := M[2,1]*elt_t + M[2,2]*elt_u + FF!M[2,3];
    den   := M[3,1]*elt_t + M[3,2]*elt_u + FF!M[3,3];

    sigma_t := num_t / den;
    sigma_u := num_u / den;
    sigma_q1 := 2*sigma_t^2 + (1-w)*sigma_u^2 + (1+w);
    ratio := sigma_q1 / q1;

    // Find a place not in the support of div(ratio) for evaluation
    D_ratio := Divisor(ratio);
    supp := Support(D_ratio);
    supp_set := Set(supp);

    eval_val := Fp!0;
    found_place := false;
    for P in deg1 do
        if P notin supp_set then
            // ratio has no zero/pole at P, so ratio(P) is well-defined and nonzero
            val := Evaluate(ratio, P);
            ok, vi := IsCoercible(Fp, val);
            if ok and vi ne 0 then
                eval_val := vi;
                found_place := true;
                break;
            end if;
        end if;
    end for;

    if not found_place then
        // ratio is a constant (no zeros or poles)
        // Try to extract the constant
        // For a constant function f in FF, Evaluate at any place gives f
        for P in deg1 do
            val := Evaluate(ratio, P);
            ok, vi := IsCoercible(Fp, val);
            if ok then
                eval_val := vi;
                found_place := true;
                break;
            end if;
        end for;
    end if;

    is_sq := IsSquare(eval_val);
    if is_sq then
        n_square +:= 1;
        Append(~square_labels, aut_list[k][2]);
    else
        n_nonsq +:= 1;
        Append(~nonsq_labels, aut_list[k][2]);
    end if;

    if k le 16 then
        printf "Aut #%2o: %-35o c ~ %3o (square? %o)\n",
            k, aut_list[k][2], Integers()!eval_val, is_sq;
    end if;
end for;

printf "\n... (showing first 16 of 96)\n\n";

printf "=== RESULTS ===\n";
printf "# with c_sigma square:     %o\n", n_square;
printf "# with c_sigma non-square: %o\n", n_nonsq;
printf "Expected |Aut(D/F_%o)| = 2 * %o = %o\n", p, n_square, 2*n_square;
printf "Previous |Aut(D/F_%o)|: 96\n", p;
printf "Match? %o\n\n", 2*n_square eq 96;

printf "Geometric |Aut(D)| = 2 * 96 = 192\n";
printf "|Aut(D/F_%o)| = %o (= 2 * %o sigma's with square constant)\n\n",
    p, 2*n_square, n_square;

// Analyze the structure: which permutations appear with square vs non-square
printf "=== BREAKDOWN BY PERMUTATION TYPE ===\n";
for perm_idx in [1..6] do
    perm_name := S3_perms[perm_idx][1];
    // Automorphisms with this permutation: indices (perm_idx-1)*16 + 1 to perm_idx*16
    start := (perm_idx-1)*16 + 1;
    finish := perm_idx*16;
    sq_count := 0;
    for k in [start..finish] do
        M := aut_list[k][1];
        num_t := M[1,1]*elt_t + M[1,2]*elt_u + FF!M[1,3];
        num_u := M[2,1]*elt_t + M[2,2]*elt_u + FF!M[2,3];
        den   := M[3,1]*elt_t + M[3,2]*elt_u + FF!M[3,3];
        sigma_t := num_t / den;
        sigma_u := num_u / den;
        sigma_q1 := 2*sigma_t^2 + (1-w)*sigma_u^2 + (1+w);
        ratio := sigma_q1 / q1;
        D_ratio := Divisor(ratio);
        supp := Support(D_ratio);
        supp_set := Set(supp);
        for P in deg1 do
            if P notin supp_set then
                val := Evaluate(ratio, P);
                ok, vi := IsCoercible(Fp, val);
                if ok and vi ne 0 then
                    if IsSquare(vi) then sq_count +:= 1; end if;
                    break;
                end if;
            end if;
        end for;
    end for;
    printf "  %o: %o square, %o non-square (out of 16)\n",
        perm_name, sq_count, 16 - sq_count;
end for;

quit;
