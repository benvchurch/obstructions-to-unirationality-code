/*******************************************************************************
 * lift_constants_p7.m — Check lifting constants at p=7.
 ******************************************************************************/

p := 7;
Fp := GF(p);
w := Sqrt(Fp!(-3)); // -3 = 4 mod 7, sqrt = 2
printf "p = %o, w = sqrt(-3) = %o\n", p, w;
printf "Squares in F_7*: %o\n", [x^2 : x in [Fp!1..Fp!(p-1)]];
printf "i = sqrt(-1) exists? %o\n\n", IsSquare(Fp!(-1));

// Only use 4th roots of unity that exist in F_7
// F_7* has order 6, 4th roots of unity are solutions to x^4=1, i.e., x^(gcd(4,6))=x^2=1
// So 4th roots in F_7 are {1, -1} = {1, 6}
roots4 := [x : x in Fp | x^4 eq 1 and x ne 0];
printf "4th roots of unity in F_%o: %o\n\n", p, roots4;

Fpt<t> := FunctionField(Fp);
Ku<u> := PolynomialRing(Fpt);
FF<uu> := FunctionField(u^4 + t^4 + 1);
elt_t := FF!t;
elt_u := uu;

q1 := 2*elt_t^2 + (1-w)*elt_u^2 + (1+w);

// Check etale
dq1 := Divisor(q1);
supp_q1 := Support(dq1);
all_even := &and[Valuation(q1, P) mod 2 eq 0 : P in supp_q1];
printf "div(q1) all-even (etale)? %o\n\n", all_even;

deg1 := Places(FF, 1);

S3_perms := [
    <"id",    Matrix(Fp, 3, 3, [1,0,0, 0,1,0, 0,0,1])>,
    <"(12)",  Matrix(Fp, 3, 3, [0,1,0, 1,0,0, 0,0,1])>,
    <"(13)",  Matrix(Fp, 3, 3, [0,0,1, 0,1,0, 1,0,0])>,
    <"(23)",  Matrix(Fp, 3, 3, [1,0,0, 0,0,1, 0,1,0])>,
    <"(123)", Matrix(Fp, 3, 3, [0,0,1, 1,0,0, 0,1,0])>,
    <"(132)", Matrix(Fp, 3, 3, [0,1,0, 0,0,1, 1,0,0])>
];

// Only F_7-rational automorphisms
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
printf "|Aut(C/F_%o)| = %o\n\n", p, #aut_list;

n_sq := 0; n_nsq := 0; n_fixes := 0;

for k in [1..#aut_list] do
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
    vals_even := #supp eq 0 or &and[Valuation(ratio, P) mod 2 eq 0 : P in supp];

    if not vals_even then
        printf "Aut #%2o: %-30o — does NOT fix eta (odd vals)\n", k, aut_list[k][2];
        continue;
    end if;

    // Check half-divisor principal
    if #supp eq 0 then
        half_principal := true;
    else
        half_D := D_ratio div 2;
        Cl, m := ClassGroup(FF);
        cls := half_D @@ m;
        half_principal := cls eq Cl!0;
    end if;

    if not half_principal then
        printf "Aut #%2o: %-30o — fixes eta but half not principal\n", k, aut_list[k][2];
        n_fixes +:= 1;
        continue;
    end if;

    n_fixes +:= 1;

    // Determine square class of c
    eval_val := Fp!0;
    for P in deg1 do
        if P notin supp_set then
            val := Evaluate(ratio, P);
            ok, vi := IsCoercible(Fp, val);
            if ok and vi ne 0 then
                eval_val := vi;
                break;
            end if;
        end if;
    end for;

    is_sq := IsSquare(eval_val);
    if is_sq then n_sq +:= 1; else n_nsq +:= 1; end if;

    printf "Aut #%2o: %-30o c ~ %o (square? %o)\n",
        k, aut_list[k][2], Integers()!eval_val, is_sq;
end for;

printf "\n=== RESULTS for p = %o ===\n", p;
printf "Fixes eta: %o / %o\n", n_fixes, #aut_list;
printf "Square c: %o, Non-square c: %o\n", n_sq, n_nsq;
printf "Expected |Aut(D/F_%o)| = 2 * %o = %o\n", p, n_sq, 2*n_sq;
printf "Previous |Aut(D/F_%o)| from Magma: 24\n", p;

quit;
