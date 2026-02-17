/*******************************************************************************
 * lift_constants_multi.m — Check lifting constants at multiple primes.
 ******************************************************************************/

for p in [7, 13, 19, 37, 43] do
    Fp := GF(p);
    if not IsSquare(Fp!(-3)) then continue; end if;
    w := Sqrt(Fp!(-3));
    has_i := IsSquare(Fp!(-1));
    roots4 := [x : x in Fp | x^4 eq 1 and x ne 0];

    Fpt<t> := FunctionField(Fp);
    Ku<u> := PolynomialRing(Fpt);
    f_C := u^4 + t^4 + 1;
    if not IsIrreducible(f_C) then
        printf "p=%o: C reducible, skip\n", p; continue;
    end if;
    FF<uu> := FunctionField(f_C);
    elt_t := FF!t; elt_u := uu;

    q1 := 2*elt_t^2 + (1-w)*elt_u^2 + (1+w);
    // Check etale
    dq1 := Divisor(q1);
    supp_q1 := Support(dq1);
    etale := #supp_q1 eq 0 or &and[Valuation(q1, P) mod 2 eq 0 : P in supp_q1];

    deg1 := Places(FF, 1);

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
                Append(~aut_list, <M, sp[1]>);
            end for;
        end for;
    end for;

    n_sq := 0; n_nsq := 0; n_notfix := 0;
    // Track constants by permutation type
    perm_sq := AssociativeArray();
    for pn in ["id", "(12)", "(13)", "(23)", "(123)", "(132)"] do
        perm_sq[pn] := <0, 0>; // <square, nonsquare>
    end for;

    Cl, m := ClassGroup(FF);

    for k in [1..#aut_list] do
        M := aut_list[k][1];
        pname := aut_list[k][2];

        num_t := M[1,1]*elt_t + M[1,2]*elt_u + FF!M[1,3];
        num_u := M[2,1]*elt_t + M[2,2]*elt_u + FF!M[2,3];
        den   := M[3,1]*elt_t + M[3,2]*elt_u + FF!M[3,3];
        sigma_t := num_t / den;
        sigma_u := num_u / den;
        sigma_q1 := 2*sigma_t^2 + (1-w)*sigma_u^2 + (1+w);
        ratio := sigma_q1 / q1;

        D_ratio := Divisor(ratio);
        supp := Support(D_ratio);
        vals_even := #supp eq 0 or &and[Valuation(ratio, P) mod 2 eq 0 : P in supp];

        if not vals_even then
            n_notfix +:= 1;
            continue;
        end if;

        // Check half principal
        if #supp gt 0 then
            half_D := D_ratio div 2;
            cls := half_D @@ m;
            if cls ne Cl!0 then
                n_notfix +:= 1;
                continue;
            end if;
        end if;

        // Evaluate at a safe place
        supp_set := Set(supp);
        eval_val := Fp!1;
        for P in deg1 do
            if P notin supp_set then
                val := Evaluate(ratio, P);
                ok, vi := IsCoercible(Fp, val);
                if ok and vi ne 0 then
                    eval_val := vi; break;
                end if;
            end if;
        end for;

        is_sq := IsSquare(eval_val);
        if is_sq then
            n_sq +:= 1;
            perm_sq[pname] := <perm_sq[pname][1]+1, perm_sq[pname][2]>;
        else
            n_nsq +:= 1;
            perm_sq[pname] := <perm_sq[pname][1], perm_sq[pname][2]+1>;
        end if;
    end for;

    printf "p=%2o (w=%2o, has_i=%o, etale=%o): |Aut(C)|=%2o, sq=%2o, nsq=%2o, notfix=%o => |Aut(D)|=%o\n",
        p, Integers()!w, has_i, etale, #aut_list, n_sq, n_nsq, n_notfix, 2*n_sq;

    for pn in ["id", "(12)", "(13)", "(23)", "(123)", "(132)"] do
        s := perm_sq[pn][1]; ns := perm_sq[pn][2];
        if s + ns gt 0 then
            printf "  %o: %o sq, %o nsq\n", pn, s, ns;
        end if;
    end for;
    printf "\n";

    delete FF; delete Fpt;
end for;

quit;
