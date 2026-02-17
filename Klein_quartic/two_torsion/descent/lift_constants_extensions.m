/*******************************************************************************
 * lift_constants_extensions.m
 *
 * Compute lifting constants over various fields including F_{p^k}.
 * Key predictions:
 *   - F_49: √(-3), √(-1), √(-2) all exist → all 96 sq → |Aut(D)|=192
 *   - F_97: same (97 ≡ 1 mod 24) → |Aut(D)|=192
 *   - F_3: 3 | disc(Q(√(-3))), might be bad
 *   - F_9: same caveat
 ******************************************************************************/

// Helper function: compute lifting data over GF(q)
procedure CheckField(q)
    Fq := GF(q);
    p := Characteristic(Fq);

    if not IsSquare(Fq!(-3)) then
        printf "F_%o: sqrt(-3) does not exist, skip\n\n", q;
        return;
    end if;
    w := Sqrt(Fq!(-3));
    has_i := IsSquare(Fq!(-1));
    roots4 := [x : x in Fq | x^4 eq 1 and x ne 0];

    printf "=== F_%o (char %o) ===\n", q, p;
    printf "  sqrt(-3) = %o, sqrt(-1) exists? %o\n", w, has_i;
    printf "  sqrt(-2) exists? %o\n", IsSquare(Fq!(-2));
    printf "  4th roots: %o\n", #roots4;

    Fqt<t> := FunctionField(Fq);
    Ku<u> := PolynomialRing(Fqt);
    f_C := u^4 + t^4 + 1;
    if not IsIrreducible(f_C) then
        printf "  u^4+t^4+1 REDUCIBLE over F_%o, skip\n\n", q;
        return;
    end if;
    FF<uu> := FunctionField(f_C);
    elt_t := FF!t; elt_u := uu;
    printf "  Genus(C) = %o\n", Genus(FF);

    q1 := 2*elt_t^2 + (1-w)*elt_u^2 + (1+w);

    // Check etale
    dq1 := Divisor(q1);
    supp_q1 := Support(dq1);
    etale := #supp_q1 eq 0 or &and[Valuation(q1, P) mod 2 eq 0 : P in supp_q1];
    printf "  Etale cover? %o\n", etale;

    if not etale then
        printf "  Cover NOT etale, skip lifting analysis\n\n";
        return;
    end if;

    // Check if v^2 - q1 is irreducible (cover is connected)
    Kv<v> := PolynomialRing(FF);
    irr := IsIrreducible(v^2 - q1);
    printf "  v^2-q1 irreducible? %o\n", irr;
    if not irr then
        printf "  Cover REDUCIBLE (eta = 0), skip\n\n";
        return;
    end if;

    deg1 := Places(FF, 1);
    Cl, m := ClassGroup(FF);

    S3_perms := [
        <"id",    Matrix(Fq, 3, 3, [1,0,0, 0,1,0, 0,0,1])>,
        <"(12)",  Matrix(Fq, 3, 3, [0,1,0, 1,0,0, 0,0,1])>,
        <"(13)",  Matrix(Fq, 3, 3, [0,0,1, 0,1,0, 1,0,0])>,
        <"(23)",  Matrix(Fq, 3, 3, [1,0,0, 0,0,1, 0,1,0])>,
        <"(123)", Matrix(Fq, 3, 3, [0,0,1, 1,0,0, 0,1,0])>,
        <"(132)", Matrix(Fq, 3, 3, [0,1,0, 0,0,1, 1,0,0])>
    ];

    aut_list := [];
    for sp in S3_perms do
        for beta in roots4 do
            for gamma in roots4 do
                M := sp[2] * DiagonalMatrix(Fq, [1, beta, gamma]);
                Append(~aut_list, <M, sp[1]>);
            end for;
        end for;
    end for;

    n_sq := 0; n_nsq := 0; n_notfix := 0;
    perm_sq := AssociativeArray();
    for pn in ["id", "(12)", "(13)", "(23)", "(123)", "(132)"] do
        perm_sq[pn] := <0, 0>;
    end for;

    for k in [1..#aut_list] do
        M := aut_list[k][1]; pname := aut_list[k][2];
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
            n_notfix +:= 1; continue;
        end if;

        if #supp gt 0 then
            half_D := D_ratio div 2;
            cls := half_D @@ m;
            if cls ne Cl!0 then n_notfix +:= 1; continue; end if;
        end if;

        // Evaluate at safe place
        eval_val := Fq!1;
        for P in deg1 do
            if P notin supp_set then
                val := Evaluate(ratio, P);
                ok, vi := IsCoercible(Fq, val);
                if ok and vi ne 0 then eval_val := vi; break; end if;
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

    printf "  |Aut(C/F_%o)| = %o\n", q, #aut_list;
    printf "  Fixes eta: %o, sq: %o, nsq: %o, notfix: %o\n",
        #aut_list - n_notfix, n_sq, n_nsq, n_notfix;
    printf "  => |Aut(D/F_%o)| = 2*%o = %o\n", q, n_sq, 2*n_sq;
    for pn in ["id", "(12)", "(13)", "(23)", "(123)", "(132)"] do
        s := perm_sq[pn][1]; ns := perm_sq[pn][2];
        if s + ns gt 0 then
            printf "    %o: %o sq, %o nsq\n", pn, s, ns;
        end if;
    end for;
    printf "\n";
end procedure;

// Run checks
CheckField(3);
CheckField(9);
CheckField(49);
CheckField(97);

quit;
