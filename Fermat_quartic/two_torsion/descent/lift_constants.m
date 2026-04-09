/*******************************************************************************
 * lift_constants.m
 *
 * Compute lifting constants c_sigma where sigma*(q1)/q1 = c_sigma * h^2.
 * The lift sigma -> Aut(D) exists over the base field iff c_sigma is a square.
 *
 * Merged from: lift_constants.m, lift_constants_p7.m, lift_constants_multi.m,
 *              lift_constants_extensions.m, lift_verify_zeta8.m
 *
 * Contents:
 *   1. Multi-prime summary (general version)
 *   2. Extension fields F_{p^k}
 *   3. Verification: Aut(D) defined over Q(zeta_8)
 ******************************************************************************/


// =========== MULTI-PRIME SUMMARY ===========
// Check lifting constants at multiple primes simultaneously.
// For each prime, compute how many automorphisms have square lifting constant.

print "=============================================";
print "SECTION 1: Lifting constants at multiple primes";
print "=============================================";

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


// =========== EXTENSION FIELDS ===========
// Compute lifting constants over various fields including F_{p^k}.
// Key predictions:
//   - F_49: sqrt(-3), sqrt(-1), sqrt(-2) all exist -> all 96 sq -> |Aut(D)|=192
//   - F_97: same (97 = 1 mod 24) -> |Aut(D)|=192

print "=============================================";
print "SECTION 2: Lifting constants over extensions";
print "=============================================";

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

// Run checks over extension fields
CheckField(3);
CheckField(9);
CheckField(49);
CheckField(97);


// =========== ZETA_8 VERIFICATION ===========
// Verify that |Aut(D/F_p)| = 192 iff F_p contains zeta_8 (i.e., p = 1 mod 8),
// plus i (for full Aut(C)) and sqrt(-3) (for the q1 model).
//
// The claim: Aut(D) is defined over Q(zeta_8) = Q(i, sqrt(2)).

print "=============================================";
print "SECTION 3: Verify field of definition = Q(zeta_8)";
print "=============================================";

printf "=== Primes p = 1 mod 24 (should give |Aut(D)|=192 over F_p) ===\n";
for p in [97, 193, 241] do
    if not IsPrime(p) or p mod 24 ne 1 then continue; end if;
    Fp := GF(p);
    if not IsSquare(Fp!(-3)) then continue; end if;
    w := Sqrt(Fp!(-3));
    roots4 := [x : x in Fp | x^4 eq 1 and x ne 0];
    assert #roots4 eq 4;

    Fpt<t> := FunctionField(Fp);
    Ku<u> := PolynomialRing(Fpt);
    FF<uu> := FunctionField(u^4 + t^4 + 1);
    q1 := 2*(FF!t)^2 + (1-w)*uu^2 + (1+w);
    deg1 := Places(FF, 1);
    Cl, m := ClassGroup(FF);

    S3_perms := [
        Matrix(Fp, 3, 3, [1,0,0, 0,1,0, 0,0,1]),
        Matrix(Fp, 3, 3, [0,1,0, 1,0,0, 0,0,1]),
        Matrix(Fp, 3, 3, [0,0,1, 0,1,0, 1,0,0]),
        Matrix(Fp, 3, 3, [1,0,0, 0,0,1, 0,1,0]),
        Matrix(Fp, 3, 3, [0,0,1, 1,0,0, 0,1,0]),
        Matrix(Fp, 3, 3, [0,1,0, 0,0,1, 1,0,0])
    ];

    n_sq := 0;
    for sp in S3_perms do
        for beta in roots4 do
            for gamma in roots4 do
                M := sp * DiagonalMatrix(Fp, [1, beta, gamma]);
                num_t := M[1,1]*(FF!t) + M[1,2]*uu + FF!M[1,3];
                num_u := M[2,1]*(FF!t) + M[2,2]*uu + FF!M[2,3];
                den   := M[3,1]*(FF!t) + M[3,2]*uu + FF!M[3,3];
                sigma_q1 := 2*(num_t/den)^2 + (1-w)*(num_u/den)^2 + (1+w);
                ratio := sigma_q1 / q1;
                D_ratio := Divisor(ratio);
                supp := Support(D_ratio);
                supp_set := Set(supp);
                eval_val := Fp!1;
                for P in deg1 do
                    if P notin supp_set then
                        val := Evaluate(ratio, P);
                        ok, vi := IsCoercible(Fp, val);
                        if ok and vi ne 0 then eval_val := vi; break; end if;
                    end if;
                end for;
                if IsSquare(eval_val) then n_sq +:= 1; end if;
            end for;
        end for;
    end for;

    printf "p=%o: sqrt(-2) sq? %o, all sq=%o/96, |Aut(D)|=%o\n",
        p, IsSquare(Fp!(-2)), n_sq, 2*n_sq;
    delete FF; delete Fpt;
end for;

printf "\n=== Primes p = 1 mod 8 but p not= 1 mod 3 ===\n";
printf "(sqrt(-3) not in F_p, so test over F_{p^2})\n";
for p in [17, 41, 89] do
    if not IsPrime(p) or p mod 8 ne 1 then continue; end if;
    // Use F_{p^2} so sqrt(-3) exists
    q := p^2;
    Fq := GF(q);
    w := Sqrt(Fq!(-3));
    roots4 := [x : x in Fq | x^4 eq 1 and x ne 0];

    Fqt<t> := FunctionField(Fq);
    Ku<u> := PolynomialRing(Fqt);
    FF<uu> := FunctionField(u^4 + t^4 + 1);
    q1 := 2*(FF!t)^2 + (1-w)*uu^2 + (1+w);
    deg1 := Places(FF, 1);
    Cl, m := ClassGroup(FF);

    S3_perms := [
        Matrix(Fq, 3, 3, [1,0,0, 0,1,0, 0,0,1]),
        Matrix(Fq, 3, 3, [0,1,0, 1,0,0, 0,0,1]),
        Matrix(Fq, 3, 3, [0,0,1, 0,1,0, 1,0,0]),
        Matrix(Fq, 3, 3, [1,0,0, 0,0,1, 0,1,0]),
        Matrix(Fq, 3, 3, [0,0,1, 1,0,0, 0,1,0]),
        Matrix(Fq, 3, 3, [0,1,0, 0,0,1, 1,0,0])
    ];

    n_sq := 0;
    for sp in S3_perms do
        for beta in roots4 do
            for gamma in roots4 do
                M := sp * DiagonalMatrix(Fq, [1, beta, gamma]);
                num_t := M[1,1]*(FF!t) + M[1,2]*uu + FF!M[1,3];
                num_u := M[2,1]*(FF!t) + M[2,2]*uu + FF!M[2,3];
                den   := M[3,1]*(FF!t) + M[3,2]*uu + FF!M[3,3];
                sigma_q1 := 2*(num_t/den)^2 + (1-w)*(num_u/den)^2 + (1+w);
                ratio := sigma_q1 / q1;
                D_ratio := Divisor(ratio);
                supp := Support(D_ratio);
                supp_set := Set(supp);
                eval_val := Fq!1;
                for P in deg1 do
                    if P notin supp_set then
                        val := Evaluate(ratio, P);
                        ok, vi := IsCoercible(Fq, val);
                        if ok and vi ne 0 then eval_val := vi; break; end if;
                    end if;
                end for;
                if IsSquare(eval_val) then n_sq +:= 1; end if;
            end for;
        end for;
    end for;

    printf "F_%o (p=%o): sqrt(-2) sq? %o, all sq=%o/96, |Aut(D)|=%o\n",
        q, p, IsSquare(Fq!(-2)), n_sq, 2*n_sq;
    delete FF; delete Fqt;
end for;

printf "\n=== SUMMARY ===\n";
printf "Prediction: Aut(D) defined over Q(zeta_8) = Q(i, sqrt(2))\n";
printf "Full |Aut(D)| = 192 visible iff zeta_8 in base field\n";
printf "zeta_8 in F_p iff p = 1 mod 8\n";
printf "For q1 model also need sqrt(-3) in field\n";

quit;
