/*******************************************************************************
 * lift_verify_zeta8.m
 *
 * Verify that |Aut(D/F_p)| = 192 iff F_p contains ζ_8 (i.e., p ≡ 1 mod 8),
 * plus i (for full Aut(C)) and √(-3) (for the q1 model).
 *
 * For primes where √(-3) doesn't exist, D isn't defined via q1 over F_p,
 * but we can still test over extensions.
 *
 * The claim: Aut(D) is defined over Q(ζ_8) = Q(i, √2).
 ******************************************************************************/

// Test at primes p ≡ 1 mod 8 (where ζ_8 ∈ F_p) that also have √(-3)
// These need p ≡ 1 mod 8 AND p ≡ 1 mod 3, i.e., p ≡ 1 mod 24.
// Also test p ≡ 1 mod 8 but p ≡ 2 mod 3 (no √(-3) in F_p but in F_{p^2}).

printf "=== Primes p ≡ 1 mod 24 (should give |Aut(D)|=192 over F_p) ===\n";
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

printf "\n=== Primes p ≡ 1 mod 8 but p ≢ 1 mod 3 ===\n";
printf "(√(-3) not in F_p, so test over F_{p^2})\n";
for p in [17, 41, 89] do
    if not IsPrime(p) or p mod 8 ne 1 then continue; end if;
    // Use F_{p^2} so √(-3) exists
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
printf "zeta_8 in F_p iff p ≡ 1 mod 8\n";
printf "For q1 model also need sqrt(-3) in field\n";

quit;
