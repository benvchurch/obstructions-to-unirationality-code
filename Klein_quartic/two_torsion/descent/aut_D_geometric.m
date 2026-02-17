/*******************************************************************************
 * aut_D_geometric.m
 *
 * Compute |Aut(D)| over F_p and F_{p^2} to check if the geometric
 * automorphism group is larger than what's visible over F_p.
 *
 * Prediction: |Aut(D/F_p)| = 96 for p ≡ 1 mod 12,
 *             |Aut(D/F_{p^2})| = 192 (the full geometric group).
 ******************************************************************************/

// ====== Over F_13 ======
printf "=== Aut(D) over F_13 ===\n";
p := 13;
Fp := GF(p);
w := Sqrt(Fp!(-3));
printf "p = %o, w = sqrt(-3) = %o\n", p, w;

Fpt<t> := FunctionField(Fp);
Ku<u> := PolynomialRing(Fpt);
FC<uu> := FunctionField(u^4 + t^4 + 1);
q1 := 2*(FC!t)^2 + (1-w)*uu^2 + (1+w);
Kv<v> := PolynomialRing(FC);
FD<vv> := FunctionField(v^2 - q1);
printf "Genus(D) = %o\n", Genus(FD);
time A13, mp13 := AutomorphismGroup(FD);
phi13, G13 := CosetAction(A13, sub<A13 | Id(A13)>);
printf "|Aut(D/F_%o)| = %o, GroupName = %o\n\n", p, #G13, GroupName(G13);

// ====== Over F_{13^2} = F_169 ======
printf "=== Aut(D) over F_{13^2} = F_169 ===\n";
Fq := GF(p^2);
w2 := Sqrt(Fq!(-3));
printf "w = sqrt(-3) = %o in F_%o\n", w2, p^2;

Fqt<t2> := FunctionField(Fq);
Ku2<u2> := PolynomialRing(Fqt);
FC2<uu2> := FunctionField(u2^4 + t2^4 + 1);
q1_2 := 2*(FC2!t2)^2 + (1-w2)*uu2^2 + (1+w2);
Kv2<v2> := PolynomialRing(FC2);
FD2<vv2> := FunctionField(v2^2 - q1_2);
printf "Genus(D) = %o\n", Genus(FD2);
time A169, mp169 := AutomorphismGroup(FD2);
phi169, G169 := CosetAction(A169, sub<A169 | Id(A169)>);
printf "|Aut(D/F_%o)| = %o, GroupName = %o\n\n", p^2, #G169, GroupName(G169);

// Summary
printf "=== SUMMARY ===\n";
printf "Over F_%o:  |Aut(D)| = %o\n", p, #G13;
printf "Over F_%o: |Aut(D)| = %o\n", p^2, #G169;
printf "Ratio: %o\n", #G169 / #G13;
printf "Prediction: should go from 96 to 192 (ratio 2)\n";

quit;
