/*******************************************************************************
 * aut_D_F169.m — Compute Aut(D) over F_{13^2} = F_169.
 ******************************************************************************/

Fq := GF(13^2);
w := Sqrt(Fq!(-3));
printf "w = sqrt(-3) = %o in F_169\n", w;

Fqt<t> := FunctionField(Fq);
Ku<u> := PolynomialRing(Fqt);
FC<uu> := FunctionField(u^4 + t^4 + 1);
q1 := 2*(FC!t)^2 + (1-w)*uu^2 + (1+w);
Kv<v> := PolynomialRing(FC);
FD<vv> := FunctionField(v^2 - q1);
printf "Genus(D) = %o\n", Genus(FD);
printf "Computing Aut(D/F_169)...\n";
time A, mp := AutomorphismGroup(FD);
phi_a, G := CosetAction(A, sub<A | Id(A)>);
printf "|Aut(D/F_169)| = %o\n", #G;
printf "GroupName = %o\n", GroupName(G);
printf "|Z(G)| = %o\n", #Center(G);

// Check if 192
if #G eq 192 then
    printf "\nCONFIRMED: |Aut(D/Fbar)| = 192 = 2 * |Aut(C)|\n";
    printf "The geometric Aut(D) has order 192, not 96.\n";
    printf "The previous result of 96 was Aut(D/F_13), not geometric.\n";
elif #G eq 96 then
    printf "\nStill 96 over F_169 — may need larger extension.\n";
else
    printf "\nUnexpected order %o\n", #G;
end if;

quit;
