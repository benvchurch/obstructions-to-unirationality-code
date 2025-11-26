/*******************************************************************************
 * quadric_obstruction.m
 *
 * The decomposition with Q2 = Y^2+Z^2 over F_3 gives the class e1+e2+e3
 * NOT in V_rat. Check if F + Q2^2 factors over Q, Q(sqrt(-1)), Q(sqrt(-2)),
 * Q(sqrt(2)), etc.
 ******************************************************************************/

// Over Q
print "=== FACTORING F + Q2^2 OVER Q ===";
RQ<X,Y,Z> := PolynomialRing(Rationals(), 3);
FQ := X^4 + Y^4 + Z^4;

// Q2 = Y^2 + Z^2
Q2 := Y^2 + Z^2;
G := FQ + Q2^2;
printf "F + (Y^2+Z^2)^2 = %o\n", G;
facQ := Factorization(G);
printf "Factorization over Q: ";
for pair in facQ do
    printf "(%o)^%o ", pair[1], pair[2];
end for;
printf "\n\n";

// Also check the other key Q2 values from the F_3 search
for Q2_data in [
    <X*Y + Z^2, "XY+Z^2">,
    <X*Z + Y^2, "XZ+Y^2">,
    <Y^2 + Y*Z + Z^2, "Y^2+YZ+Z^2">
] do
    Q2 := Q2_data[1];
    name := Q2_data[2];
    G := FQ + Q2^2;
    facQ := Factorization(G);
    printf "Q2 = %o: F+Q2^2 = ", name;
    for pair in facQ do
        printf "(%o)^%o ", pair[1], pair[2];
    end for;
    printf "\n";
end for;

// Now try over Q(sqrt(-2))
print "";
print "=== FACTORING OVER Q(sqrt(-2)) ===";
K<w> := QuadraticField(-2);
RK<X,Y,Z> := PolynomialRing(K, 3);
FK := X^4 + Y^4 + Z^4;

Q2 := Y^2 + Z^2;
G := FK + Q2^2;
facK := Factorization(G);
printf "F + (Y^2+Z^2)^2 over Q(sqrt(-2)): ";
for pair in facK do
    printf "(%o)^%o ", pair[1], pair[2];
end for;
printf "\n";

// Check all four Q2 values
for Q2_data in [
    <X*Y + Z^2, "XY+Z^2">,
    <X*Z + Y^2, "XZ+Y^2">,
    <Y^2 + Y*Z + Z^2, "Y^2+YZ+Z^2">
] do
    Q2 := Q2_data[1];
    name := Q2_data[2];
    G := FK + Q2^2;
    facK := Factorization(G);
    printf "Q2 = %o: ", name;
    for pair in facK do
        printf "(%o)^%o ", pair[1], pair[2];
    end for;
    printf "\n";
end for;

// Also try Q(sqrt(-1))
print "";
print "=== FACTORING OVER Q(sqrt(-1)) = Q(i) ===";
Ki<i> := QuadraticField(-1);
RKi<X,Y,Z> := PolynomialRing(Ki, 3);
FKi := X^4 + Y^4 + Z^4;

Q2 := Y^2 + Z^2;
G := FKi + Q2^2;
facKi := Factorization(G);
printf "F + (Y^2+Z^2)^2 over Q(i): ";
for pair in facKi do
    printf "(%o)^%o ", pair[1], pair[2];
end for;
printf "\n";

for Q2_data in [
    <X*Y + Z^2, "XY+Z^2">,
    <X*Z + Y^2, "XZ+Y^2">,
    <Y^2 + Y*Z + Z^2, "Y^2+YZ+Z^2">
] do
    Q2 := Q2_data[1];
    name := Q2_data[2];
    G := FKi + Q2^2;
    facKi := Factorization(G);
    printf "Q2 = %o: ", name;
    for pair in facKi do
        printf "(%o)^%o ", pair[1], pair[2];
    end for;
    printf "\n";
end for;

// Also try Q(sqrt(2))
print "";
print "=== FACTORING OVER Q(sqrt(2)) ===";
K2<s> := QuadraticField(2);
RK2<X,Y,Z> := PolynomialRing(K2, 3);
FK2 := X^4 + Y^4 + Z^4;

Q2 := Y^2 + Z^2;
G := FK2 + Q2^2;
facK2 := Factorization(G);
printf "F + (Y^2+Z^2)^2 over Q(sqrt(2)): ";
for pair in facK2 do
    printf "(%o)^%o ", pair[1], pair[2];
end for;
printf "\n";

for Q2_data in [
    <X*Y + Z^2, "XY+Z^2">,
    <X*Z + Y^2, "XZ+Y^2">,
    <Y^2 + Y*Z + Z^2, "Y^2+YZ+Z^2">
] do
    Q2 := Q2_data[1];
    name := Q2_data[2];
    G := FK2 + Q2^2;
    facK2 := Factorization(G);
    printf "Q2 = %o: ", name;
    for pair in facK2 do
        printf "(%o)^%o ", pair[1], pair[2];
    end for;
    printf "\n";
end for;

// Try Q(zeta_8) = Q(sqrt(-1), sqrt(2)) = the 2-torsion field
print "";
print "=== FACTORING OVER Q(zeta_8) ===";
P<x> := PolynomialRing(Rationals());
K8<z8> := NumberField(x^4 + 1);
RK8<X,Y,Z> := PolynomialRing(K8, 3);
FK8 := X^4 + Y^4 + Z^4;

Q2 := Y^2 + Z^2;
G := FK8 + Q2^2;
facK8 := Factorization(G);
printf "F + (Y^2+Z^2)^2 over Q(zeta_8): ";
for pair in facK8 do
    printf "(%o)^%o ", pair[1], pair[2];
end for;
printf "\n";

for Q2_data in [
    <X*Y + Z^2, "XY+Z^2">,
    <X*Z + Y^2, "XZ+Y^2">,
    <Y^2 + Y*Z + Z^2, "Y^2+YZ+Z^2">
] do
    Q2 := Q2_data[1];
    name := Q2_data[2];
    G := FK8 + Q2^2;
    facK8 := Factorization(G);
    printf "Q2 = %o: ", name;
    for pair in facK8 do
        printf "(%o)^%o ", pair[1], pair[2];
    end for;
    printf "\n";
end for;

quit;
