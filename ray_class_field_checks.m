// Here we check that the various definitions of K agree.

F := CyclotomicField(7);
K := sub<F | F.1 + F.1^(-1)>;

OK := RingOfIntegers(K);
fact := Factorization(13*OK);
pp := fact[1][1];
G, m := RayClassGroup(pp,[1..3]);

Kpp := NumberField(AbelianExtension(m));
Kpp := AbsoluteField(Kpp);

Discriminant(RingOfIntegers(Kpp));
Signature(Kpp);

// Define the number field: 
R<x> := PolynomialRing(Rationals()); 
L<a> := NumberField(x^6 - 2*x^5 + 2*x^4 - 3*x^3 + 2*x^2 - 2*x + 1);

IsIsomorphic(Kpp, L);


