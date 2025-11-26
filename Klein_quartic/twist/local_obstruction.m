/*  Check whether C_twist has points over K = Q(sqrt(-7))
    using local obstructions at p=2.  */

// find the locus of primes of bad reduction

Z := IntegerRing();
R<x,y,z> := PolynomialRing(Z, 3);
g := x^4 + y^4 + z^4 + 6*(x*y^3 + y*z^3 + z*x^3)
     - 3*(x^2*y^2 + y^2*z^2 + z^2*x^2) + 3*x*y*z*(x+y+z);
I := ideal< R | g, Derivative(g,1), Derivative(g,2), Derivative(g,3)>;
EliminationIdeal(I, {x}); 
EliminationIdeal(I, {y}); 
EliminationIdeal(I, {z});

// we see only factors of 7 appearing 

Q := Rationals();
P2<x,y,z> := ProjectiveSpace(Q, 2);

C_twist := Curve(P2, g);

print "=== C_twist ===";
print "Smooth:", IsNonsingular(C_twist);
print "Genus:", Genus(C_twist);


possible_primes := [];

for p in PrimesUpTo(50) do // bound comes from discriminant (computed above) and Hasse-Weil bound


// --- Key check: reduction mod p ---
C2 := ChangeRing(C_twist, GF(p));
pts := RationalPoints(C2);
print "\n=== Reduction mod ", p, " ===";
print "Good reduction: ", IsNonsingular(C2);
if not IsNonsingular(C2) then 
    print "BAD REDUCTION AT ", p;
    Append(~possible_primes, p);
end if;
print "#C_twist(F_",p,") =", #pts;
if #pts gt 0 then
    print "Points:", pts;
end if;

if #pts eq 0 then
    print "LOCAL OBSTRUCTION AT ", p;
    Append(~possible_primes,p);
end if;
end for;

possible_primes;

for p in possible_primes do
    print "\nKroneckerSymbol(-3, ",p,") =", KroneckerSymbol(-3, p);
    print "\nKroneckerSymbol(-7, ",p,") =", KroneckerSymbol(-7, p);
end for;


print "=== C_twist ===";
print "Smooth:", IsNonsingular(C_twist);
print "Genus:", Genus(C_twist);

// --- Key check: reduction mod 2 ---
C2 := ChangeRing(C_twist, GF(2));
pts2 := RationalPoints(C2);
print "\n=== Reduction mod 2 ===";
print "#C_twist(F_2) =", #pts2;
if #pts2 gt 0 then
    print "Points:", pts2;
end if;

print "\nKroneckerSymbol(-7, 2) =", KroneckerSymbol(-7, 2);
print "  => 2 splits in Q(sqrt(-7))";
print "  => completions at primes above 2 are Q_2";
print "  => residue field is F_2";

if #pts2 eq 0 then
    print "\n*** #C_twist(F_2) = 0 ***";
    print "=> C_twist has no Q_2-points (projective => any Q_2-pt reduces to F_2-pt)";
    print "=> LOCAL OBSTRUCTION at p=2";
    print "=> C_twist has NO points over Q(sqrt(-7))";
    print "   (and in fact no points over Q either)";
end if;

// --- Also check: does C_twist also fail over Q_2 via Hensel? ---
// Verify: the special fiber at 2 is actually singular?
print "\nSmooth over F_2:", IsNonsingular(C2);

// --- For completeness, check other small primes ---
print "\n=== Other small primes (local solubility) ===";
for p in [3, 5, 7, 11, 13, 17, 19, 23, 29, 31] do
    kron := KroneckerSymbol(-7, p);
    Cp := ChangeRing(C_twist, GF(p));
    np := #RationalPoints(Cp);

    if kron eq 0 then
        split_str := "ramifies";
        res_field := Sprintf("F_%o", p);
        need := np;
    elif kron eq 1 then
        split_str := "splits  ";
        res_field := Sprintf("F_%o", p);
        need := np;
    else
        split_str := "inert   ";
        res_field := Sprintf("F_%o^2", p);
        Cp2 := ChangeRing(C_twist, GF(p^2));
        need := #RationalPoints(Cp2);
    end if;

    printf "p=%2o %o: #C(F_%o)=%3o, #C(res.field)=%o %o\n",
           p, split_str, p, np, need,
           need eq 0 select "** OBSTRUCTION **" else "ok";
end for;

// --- Compare with the Klein model C ---
print "\n=== Comparison: Klein model C ===";
C := Curve(P2, x^3*y + y^3*z + z^3*x);
C2_klein := ChangeRing(C, GF(2));
print "#C(F_2) =", #RationalPoints(C2_klein);
print "C has Q-rational points: (1:0:0), (0:1:0), (0:0:1)";
print "So C is locally soluble everywhere.";
print "C_twist is a twist of C that becomes isomorphic over some extension,";
print "but is obstructed at p=2 over Q and Q(sqrt(-7)).";

