/*******************************************************************************
 * check_conjugate.m
 *
 * Check if the genus 5 cover D: w^2 = q1 is isomorphic to its Galois
 * conjugate sigma(D): w^2 = sigma(q1) over Q(sqrt(-3)).
 *
 * Work at p=7 where sqrt(-3) = 2 (and sigma sends 2 -> -2 = 5).
 * D ~ sigma(D) iff the 2-torsion classes eta, sigma(eta) are equal.
 ******************************************************************************/

p := 7;
Fp := GF(p);

// Check sqrt(-3) mod 7
assert Fp!2^2 eq Fp!(-3);  // 4 = -3 mod 7
printf "p = %o, sqrt(-3) = 2 mod 7\n\n", p;

// Function field of C: u^4 + t^4 + 1 = 0
Fpt<t> := FunctionField(Fp);
Fptu<u> := PolynomialRing(Fpt);
ff := u^4 + t^4 + 1;
printf "u^4+t^4+1 irreducible over F_%o? %o\n", p, IsIrreducible(ff);
if not IsIrreducible(ff) then
    print "PROBLEM: curve reducible at this prime!";
    quit;
end if;

FF := FunctionField(ff);
Cl, m := ClassGroup(FF);
elt_t := FF ! t;
elt_u := FF.1;

printf "Class group: ";
invs := Invariants(Cl);
for i in [1..#invs] do
    if i gt 1 then printf " x "; end if;
    if invs[i] eq 0 then printf "Z"; else printf "Z/%oZ", invs[i]; end if;
end for;
printf "\n";

// J[2]
tors_gens := [];
for i in [1..#invs] do
    if invs[i] ne 0 and invs[i] mod 2 eq 0 then
        Append(~tors_gens, (invs[i] div 2) * Cl.i);
    end if;
end for;
J2 := sub<Cl | tors_gens>;
printf "J[2] order = %o\n\n", #J2;

function HalfDiv(D)
    B := D - D;
    for pl in Support(D) do
        v := Valuation(D, pl);
        if v mod 2 ne 0 then return false, B; end if;
        B := B + (v div 2) * pl;
    end for;
    return true, B;
end function;

// The Q(sqrt(-3)) decomposition with w = sqrt(-3)
// Q1 = 2X^2 + (1-w)Y^2 + (1+w)Z^2
// Reduce at p=7 with w = 2:
w1 := Fp!2;
Q1_w1 := 2*elt_t^2 + (1-w1)*elt_u^2 + (1+w1);  // z=1
printf "eta (w=2): q1 = %o\n", Q1_w1;
D1 := Divisor(Q1_w1);
ok1, half1 := HalfDiv(D1);
printf "  div(q1) all even? %o\n", ok1;
if ok1 then
    eta1 := half1 @@ m;
    printf "  (1/2)div(q1) = %o\n", eta1;
    printf "  In J[2]? %o\n", eta1 in J2;
end if;

// Conjugate: sigma(w) = -w, so w = -2 = 5 mod 7
w2 := Fp!5;
Q1_w2 := 2*elt_t^2 + (1-w2)*elt_u^2 + (1+w2);  // z=1
printf "\nsigma(eta) (w=5): sigma(q1) = %o\n", Q1_w2;
D2 := Divisor(Q1_w2);
ok2, half2 := HalfDiv(D2);
printf "  div(sigma(q1)) all even? %o\n", ok2;
if ok2 then
    eta2 := half2 @@ m;
    printf "  (1/2)div(sigma(q1)) = %o\n", eta2;
    printf "  In J[2]? %o\n", eta2 in J2;
end if;

if ok1 and ok2 then
    printf "\neta = sigma(eta)? %o\n", eta1 eq eta2;
    printf "eta - sigma(eta) = %o\n", eta1 - eta2;
    if eta1 eq eta2 then
        print "D is isomorphic to sigma(D) as covers of C.";
    else
        print "D is NOT isomorphic to sigma(D)!";
        printf "  eta - sigma(eta) in J[2]? %o\n", (eta1-eta2) in J2;
    end if;
end if;

quit;
