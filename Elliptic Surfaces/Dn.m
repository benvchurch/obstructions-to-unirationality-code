import "../invariants.m": K2, HodgeDiamond, ComputeBasket, SegreNumber, MyPi1, GammaBas;
import "../group_reps.m": computeRationalCohomology;

for n in [3..10] do

    G := DihedralGroup(n);

    gn := G.1;
    g2 := G.2;

    seq := [gn, gn^(-1), g2, g2];

    print " ";

    print "K2 = ", K2([seq, seq], G);
    print "Segre = ", SegreNumber([seq, seq], G);
    pg, h11 := HodgeDiamond([seq, seq], G);

    print "Rational cohomology = ", computeRationalCohomology(G, seq);
    print "Gamma = ", GammaBas(ComputeBasket(seq, seq, G)); // conjecturally this detects minimality for a general type surface?
end for;



for n in [3..3] do

    G := CyclicGroup(n);

    gn := G.1;

    seq := [gn, gn, gn];

    print "K2 = ", K2([seq, seq], G);
    print "Segre = ", SegreNumber([seq, seq], G);
    pg, h11 := HodgeDiamond([seq, seq], G);

    print "Rational cohomology = ", computeRationalCohomology(G, seq);
    print "Gamma = ", GammaBas(ComputeBasket(seq, seq, G)); 
end for;