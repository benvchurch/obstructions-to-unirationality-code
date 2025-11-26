K<x> := CyclotomicField(7);
F := sub<K | x + x^(-1)>;

primes := PrimesUpTo(100,F);

for i in [1..#primes] do

    q := Norm(primes[i]);

    print "q = ", q;
    G := PSL(2, q);

    // get a fixed element of order 2
    conj := ConjugacyClasses(G);

    g2 := Id(G);

    for c in conj do
        if c[1] eq 2 then
            g2 := c[3];
        end if;
    end for;


    // for each element of order 3, check if its product has order 7 and generates the entire group
    for c in conj do
        if c[1] eq 3 then
            for h in G do 
                g3 := c[3] ^ h;
                if Order(g3 * g2) eq 7 and sub<G |g2, g3> eq G then
                    print "Found: g3 = ", g3;
                    break;
                end if;
            end for;
        end if;
    end for;

    g7 := (g2 * g3)^(-1);
    seq := [g2, g3, g7];

    import "invariants.m": K2, HodgeDiamond;
    print " ";

    print "K2 = ", K2([seq, seq], G);

    HodgeDiamond([seq, seq], G);

end for;