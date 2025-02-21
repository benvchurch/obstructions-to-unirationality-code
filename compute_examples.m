load "invariants.m";

runData := function(G, seq1, seq2)
    totalBasket, lTot, eTot, kTot := ComputeBasket(seq1, seq2, G);
    print "totalBasket: ", totalBasket;
    print "pi_1: ", Order(Pi1([seq1, seq2], G));
    print "K2: ", K2([seq1,seq2],G);
    print "Segre: ", SegreNumber([seq1,seq2],G);
    print "RR13: ", RR13Number([seq1, seq2], G);
    print "Bruin: ", BruinNumber([seq1, seq2], G);
    print "Diagonal: ", DiagonalFormNumber([seq1, seq2], G);
    return "";
end function;

findData := function(G, seq1, seq2)
    if Order(Pi1([seq1, seq2], G)) ne 1 then
        return false;
    end if;
    
    rr13 := RR13Number([seq1, seq2], G);
    bruin := BruinNumber([seq1, seq2], G);
    diagonal := DiagonalFormNumber([seq1, seq2], G);
    
    return rr13 gt 0 or bruin gt 0 or diagonal gt 0;
end function;


runCyclic := function(a,b)
// Get primes in range [10..20]
primes := [n : n in [a..b] | IsPrime(n)];

for n in primes do
    G := CyclicGroup(n);
    for p in primes do
        if p eq n then continue; end if;
        for q in primes do
            if q eq n or q eq p then continue; end if;
            seq1 := [ G.1 : i in [1..p] ];
            seq1 := Append(seq1, G.1^(n-p));
            seq2 := [ G.1 : i in [1..q] ];
            seq2 := Append(seq2, G.1^(n-q));
            
            if findData(G, seq1, seq2) then
                print p,q,n;
                runData(G, seq1, seq2);
            end if;
        end for;
    end for;
end for;
end function; 

// This looks like a real example!!!
G := SmallGroups(18)[3];
seq1 := [ G.1 * G.2^2 * G.3, G.2^2, G.3, G.2^2 * G.3, G.1 ];
seq2 := [ G.1 * G.2^2 * G.3, G.2 * G.3^2, G.2^2 * G.3, G.2 * G.3, G.1 * G.3^2 ];
runData(G, seq1, seq2);

seq1 := [ G.1 * G.2 * G.3^2, G.1 * G.2, G.2 * G.3, G.1, G.1 * G.3 ];
seq2 := [ G.1 * G.2^2 * G.3, G.1 * G.2^2 * G.3^2, G.2^2 * G.3, G.1 * G.3^2, G.1 ];
runData(G, seq1, seq2);

G := SmallGroups(18)[4];
seq1 := [ G.2^2 * G.3, G.2 * G.3, G.2, G.1 * G.3^2, G.1 * G.2^2 ];
seq2 := [ G.3, G.2^2 * G.3, G.2 * G.3, G.1 * G.3^2, G.1 * G.3^2 ];

runData(G, seq1, seq2);

G := AlternatingGroup(4);
x1 := G ! (1,3)(2,4);
x2 := G ! (1,2,3);
x3 := G ! (1,2,3);
x4 := G ! (2,4,3);

y1 := G ! (1,3)(2,4);
y2 := G ! (1,2)(3,4);
y3 := G ! (2,4,3);
y4 := G ! (1,2,4);

seq1 := [x1,x2,x3,x4];
seq2 := [y1,y2,y3,y4];

runData(G, seq1, seq2);

// NOT SIMPLY-CONNECTED

S8 := SymmetricGroup(8);
G := sub<S8| (3,6,7)(4,5,8), (1,8,2)(4,5,6)>;
x1 := G ! (1,8,2,4,3,7,5);
x2 := G ! (1,3,6)(2,8,4);
x3 := G ! (1,6,4)(3,5,7);

y1 := G ! (1,6,5,8,3,2,7);
y2 := G ! (1,4,7,8)(2,6,5,3);
y3 := (y1*y2)^(-1);

seq1 := [x1,x2,x3];
seq2 := [y1,y2,y3];

runData(G, seq1, seq2);


