// finds the Galois-invariant subgroups of Aut(C)

prim_root := 2; // primitive root mod 13

SL2 := SL(2,13);
GL2 := GL(2,13);

inc := hom<SL2 -> GL2 | x :-> x>;

PGL2, piG := quo<GL2 | GL2 ! [[prim_root,0], [0,prim_root]] >;  // create PGL(2, 13) as a quotient
PSL2 := piG(inc(SL2));

C2, det := quo<PGL2 | PSL2>;

// for the Galois extension K / K+ there is a unique outer form of PSL(2, 13). 
// Since Gal(K/K+) = C_2 it is given by the unique element of order 2 in Aut(PSL(2,13)) = PGL(2,13) with nonsquare determinant up to conjugacy..

// indeed: find this unique class and check that it is unique

g_2 := Id(PGL2);
is_unique := true;
is_assigned := false;

for C in ConjugacyClasses(PGL2) do
    if C[1] eq 2 then // if it has order 2
        g := C[3];
        if det(g) ne Id(C2) then // if it has nonsquare determinant
            g_2 := g;
            g;
            if not is_assigned then
                is_assigned := true;
            else
                is_unique := false;
            end if;
        end if;
    end if;
end for;

print "Found g_2: ", is_assigned;
print "Is unique: ", is_unique;

mat := g_2 @@ piG; // get a matrix representative of g_2 in GL(2,13)
print "Matrix representative of g_2: ", mat; // print it

// now we determine its action on the subgroup lattices of SL(2,13)

aut := hom<PSL2 -> PSL2 | x :-> x^(g_2)>; // action of g_2 on PSL(2,13) by conjugation

// first we need to find the subgroups of SL(2,13)

rec := Subgroups(PSL2);
subgroupClasses := [H`subgroup : H in rec]; // get the conjugacy classes of subgroups of PSL(2,13)
subgroups := &join [Conjugates(PSL2, H) : H in subgroupClasses]; // union of all conjugates

// we need to find the subgroups of SL(2,13) that are invariant under the action of g_2

invariant_subgroups := [H : H in subgroups | aut(H) eq H];

print "Number of invariant subgroups: ", #invariant_subgroups;
orders := [Order(H) : H in invariant_subgroups];
print "Orders of invariant subgroups: ", orders;

// now we need to determined the number of subgroups of each conjugacy class invariant by g_2

counts := [];
for i in [1..#subgroupClasses] do
    Hrep := subgroupClasses[i]; // representative of the conjugacy class
    count := 0;
    for H in invariant_subgroups do
        if IsConjugate(PSL2, Hrep, H) then
            count +:= 1;
        end if;
    end for;
    Append(~counts, count);
end for;

print "Number of subgroups of each conjugacy class invariant by g_2: ", counts;

// we are interested in the subroups 10,13,14 which are D_7, D_6, A_4 respectively
// we need to find the number of subgroups of these orders in the conjugacy classes

print "Invariant copies of D_7: ", counts[10];
print "Invariant copies of D_6: ", counts[13];
print "Invariant copies of A_4: ", counts[14];
