/*******************************************************************************
 * Gamma0.m
 *
 * Purpose:
 *   Verify that "conjugated" Shimura curves at level Gamma_0(13^2) have the
 *   correct genera. This is related to studying modular curves and their
 *   quotients by Borel subgroups.
 *
 * Method:
 *   1. Construct PSL(2, Z/169Z) as the appropriate level structure group
 *   2. Create the Borel-Unipotent subgroup BU (upper triangular mod 13)
 *   3. Find spherical generators (2,3,7)-triple generating the full group
 *   4. Compute genus of the curve and the intermediate extension via BU
 *
 * Output:
 *   - Genus of the full Shimura curve
 *   - Genus of the quotient by Borel-Unipotent subgroup
 *
 * Dependencies:
 *   - intermediate_extensions.m: GenusIntermediateExtension, Genus, etc.
 *
 * Note:
 *   Includes optional data caching via loadComputedData/saveComputedData
 *   to avoid expensive recomputation.
 ******************************************************************************/

// In this file we verify that certain "conjugated" Shimura curves at level Gamma_0(p_13^2) have the correct genera

import "intermediate_extensions.m": GenusIntermediateExtension, Genus,
    IntermediateMonodromy, GetMonodromyIntermediateExtension;

// Create the group PSL(2, Z/13^2Z)
Z := Integers();
R := Integers(13^2);
SL2R := SL(2, R);
G, pi := quo<SL2R | -Id(SL2R)>;

// Create the Borel subgroup (upper triangular matrices)
A, m := UnitGroup(R);
Tgen := SL2R ! [m(A.1), 0, 0, m(-A.1)]; // generator of the maximal torus
Ugen := SL2R ! [1, 1, 0, 1]; // generator of the unipotent radical
BU := sub<G | pi(Tgen^(13)), pi(Ugen)>;
print "Borel-Unipotent subgroup order:", #BU;
print "Borel-Unipotent subgroup:", BU;

// Check if we have precomputed data
filename := "gamma0_computed_data.m";
success, precomputed_data := loadComputedData(filename);

if success then
    print "Loading precomputed data...";
    seq := precomputed_data`seq;
    classes := precomputed_data`classes;
    print "Found", #seq, "sequences";
else
    print "Computing data...";
    seq := [];
    classes := ConjugacyClasses(G);
    
    for c1 in classes do
        if Order(c1[3]) eq 2 then
            for c2 in classes do
                if Order(c2[3]) eq 3 then
                    g1 := c1[3];
                    for h in G do
                        g2 := (c2[3])^h;
                        if Order(g1*g2) eq 7 then
                            if sub<G | g1, g2> eq G then
                                print "found";
                                seq := [g1, g2, (g1*g2)^-1];
                                break;
                            end if;
                        end if;
                    end for;
                end if;
            end for;
        end if;
    end for;
    
    // Save the computed data
    data := rec<seq := seq, classes := classes>;
    saveComputedData(filename, data);
    print "Data saved to", filename;
end if;

Genus(G, seq);
GenusIntermediateExtension(G, seq, BU);







