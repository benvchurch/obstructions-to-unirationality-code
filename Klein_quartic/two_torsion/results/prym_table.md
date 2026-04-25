# Prym varieties of etale double covers: genus-2 isomorphism classes

Each smooth plane quartic C has 63 Steiner complexes (= nontrivial elements of J(C)[2]).
Each Steiner complex determines an etale double cover whose Prym is a principally
polarized abelian surface, generically a genus-2 Jacobian.  We identify the genus-2
curve up to geometric isomorphism via absolute Igusa invariants (j1, j2, j3).

For each isomorphism class we also report:
- **Extra Z/3 symmetry:** Whether the 6 branch points of the genus-2 hyperelliptic
  cover admit a partition into two Z/3-orbits {x, 1-1/x, 1/(1-x)}.  When this
  holds, the genus-2 Jacobian has an elliptic factor whose j-invariant we record
  via its minimal polynomial over Q.
- **Reduced automorphism group:** The reduced automorphism group RA(C_g2) =
  Aut(C_g2)/\<hyperelliptic involution\> acts faithfully on P^1 via Mobius
  transformations permuting the 6 branch points.  We detect two levels:
  - **RA ⊇ (Z/2)^2:** Branch points in the form {0, 1, -1, λ, 1/λ, ∞}.
    The Klein four-group V_4 acts via x→1/x, x→(λx-1)/(x-λ), and their
    composition.  The Jacobian decomposes J ~ E_1 × E_2 where E_1, E_2 are
    the two Z/2-quotient elliptic curves.  Marked "(Z/2)^2" in the tables.
  - **RA ⊇ Z/2:** Branch points admit a Mobius involution (but not
    necessarily the {0,1,-1,λ,1/λ,∞} form).  The normal form is
    y^2 = x(x-1)(x-a)(x-b)(x-a(1-b)/(1-a)).  Marked "Z/2" in the tables.
  For all three quartics studied, **every** Prym has RA ⊇ Z/2 (63/63).
  This is a consequence of the large automorphism groups: the stabilizer of
  any Steiner complex in Aut(C) is nontrivial and induces non-hyperelliptic
  automorphisms of the Prym.
- **Collinear triples:** Among the Steiner complexes producing a given isomorphism
  class, we count unordered triples {x, y, z} with x + y + z = 0 in J[2] (i.e.,
  collinear in the F₂-projective space PG(5, F₂)).

---

## Klein twist

**Quartic:** x^4 - 3x^2y^2 + 6xy^3 + y^4 + 6x^3z + 3x^2yz + 3xy^2z - 3x^2z^2 + 3xyz^2 - 3y^2z^2 + 6yz^3 + z^4

**Bitangent field:** Q(w), w^2 + 5w/2 + 2 = 0  (degree 2 over Q)

**Aut(C):** PSL(2,7) (order 168) | **J[2] module:** V + V* (semisimple, two irreducible 3-dim summands)

### Igusa classes, extra symmetries, and collinear triples

| # | Absolute Igusa invariants (j1, j2, j3) | Count | RA ⊇ | Coll. triples | Orbit field |
|---|----------------------------------------|-------|------|--------------|-------------|
| 1 | (2048, -192, 64) | 28 | S_3 | 56 | Q |
| 2 | (2048/343, 4416/343, -2816/343) | 21 | (Z/2)^2 | 28 | Q |
| 3 | (-76740102w - 95211256, -3674430w - 3245592, 39906w - 728) /343 | 7 | S_3 | 7 | Q(√-7) |
| 4 | (76740102w + 96638999, 3674430w + 5940483, -39906w - 100493) /343 | 7 | S_3 | 7 | Q(√-7) |

**Total:** 63 = 28 + 21 + 7 + 7.  Classes 3 and 4 are Galois conjugate over Q.

#### Extra Z/3 symmetry (elliptic j-invariant from branch point Z/3-orbit)

All 28 complexes in class 1 have a Z/3-orbit on their branch points, as do all 14
complexes in classes 3 and 4 combined.  The 21 complexes in class 2 have no Z/3-orbit.

| Elliptic j min poly | Classes | # complexes | mp(1728) factorization |
|---------------------|---------|-------------|------------------------|
| t^2 + 13856t - 26578688 | 1 | 28 | 2^8 . 37^2 |
| t^4 - 103439t^3 + 6670405329t^2 + 31128229267744t + 148381159092130048 | 3, 4 | 14 | 2^8 . 11^6 . 23^2 . 31^4 |
| (no Z/3 orbit) | 2 | 21 | -- |

#### Reduced automorphism group (involutions beyond hyperelliptic)

**All 63 complexes have RA ⊇ Z/2** (at least one extra involution).  This
follows from the large automorphism group: PSL(2,7) acting on J[2] stabilizes
each complex with a subgroup of order ≥ 6, inducing non-hyperelliptic automorphisms.

**21 of 63 have RA ⊇ (Z/2)^2** (the stronger condition).  All 21 belong
to class 2, and every member of class 2 has (Z/2)^2.  The lambda minimal
polynomial takes two conjugate forms, each yielding a distinct elliptic
j-invariant for the Z/2 quotient:

| Class | Lambda min poly | Elliptic j min poly | # complexes |
|-------|-----------------|---------------------|-------------|
| 2 | t^2 + 3/2 t + 1 | t^2 + 7184t + 16777216 | 21 (all) |
| 2 | t^2 - 3/2 t + 1 | t^2 + 7184t + 16777216 | 21 (all) |

Both lambda conjugates give the same elliptic j min poly t^2 + 7184t + 16777216,
with discriminant -2^8 . 3^2 . 7 . 31^2.  The j-values lie in Q(sqrt(-7)).
The two quotient elliptic curves (roots of the j-poly) are **twist-isogenous**
(a_p agree up to sign at all primes, with ~50/50 split).

**Observation:** Class 2 is the unique Igusa class with (Z/2)^2.
Classes 1, 3, 4 have only Z/2 (not (Z/2)^2).  The complementary pattern with
Z/3 still holds: classes 1, 3, 4 have Z/3, while class 2 does not.

#### Syzygetic triples within Igusa classes

| Class | Size | # syz. triples | Ratio C(n,3) | Triples |
|-------|------|----------------|-------------|---------|
| 1 (j1=2048) | 28 | 56 | 56/3276 | {3,4,34}, {3,10,13}, {3,20,35}, {3,25,49}, {3,38,63}, {3,52,57}, {4,9,13}, {4,20,37}, {4,26,49}, {4,40,63}, {4,53,57}, {7,9,37}, {7,10,35}, {7,13,20}, {7,18,29}, {7,27,45}, {7,39,59}, {9,10,34}, {9,26,39}, {9,27,53}, {9,29,40}, {10,25,39}, {10,27,52}, {10,29,38}, {13,27,57}, {13,29,63}, {13,39,49}, {18,20,63}, {18,24,45}, {18,35,38}, {18,37,40}, {18,51,59}, {20,45,57}, {20,49,59}, {24,27,29}, {24,38,52}, {24,40,53}, {24,48,51}, {24,57,63}, {25,26,34}, {25,35,59}, {25,38,51}, {25,48,52}, {26,37,59}, {26,40,51}, {26,48,53}, {27,39,48}, {29,39,51}, {34,35,37}, {34,38,40}, {34,52,53}, {35,45,52}, {37,45,53}, {45,48,59}, {48,49,57}, {49,51,63} |
| 2 (j1=2048/343) | 21 | 28 | 28/1330 | {1,11,30}, {1,22,58}, {1,28,60}, {1,47,55}, {2,5,17}, {2,15,56}, {2,21,58}, {2,28,61}, {5,8,11}, {5,32,56}, {5,47,61}, {8,22,32}, {8,43,61}, {8,46,62}, {11,22,56}, {11,43,47}, {15,17,32}, {15,21,30}, {15,46,55}, {17,28,47}, {17,55,60}, {21,43,46}, {21,61,62}, {22,60,62}, {28,58,62}, {30,43,55}, {30,56,58}, {32,46,60} |
| 3 (conj. pair) | 7 | 7 | 7/35 | {6,16,41}, {6,19,33}, {6,23,42}, {16,19,42}, {16,23,33}, {19,23,41}, {33,41,42} |
| 4 (conj. pair) | 7 | 7 | 7/35 | {12,14,36}, {12,31,50}, {12,44,54}, {14,31,54}, {14,44,50}, {31,36,44}, {36,50,54} |

**Observation:** Classes 3 and 4 each have the maximum possible number of collinear
triples for 7 elements: C(7,3)/C(7,3) is not the right comparison -- rather, 7
elements in F_2^6 forming 7 = C(7,3)/5 collinear triples means every triple from
this 7-element set that is collinear has been counted.  In fact 7 out of C(7,3)=35
triples are collinear, exactly 1/5 of all triples.

---

## Fermat quartic

**Quartic:** x^4 + y^4 + z^4

**Bitangent field:** Q(w), w^4 + 1 = 0  (degree 4 over Q)

**Aut(C):** order 96 (C_4^2 : C_3 : C_2) | **J[2] module:** uniserial 6-dim, comp factors 1,2,2,1 (not semisimple)

### Igusa classes, extra symmetries, and collinear triples

| # | Absolute Igusa invariants (j1, j2, j3) | Count | RA ⊇ | Coll. triples | Orbit field |
|---|----------------------------------------|-------|------|--------------|-------------|
| 1 | (131072, 6144, -512) | 24 | Z/2 | 64 | Q |
| 2 | (-224208w^3 + 224208w + 344408, ...) | 16 | S_3 | 0 | Q(√2) |
| 3 | (224208w^3 - 224208w + 344408, ...) | 16 | S_3 | 0 | Q(√2) |
| 4 | (8388608, 245760, 4096) | 6 | (Z/2)^2 | 4 | Q |
| 5 | (50000, 3750, -125) | 1 | S_4 | 0 | Q |

**Total:** 63 = 24 + 16 + 16 + 6 + 1.  Classes 2 and 3 are Galois conjugate
over Q; each orbit is individually well-defined over Q(√2) since the Igusa
invariants involve w³ − w = √2.

#### Extra Z/3 symmetry (elliptic j-invariant from branch point Z/3-orbit)

| Elliptic j min poly | Classes | # complexes | mp(1728) factorization |
|---------------------|---------|-------------|------------------------|
| t - 8000 | 5 | 1 | 2^7 . 7^2  (j = 8000, CM by Z[sqrt(-2)]) |
| t^4 + 73216t^3 + 1533640704t^2 + 6119514701824t - 15081210455785472 | 2, 3 | 32 | 2^24 . 5233^2 |
| (no Z/3 orbit) | 1, 4 | 30 | -- |

The Z/3-bearing complexes are exactly classes 2, 3, and 5.  Class 1 (the largest,
with 24 members) and class 4 have no Z/3 orbit.

#### Reduced automorphism group (involutions beyond hyperelliptic)

**All 63 complexes have RA ⊇ Z/2.**  The Fermat automorphism group (order 96)
stabilizes each complex with a subgroup of order ≥ 4, inducing extra involutions.

**7 of 63 have RA ⊇ (Z/2)^2**, falling into two Igusa classes:

| Igusa class | RA ⊇ | Lambda min poly | Elliptic j (Z/2 quotient) | Complex indices |
|-------------|-------|-----------------|---------------------------|-----------------|
| 5: (50000, 3750, -125) | S_4 | t^2 + 1 | j = 8000 | 34 |
| 4: (8388608, 245760, 4096) | (Z/2)^2 | t^2 - 1/2 | j = 128 | 3, 4, 38, 40, 62, 63 |

**Class 5 (the unique complex #34):** This is the most special Prym of the Fermat quartic.
It has RA = S_4: the branch points {0, 1, -1, i, -i, infinity} admit the full
symmetric group of Mobius transformations.  The Z/2 and Z/3 quotients give the
**same** elliptic curve (j = 8000, CM by Z[sqrt(-2)]).

**Class 4 (all 6 members have (Z/2)^2):** Geometric full Aut = D_4 (order 8), J ~ E x E where
Lambda min poly t^2 - 1/2 (lambda = 1/sqrt(2)).  **The Z/2 quotient gives j = 128**,
confirming the isogeny decomposition J ~ E^2 with E = 128a1.

**Classes 1, 2, 3 (56 members, RA ⊇ Z/2 but not (Z/2)^2):**
Class 1 has RA ⊇ Z/2 (no Z/3 or (Z/2)^2).
Classes 2, 3 have RA ⊇ S_3 (Z/3 orbit present, which forces an involution).

#### Syzygetic triples within Igusa classes

| Class | Size | # syz. triples | Triples |
|-------|------|----------------|---------|
| 1 (j1=131072) | 24 | 64 | {5,15,41}, {5,16,39}, {5,21,51}, {5,22,50}, {5,25,45}, {5,26,44}, {5,47,61}, {5,49,60}, {6,15,39}, {6,16,41}, {6,21,50}, {6,22,51}, {6,25,44}, {6,26,45}, {6,47,60}, {6,49,61}, {9,15,45}, {9,16,44}, {9,21,49}, {9,22,47}, {9,25,41}, {9,26,39}, {9,50,61}, {9,51,60}, {10,15,44}, {10,16,45}, {10,21,47}, {10,22,49}, {10,25,39}, {10,26,41}, {10,50,60}, {10,51,61}, {13,15,61}, {13,16,60}, {13,21,26}, {13,22,25}, {13,39,49}, {13,41,47}, {13,44,51}, {13,45,50}, {14,15,60}, {14,16,61}, {14,21,25}, {14,22,26}, {14,39,47}, {14,41,49}, {14,44,50}, {14,45,51}, {15,21,30}, {15,22,29}, {16,21,29}, {16,22,30}, {25,29,61}, {25,30,60}, {26,29,60}, {26,30,61}, {29,39,51}, {29,41,50}, {29,44,49}, {29,45,47}, {30,39,50}, {30,41,51}, {30,44,47}, {30,45,49} |
| 2 (Galois conj.) | 16 | 0 | (none) |
| 3 (Galois conj.) | 16 | 0 | (none) |
| 4 (j1=8388608) | 6 | 4 | {3,38,63}, {3,40,62}, {4,38,62}, {4,40,63} |
| 5 (j1=50000) | 1 | 0 | (only 1 element) |

**Observation:** The two Galois-conjugate 16-element classes have ZERO collinear triples.
This is remarkable: among C(16,3) = 560 triples, not a single one sums to zero in J[2].
This strongly constrains the geometry of how these 16 elements sit inside F_2^6.

Meanwhile, class 1 (24 elements) has 64 collinear triples out of C(24,3) = 2024
possible, and class 4 (6 elements) has 4 out of C(6,3) = 20.

---

## Edge quartic

**Quartic:** 25x^4 - 34x^2y^2 + 25y^4 - 34x^2z^2 - 34y^2z^2 + 25z^4

**Bitangent field:** Q  (all 28 bitangents rational)

**Aut(C):** S_4 (order 24). Generated by coordinate permutations S_3 and sign
changes (x:y:z) -> (-x:y:z), (x:-y:z) (possible because all monomials have even
degree in each variable). S_3 x (Z/2)^2 / (overall sign) = S_4.

**J[2] as F_2[S_4]-module:** two non-split 3-dim indecomposable summands (not semisimple).
Composition factors: trivial(1), irred(2), irred(2), trivial(1). The two irred(2) factors
are isomorphic (the unique 2-dim simple F_2[S_4]-module, inflated from S_3 = GL(2,F_2)
via S_4 -> S_4/V_4 = S_3). The summands are: 0 -> trivial -> V_1 -> irred(2) -> 0
and 0 -> irred(2) -> V_2 -> trivial -> 0.
Restriction to S_3 is SEMISIMPLE: trivial + trivial + irred(2) + irred(2).

**S_4 orbits on J[2]\{0}:** 10 orbits, sizes {1, 3, 3, 4, 4, 6, 6, 12, 12, 12},
**exactly matching the 10 Igusa invariant classes.**

### Igusa classes, extra symmetries, and collinear triples

| # | Absolute Igusa invariants (j1, j2, j3) | Count | RA ⊇ | Coll. triples | Orbit field |
|---|----------------------------------------|-------|------|--------------|-------------|
| 1 | (1729733224448/151875, 1496258752/5625, -1425053696/4100625) | 12 | Z/2 | 0 | Q |
| 2 | (31172342123300864/5955980625, ..., 68168000576/73530625) | 12 | Z/2 | 0 | Q |
| 3 | (800000000/81, 23560000/81, 40000/9) | 12 | Z/2 | 8 | Q |
| 4 | (68934134667875/28588707, ..., -316737676475/771895089) | 6 | Z/2 | 4 | Q |
| 5 | (1429519218944000/28588707, ..., 33694083654400/771895089) | 6 | Z/2 | 4 | Q |
| 6 | (6400000/3, 440000/9, -32000/81) | 4 | D_6 | 0 | Q |
| 7 | (443801324800000/85766121, ..., -186184000/352947) | 4 | S_3 | 0 | Q |
| 8 | (729486255135700992/1838265625, ..., 448159706914816/771895089) | 3 | Z/2 | 1 | Q |
| 9 | (607660606990336/220591875, ..., -3387870464/9529569) | 3 | (Z/2)^2 | 0 | Q |
| 10 | (328783729403804707/5514796875, ..., -281175372827/238239225) | 1 | S_3 | 0 | Q |

**Total:** 63 = 12 + 12 + 12 + 6 + 6 + 4 + 4 + 3 + 3 + 1.

#### Extra Z/3 symmetry (elliptic j-invariant from branch point Z/3-orbit)

Only 9 of 63 complexes have Z/3 orbits, falling into 3 distinct elliptic j min polys.

| Elliptic j min poly | Classes | # complexes | mp(1728) factorization |
|---------------------|---------|-------------|------------------------|
| t - 54000 | 6 | 4 | 2^4 . 3^3 . 11^2  (j = 54000, CM by Z[sqrt(-3)]) |
| t^2 - (775180000/729)t + 40873252000000/6561 | 7 | 4 | 2^8 . 37^2 . 47^2 . 193^2 / 3^8 |
| t^2 - (541157005431/15625)t + 25745806977673041/390625 | 10 | 1 | 3^6 . 37^2 . 83^2 . 587^2 / 5^8 |
| (no Z/3 orbit) | 1–5, 8, 9 | 54 | -- |

The Z/3-bearing complexes are exactly: class 6 (all 4), class 7 (all 4), and class 10
(the unique singleton).  These are the complexes fixed or organized by the Z/3 action
sigma: (x:y:z) -> (y:z:x).

#### Reduced automorphism group (involutions beyond hyperelliptic)

**All 63 complexes have RA ⊇ Z/2.**  The Edge automorphism group S_4 (order 24)
stabilizes each complex with a subgroup of order ≥ 2, inducing extra involutions.

**7 of 63 have RA ⊇ (Z/2)^2**, falling in exactly 2 Igusa classes:

| Igusa class | RA ⊇ | Lambda | Elliptic j (Z/2 quotient) |
|-------------|-------|--------|---------------------------|
| 6 (4 members) | D_6 | lambda = -2 | **j = 54000** |
| 9 (3 members) | (Z/2)^2 | lambda = -2/5 or -5/2 | j = -11664/625 or 3538944/25 |
| 7 (4 members), 10 (1 member) | S_3 | -- | -- |
| 1, 2, 3, 4, 5, 8 | Z/2 | -- | -- |

**Class 6** (all 4 have BOTH Z/3 and (Z/2)^2):
  Complexes 5, 7, 13, 33: all have lambda = -2 and (Z/2)^2 elliptic j = **54000**.
  Z/3 elliptic j = 54000 (CM by sqrt(-3)).
  **The Z/2 and Z/3 quotients give the same elliptic curve** (j = 54000).
  The normal form is {0, 1, -1, -2, -1/2, infinity}.

**Class 9** (all 3 have (Z/2)^2):
  Complexes 23, 52: lambda = -2/5, j = -11664/625.
  Complex 39: lambda = -5/2, j = 3538944/25.

#### Syzygetic triples within Igusa classes

| Class | Size | # syz. triples | Triples |
|-------|------|----------------|---------|
| 1 (12 members) | 12 | 0 | (none) |
| 2 (12 members) | 12 | 0 | (none) |
| 3 (12 members) | 12 | 8 | {3,4,34}, {3,44,61}, {4,45,61}, {17,37,38}, {17,41,56}, {34,44,45}, {37,41,55}, {38,55,56} |
| 4 (6 members) | 6 | 4 | {11,21,58}, {11,35,63}, {21,24,35}, {24,58,63} |
| 5 (6 members) | 6 | 4 | {18,19,62}, {18,22,53}, {19,22,54}, {53,54,62} |
| 6 (4 members) | 4 | 0 | (none) |
| 7 (4 members) | 4 | 0 | (none) |
| 8 (3 members) | 3 | 1 | {12,20,40} |
| 9 (3 members) | 3 | 0 | (none) |
| 10 (1 member) | 1 | 0 | (only 1 element) |

**Observation:** Class 8 has a remarkable property: it has exactly 3 members (complexes
12, 20, 40) and they form a SINGLE collinear triple.  This means all three of these
J[2] elements sum to zero: they are "perfectly collinear."  In fact, {12, 20, 40}
is also a Z/3-orbit under sigma (orbit 7 in the Z/3 action).

**Observation:** Classes 4 and 5 each have 6 members with 4 collinear triples.
Compare with the Fermat: class 4 there also has 6 members with 4 collinear triples.

**Observation:** Class 3 (12 members, 8 triples) has a nice structure.  Inspecting
the triples, every element appears in exactly 2 triples (8 triples x 3 elements / 12
members = 2 per member).  The triples decompose into two groups of 4 that are related
by the Z/3 action: {3,4,34} is a Z/3 orbit, and so is {17,37,38}, {44,61,45}, {55,56,41}.

---

## Cross-curve comparison

### Bitangent splitting fields and fields of definition

| Quartic | Bitangent field K | [K:Q] | # Q-rational bitangents | # Q-rational torsion classes |
|---------|-------------------|-------|-------------------------|------------------------------|
| Klein twist | Q(w), w² + 5w/2 + 2 = 0 | 2 | 0 (all need √-7) | 7 |
| Fermat | Q(w), w⁴ + 1 = 0 | 4 | 0 (all need ζ₈) | 7 |
| Edge | **Q** | **1** | **28 (all)** | **63 (all)** |

The Edge quartic is exceptional: every bitangent line has rational coefficients,
and consequently every Steiner complex (= every nontrivial 2-torsion class) is
Galois-fixed.  For the Klein twist and Fermat, no individual bitangent line is
rational, but 7 out of 63 Steiner complexes are nonetheless Q-rational: a
partition of bitangents into pairs can be Galois-stable even when the individual
lines are not.  For Klein twist, the 7 split as 4 in the size-28 orbit + 3 in the
size-21 orbit.  For Fermat, the 7 split as all 6 in the size-6 orbit + the
unique singleton.

This contrasts with the Edge quartic which has the richest arithmetic structure:
10 distinct Q-rational Igusa classes (vs 4 for Klein twist, 5 for Fermat),
and all Prym Igusa invariants
lie in Q.

### Reduced automorphism group prevalence

**All 63 Pryms have RA ⊇ Z/2 for every quartic studied.**  This is a
consequence of the large automorphism groups of these quartics.

| Quartic | # with (Z/2)^2 | # with Z/2 only | Igusa classes with (Z/2)^2 |
|---------|----------------|-----------------|----------------------------|
| Klein twist | 21 | 42 | 1 of 4 (class 2) |
| Fermat | 7 | 56 | 2 of 5 (classes 4, 5) |
| Edge | 7 | 56 | 2 of 10 (classes 6, 9) |

The Klein twist has the most (Z/2)^2 symmetry (33% vs 11%).

### Z/3 vs (Z/2)^2 complementarity

A striking pattern across all three quartics: **Z/3 and (Z/2)^2 are nearly complementary.**

- **Klein twist:** Classes 1, 3, 4 have RA ⊇ S_3 (Z/3 but not (Z/2)^2).  Class 2
  (21 members) has RA ⊇ (Z/2)^2 but no Z/3.
- **Fermat:** Classes 2, 3 have RA ⊇ S_3 (Z/3 but not (Z/2)^2).  Class 4 has
  RA ⊇ (Z/2)^2 but no Z/3.  Class 5 (the unique singleton) has RA = S_4.
- **Edge:** Class 9 has RA ⊇ (Z/2)^2 but no Z/3.  Classes 7, 10 have RA ⊇ S_3
  (Z/3 but not (Z/2)^2).  Only class 6 (j = 54000, CM by sqrt(-3)) has RA ⊇ D_6.

The complexes with both (Z/2)^2 and Z/3 are always the most "special" Pryms: the CM
curves (j = 54000 for Edge, j = 8000 for Fermat).

### Isogeny of (Z/2)^2 quotient elliptic curves

For each (Z/2)^2 class, the Jacobian decomposes J ~ E_1 × E_2:

| Quartic | Class | E_1, E_2 j-invariants | Isogenous? |
|---------|-------|-----------------------|------------|
| Klein twist | 2 | roots of t^2+7184t+16777216 (in Q(√-7)) | **twist-isogenous** |
| Fermat | 4 | j=128, j=128 | trivially yes |
| Fermat | 5 | j=8000, j=8000 | trivially yes |
| Edge | 6 | j=54000, j=54000 | trivially yes |
| Edge | 9 | j=-11664/625, j=3538944/25 | **2-isogenous over Q(√969)** |

### Syzygetic triple density

| Quartic | Class | Size n | # triples | Density = #triples / C(n,3) |
|---------|-------|--------|-----------|----------------------------|
| Klein twist | 1 | 28 | 56 | 1.7% |
| Klein twist | 2 | 21 | 28 | 2.1% |
| Klein twist | 3 | 7 | 7 | 20% |
| Klein twist | 4 | 7 | 7 | 20% |
| Fermat | 1 | 24 | 64 | 3.2% |
| Fermat | 2 | 16 | 0 | 0% |
| Fermat | 3 | 16 | 0 | 0% |
| Fermat | 4 | 6 | 4 | 20% |
| Edge | 3 | 12 | 8 | 3.6% |
| Edge | 4 | 6 | 4 | 20% |
| Edge | 5 | 6 | 4 | 20% |
| Edge | 8 | 3 | 1 | 33% |

The density 20% = 1/5 appears repeatedly (Klein twist classes 3, 4; Fermat class 4;
Edge classes 4, 5).  The 6-element classes consistently yield exactly 4 collinear
triples = C(6,3)/5.  For 3-element classes, the maximum 1 triple = C(3,3) = 100%
if collinear (Edge class 8).

---

## Notes

- Genus-2 curves are computed mod p (p = 29 for Klein twist and Edge, p = 41 for Fermat)
  and identified up to geometric isomorphism via absolute Igusa invariants over the
  bitangent splitting field K.
- Z/3 elliptic j-invariants (from branch point Z/3-orbits) are detailed in the
  per-quartic subsections rather than the main tables.  When a Z/3 orbit exists,
  the genus-2 Jacobian has an elliptic factor whose j-invariant is recorded there.
- The "RA ⊇" column records a lower bound on the reduced automorphism group
  RA(C_g2) = Aut(C_g2)/<hyp. inv.>.  The possible values of RA for genus-2
  curves are: trivial, Z/2, (Z/2)^2, S_3, D_6, S_4, Z/5.  In our tables:
  "Z/2" means some Mobius involution permutes the 6 branch points;
  "(Z/2)^2" means branch points in the form {0, 1, -1, λ, 1/λ, ∞};
  "S_3" means Z/3 orbit on branch points (which forces a companion involution);
  "D_6" means both Z/3 and (Z/2)^2 are present.
- "Count" = number of Steiner complexes (out of 63) giving that isomorphism class.
- "Coll. triples" = number of unordered triples {x,y,z} of J[2] elements within
  that class satisfying x + y + z = 0 in F_2^6.
- All three quartics have Z/3 symmetry sigma: (x:y:z) -> (y:z:x), giving 23 orbits
  on the 63 complexes (three fixed points + twenty size-3 orbits).  The Fermat and
  Edge quartics additionally have sign-change automorphisms (all monomials even),
  giving S_3 x (Z/2)^2 = S_4 (order 24) as a subgroup of Aut(C).  For the Edge
  quartic, Aut(C) = S_4 and the 10 S_4-orbits on J[2]\{0} exactly coincide with
  the 10 Igusa invariant classes.
- The Edge quartic class 4 analysis confirms that **the Fermat Prym with Igusa
  invariants (8388608, 245760, 4096) has Aut = D_4 (order 8)** and Jacobian
  isogenous to E^2 where E = 128a1 (y^2 = x^3+x^2+x+1, j = 128, non-CM).
  The model is y^2 = (x^2+1)(x^4+1).
