# Pryms of étale double covers — invariants

This document records the invariants of the genus-2 Pryms arising from the
63 étale double covers of three smooth plane quartics over Q:

| Curve | Defining quartic |
|---|---|
| **Klein twist (C_twist)** | `x⁴ + y⁴ + z⁴ + 6(xy³ + yz³ + zx³) − 3(x²y² + y²z² + z²x²) + 3xyz(x+y+z)` |
| **Fermat** | `x⁴ + y⁴ + z⁴` |
| **Edge (S₄-symmetric)** | `25(x⁴ + y⁴ + z⁴) − 34(x²y² + y²z² + x²z²)` |

For each smooth plane quartic *C*, every non-zero `η ∈ J(C)[2]` determines a
Steiner complex (six pairs of bitangents) and an étale double cover
*Dη → C*. The Prym of *Dη → C* is a (principally polarized) abelian surface
which, in this construction, is realized as the Jacobian of an explicit
genus-2 curve `y² = −det(Q1 + 2t·Q2 + t²·Q3)` built from a
quadric‐pencil decomposition of *F*. This file lists those genus-2
invariants for all 63 complexes of all three curves.

The data was produced by `steiner_pipeline.m` (driver `tests.m`); raw
per-complex output lives in `results/{klein_twist,fermat,edge}.log`.

## Notation
- `(j₁, j₂, j₃)` — the absolute Igusa invariants of the genus-2 Prym (Cardona / Quer normalisation, Magma `AbsoluteIgusaInvariants`).
- `mp_E` — the minimal polynomial over Q of the j-invariant of the elliptic factor obtained from a Z/3-orbit on the six Weierstrass points (when one exists).
- `K` — the splitting field over Q of the bitangent coordinates of the quartic.
- σ — the cyclic order-3 symmetry `(x:y:z) ↦ (y:z:x)` of each of the three curves.
- `RA` — the reduced automorphism group `Aut(C_g2)/⟨hyp. inv.⟩`, acting faithfully on P¹ via Möbius transformations permuting the 6 branch points. Possible values for genus-2: trivial, Z/2, (Z/2)², S₃, D₆, S₄, Z/5. In our tables: "Z/2" = some Möbius involution permutes the 6 branch points; "(Z/2)²" = branch points in the form {0, 1, −1, λ, 1/λ, ∞}; "S₃" = Z/3 orbit on branch points (which forces a companion involution); "D₆" = both Z/3 and (Z/2)² present.

---

## 1. Klein twist (C_twist)

**Splitting field of bitangents:** `K = Q(w)` with `w² + (5/2) w + 2 = 0`,
i.e. `K = Q(√−7)`. (Discriminant `25 − 32 = −7`.)

**Distinct geometric Igusa classes (4 over K):**

| # | `(j₁, j₂, j₃)` | mult | RA ⊇ | coll. triples | orbit field | complexes |
|---|---|---|---|---|---|---|
| 1 | `(2048, −192, 64)` | 28 | S₃ | 56 | Q | 3, 4, 7, 9, 10, 13, 18, 20, 24, 25, 26, 27, 29, 34, 35, 37, 38, 39, 40, 45, 48, 49, 51, 52, 53, 57, 59, 63 |
| 2 | `(2048/343, 4416/343, −2816/343)` | 21 | (Z/2)² | 28 | Q | 1, 2, 5, 8, 11, 15, 17, 21, 22, 28, 30, 32, 43, 46, 47, 55, 56, 58, 60, 61, 62 |
| 3 | `(1/343)·(−76740102 w − 95211256, −3674430 w − 3245592, 39906 w − 728)` | 7 | S₃ | 7 | Q(√−7) | 6, 16, 19, 23, 33, 41, 42 |
| 4 | `(1/343)·(76740102 w + 96638999, 3674430 w + 5940483, −39906 w − 100493)` | 7 | S₃ | 7 | Q(√−7) | 12, 14, 31, 36, 44, 50, 54 |

Classes 3 and 4 are Galois‐conjugate over `K = Q(√−7)`; they are the two
size-7 PSL(2,7)-orbits. Class 1 is the size-28 (bitangent) orbit; class 2 is
the size-21 orbit.

**Elliptic j-invariants from Z/3 cross-ratios (2 distinct over Q):**

| `mp_E` over Q | mult | factorization of `mp_E(1728)` | complexes |
|---|---|---|---|
| `t² + 13856·t − 26578688` | 28 | `2⁸ · 37²` | the entire size-28 orbit (class 1) |
| `t⁴ − 103439·t³ + 6670405329·t² + 31128229267744·t + 148381159092130048` | 14 | `2⁸ · 11⁶ · 23² · 31⁴` | the union of the two size-7 orbits (classes 3 + 4) |

The size-21 orbit (class 2) admits **no Z/3 orbit** on the corresponding

Weierstrass set, so no elliptic j-invariant is produced for those 21 complexes.

The first polynomial splits over Q(√7) into `j = −6928 ± 3264·√7`. The second
is irreducible over Q but splits over Q(√−7) into two conjugate quadratics
(call them `mp₂·mp₃`); the field of definition of any one root is the
quartic field 4.0.1372.1.

**Z/3 action on the 63 complexes:** 23 orbits — 3 fixed (`#7`, `#14`, `#19`) and 20 of size 3.

These results match those previously recorded in `check_isogeny*.m` and the
older `steiner.m` script. Both elliptic factors are non-CM (Lang–Trotter
supersingular density up to 10⁶), pairwise non-isogenous over Q̄ (CM-field
criterion), and distinct from the curve `E = 49a1` that arises from
`J(C_twist) ≅ E³`.

**Reduced automorphism groups:**

All 63 complexes have RA ⊇ Z/2 (PSL(2,7) stabilizes each complex with a
subgroup of order ≥ 6). **21 of 63 have RA ⊇ (Z/2)²**, all in class 2.
The lambda minimal polynomial for class 2 takes two conjugate forms, both
yielding the same elliptic j min poly `t² + 7184t + 16777216` (discriminant
`−2⁸·3²·7·31²`, roots in Q(√−7)). The two Z/2-quotient elliptic curves
are **twist-isogenous** (a_p agree up to sign at all primes, ~50/50 split).

Classes 1, 3, 4 have RA ⊇ S₃ (Z/3 orbit present) but not (Z/2)².

**Collinear triples within Igusa classes:**

| Class | Size | # triples | Density |
|-------|------|-----------|---------|
| 1 | 28 | 56 | 1.7% |
| 2 | 21 | 28 | 2.1% |
| 3 | 7 | 7 | 20% |
| 4 | 7 | 7 | 20% |

Classes 3 and 4 each achieve the density 1/5 = C(7,3)/5·C(7,3)⁻¹: every
fifth triple from these 7-element sets is collinear.

---

## 2. Fermat quartic

**Splitting field of bitangents:** `K = Q(w)` with `w⁴ + 1 = 0`, i.e.
`K = Q(ζ₈) = Q(i, √2)`, the 8th cyclotomic field.

**Distinct geometric Igusa classes (5 over K):**

| # | `(j₁, j₂, j₃)` | mult | RA ⊇ | coll. triples | orbit field | complexes |
|---|---|---|---|---|---|---|
| 1 | `(131072, 6144, −512)` | 24 | Z/2 | 64 | Q | 5, 6, 9, 10, 13, 14, 15, 16, 21, 22, 25, 26, 29, 30, 39, 41, 44, 45, 47, 49, 50, 51, 60, 61 |
| 2 | `(−224208(w³−w) + 344408, −7830(w³−w) + 11121, ½(378(w³−w) − 7))` | 16 | S₃ | 0 | Q(√2) | 1, 7, 11, 18, 20, 23, 28, 32, 35, 36, 43, 48, 52, 55, 58, 59 |
| 3 | `(224208(w³−w) + 344408, 7830(w³−w) + 11121, ½(−378(w³−w) − 7))` | 16 | S₃ | 0 | Q(√2) | 2, 8, 12, 17, 19, 24, 27, 31, 33, 37, 42, 46, 53, 54, 56, 57 |
| 4 | `(8388608, 245760, 4096)` | 6 | (Z/2)² | 4 | Q | 3, 4, 38, 40, 62, 63 |
| 5 | `(50000, 3750, −125)` | **1** | S₄ | 0 | Q | 34 |

Classes 2 and 3 are Galois conjugate over Q. The algebraic part
`w³ − w` satisfies `(w³ − w)² = w⁶ − 2w⁴ + w² = −w² + 2 + w² = 2`, so
`w³ − w = √2` and each Igusa triple is defined over the index-2 subfield
`Q(√2) ⊂ K = Q(ζ₈)`. The pair (2, 3) is a Galois orbit under the unique
non-trivial automorphism of Q(√2)/Q (`√2 ↦ −√2`).

**Class 5 is exceptional:** the only Q-rational Igusa point. It is exactly
the "diagonal" Steiner complex `{1,4}{2,3}{9,20}{14,15}{25,28}{26,27}` (with
the bitangent indices used in the Fermat log) and corresponds to the unique
σ-fixed orbit that produces a Q-rational elliptic j-invariant.

**Elliptic j-invariants from Z/3 cross-ratios (2 distinct over Q):**

| `mp_E` over Q | mult | `mp_E(1728)` factorization | complexes |
|---|---|---|---|
| `t − 8000` | **1** | `−2⁷ · 7²` | 34 |
| `t⁴ + 73216·t³ + 1533640704·t² + 6119514701824·t − 15081210455785472` | 32 | `2²⁴ · 5233²` | 1, 2, 7, 8, 11, 12, 17, 18, 19, 20, 23, 24, 27, 28, 31, 32, 33, 35, 36, 37, 42, 43, 46, 48, 52, 53, 54, 55, 56, 57, 58, 59 |

The first is the (linear) minimal polynomial `t − 8000`, so `j = 8000`. This
is the **CM j-invariant for the order Z[√−2]** (class number 1, discriminant
−8). It is exactly the elliptic factor at the unique Q-rational Igusa point
(complex #34).

The remaining 30 complexes (out of 63) admit **no** Z/3 orbit on their Weierstrass
sets and so produce no elliptic j-invariant by this construction.

**Z/3 action on the 63 complexes:** 23 orbits — 3 fixed (`#23`, `#24`, `#34`) and 20 of size 3.

**Reduced automorphism groups:**

All 63 complexes have RA ⊇ Z/2. **7 of 63 have RA ⊇ (Z/2)²**, in two classes:

| Class | RA ⊇ | λ min poly | j (Z/2 quotient) | complexes |
|-------|-------|-----------|------------------|-----------|
| 5 | S₄ | `t² + 1` | j = 8000 | 34 |
| 4 | (Z/2)² | `t² − 1/2` | j = 128 | 3, 4, 38, 40, 62, 63 |

**Class 5 (#34)** has RA = S₄: the branch points {0, 1, −1, i, −i, ∞}
admit the full symmetric group of Möbius transformations permuting them.
The Z/2 and Z/3 quotients give the **same** elliptic curve (j = 8000,
CM by Z[√−2]).

**Class 4** has full Aut = D₄ (order 8), J ~ E² with E: j = 128,
Cremona label `128a1` (`y² = x³ + x² + x + 1`, non-CM). The genus-2
model is `y² = (x² + 1)(x⁴ + 1)`. The Aut = D₄ identification is
independently confirmed by the Edge quartic computation (where all
bitangents are rational and the full automorphism group is visible).

**Collinear triples within Igusa classes:**

| Class | Size | # triples | Density |
|-------|------|-----------|---------|
| 1 | 24 | 64 | 3.2% |
| 2 | 16 | 0 | 0% |
| 3 | 16 | 0 | 0% |
| 4 | 6 | 4 | 20% |
| 5 | 1 | 0 | — |

The two Galois-conjugate 16-element classes have **zero** collinear triples
(out of C(16,3) = 560 possible), strongly constraining how these 16 elements
sit inside F₂⁶.

---

## 3. Edge quartic

**Splitting field of bitangents:** `K = Q`. All 28 bitangents have rational
coefficients, so every Igusa invariant and every elliptic j-invariant is
already rational. This makes the Edge case the most arithmetically rich.

**Aut(C):** `S₄` (order 24). Generated by coordinate permutations `S₃` and
sign changes `(x:y:z) ↦ (−x:y:z)`, `(x:−y:z)` (possible because all
monomials have even degree in each variable): `S₃ × (Z/2)² / ⟨overall sign⟩ = S₄`.

**S₄-orbits on J[2]\{0}:** 10 orbits, sizes `{1, 3, 3, 4, 4, 6, 6, 12, 12, 12}`,
**exactly matching the 10 Igusa invariant classes.**

**Distinct geometric Igusa classes (10, all over Q):**

| # | `(j₁, j₂, j₃)` | mult | RA ⊇ | coll. triples | orbit field | complexes |
|---|---|---|---|---|---|---|
| 1 | `(1729733224448/151875, 1496258752/5625, −1425053696/4100625)` | 12 | Z/2 | 0 | Q | 1, 2, 6, 9, 14, 26, 30, 31, 32, 42, 50, 57 |
| 2 | `(31172342123300864/5955980625, 804859942779712/5955980625, 68168000576/73530625)` | 12 | Z/2 | 0 | Q | 8, 10, 15, 25, 27, 28, 29, 36, 46, 47, 48, 51 |
| 3 | `(800000000/81, 23560000/81, 40000/9)` | 12 | Z/2 | 8 | Q | 3, 4, 17, 34, 37, 38, 41, 44, 45, 55, 56, 61 |
| 4 | `(68934134667875/28588707, 1519104335495/28588707, −316737676475/771895089)` | 6 | Z/2 | 4 | Q | 11, 21, 24, 35, 58, 63 |
| 5 | `(1429519218944000/28588707, 43597764450880/28588707, 33694083654400/771895089)` | 6 | Z/2 | 4 | Q | 18, 19, 22, 53, 54, 62 |
| 6 | `(6400000/3, 440000/9, −32000/81)` | 4 | D₆ | 0 | Q | 5, 7, 13, 33 |
| 7 | `(443801324800000/85766121, 281630680000/3176523, −186184000/352947)` | 4 | S₃ | 0 | Q | 16, 43, 49, 59 |
| 8 | `(729486255135700992/1838265625, 2177158706811833536/148899515625, 448159706914816/771895089)` | 3 | Z/2 | 1 | Q | 12, 20, 40 |
| 9 | `(607660606990336/220591875, 43805907748544/661775625, −3387870464/9529569)` | 3 | (Z/2)² | 0 | Q | 23, 39, 52 |
| 10 | `(328783729403804707/5514796875, 301399492750133/661775625, −281175372827/238239225)` | **1** | S₃ | 0 | Q | **60** |

Classes 1–3 (mult 12) come together to give 36 complexes. Classes 4 and 5
(mult 6) are smaller orbits under the automorphism action. Classes 6–9 are
small. **Class 10 is the unique singleton**, residing entirely on the
exceptional complex #60.

**Elliptic j-invariants from Z/3 cross-ratios (3 distinct over Q):**

| `mp_E` over Q | mult | `mp_E(1728)` (factored) | complexes |
|---|---|---|---|
| `t − 54000` | 4 | `−2⁴ · 3³ · 11²` | 5, 7, 13, 33 |
| `t² − (775180000/729)·t + (40873252000000/6561)` | 4 | `2⁸ · 37² · 47² · 193² / 3⁸` | 16, 43, 49, 59 |
| `t² − (541157005431/15625)·t + (25745806977673041/390625)` | **1** | `3⁶ · 37² · 83² · 587² / 5⁸` | **60** |

The first is the linear polynomial `t − 54000`, so `j = 54000`. This is the
**CM j-invariant for the order Z[√−3]** (class number 1, discriminant −12).
It coincides with class 6 (Igusa class with multiplicity 4) on the same
4 complexes `{5, 7, 13, 33}`.

The remaining 54 complexes admit no Z/3 orbit on their Weierstrass set.

**Z/3 action on the 63 complexes:** 23 orbits — 3 fixed (`#33`, `#59`, `#60`) and 20 of size 3.

**Striking observation:** the three Z/3-fixed complexes `{33, 59, 60}` are
*exactly* the three complexes that carry a non-trivial elliptic j-invariant
of the third type (the singleton class 10) or that lie inside the four
complexes of the other two types — in fact every Z/3-fixed Edge complex
falls into one of the three "elliptic" classes:

- `#33` is in the size-4 CM class with `j = 54000`
- `#59` is in the size-4 class with the second quadratic min poly
- `#60` is the unique singleton with the third (quadratic) min poly

**Reduced automorphism groups:**

All 63 complexes have RA ⊇ Z/2. **7 of 63 have RA ⊇ (Z/2)²**, in two classes:

| Class | RA ⊇ | λ | j (Z/2 quotient) | complexes |
|-------|-------|---|------------------|-----------|
| 6 | D₆ | λ = −2 | j = 54000 | 5, 7, 13, 33 |
| 9 | (Z/2)² | λ = −2/5 or −5/2 | j = −11664/625 or 3538944/25 | 23, 39, 52 |

**Class 6** has BOTH Z/3 and (Z/2)²: the Z/2 and Z/3 quotients give the
**same** elliptic curve (j = 54000, CM by Z[√−3]). Branch points:
{0, 1, −1, −2, −1/2, ∞}.

**Class 9:** complexes 23, 52 have λ = −2/5 (j = −11664/625); complex 39 has
λ = −5/2 (j = 3538944/25). The two quotient elliptic curves are
**2-isogenous over Q(√969)** where 969 = 3·17·19. Specifically:
E₁(j=−11664/625) →[2-isogeny/Q]→ E₁' →[twist by 51/19]→ E₂(j=3538944/25).
The twist factor 51/19 = (3·17)/19 has squarefree kernel 3·17·19; note 17
and 19 are exactly the primes distinguishing the conductors (2⁴·3²·5·7²·19²
vs 2⁴·3²·5·7²·17²). The j-formula j(t) = 256(t⁴+t²+1)³/(t⁴(t²+1)²) with
t = λ+√(λ²−1) gives the SAME j for both ± branches, so each λ value
produces only one of the two elliptic quotients.

**Collinear triples within Igusa classes:**

| Class | Size | # triples | Density |
|-------|------|-----------|---------|
| 1 | 12 | 0 | 0% |
| 2 | 12 | 0 | 0% |
| 3 | 12 | 8 | 3.6% |
| 4 | 6 | 4 | 20% |
| 5 | 6 | 4 | 20% |
| 6 | 4 | 0 | 0% |
| 7 | 4 | 0 | 0% |
| 8 | 3 | 1 | 33% |
| 9 | 3 | 0 | 0% |
| 10 | 1 | 0 | — |

Class 8 is "perfectly collinear": its 3 members {12, 20, 40} form a single
collinear triple (all three sum to zero in J[2]). This set is also a Z/3-orbit
under σ.

Class 3 (12 members, 8 triples) has a nice structure: every element appears
in exactly 2 triples (8 × 3 / 12 = 2). The triples decompose into two
groups of 4 related by the Z/3 action: {3,4,34} is a Z/3-orbit, as are
{17,37,38}, {44,45,61}, {55,56,41}.

---

## Cross-curve summary

| Curve | K | # Igusa classes | # elliptic j min polys (Q) | smallest non-trivial class | CM ?|
|---|---|---|---|---|---|
| Klein twist | Q(√−7) | 4 | 2 | 7 (twin orbits) | non-CM |
| Fermat | Q(ζ₈) | 5 | 2 | 1 (#34) | **j = 8000** (Z[√−2]) at #34 |
| Edge | Q | 10 | 3 | 1 (#60) | **j = 54000** (Z[√−3]) at 4 cpx, plus exceptional #60 |

In all three cases the Z/3 action produces exactly **23 orbits** on the 63
Steiner complexes, with 3 fixed points, but the fixed points organise the
elliptic data quite differently between Fermat (one Q-rational j) and Edge
(three distinct j-invariant min polys, one of them singleton).

### Bitangent splitting fields

| Quartic | Bitangent field K | [K:Q] | # Q-rational bitangents | # Q-rational torsion classes |
|---------|-------------------|-------|-------------------------|------------------------------|
| Klein twist | Q(√−7) | 2 | 0 | 7 |
| Fermat | Q(ζ₈) | 4 | 0 | 7 |
| **Edge** | **Q** | **1** | **28 (all)** | **63 (all)** |

The Edge quartic has all 63 2-torsion classes Q-rational. For the Klein
twist and Fermat, 7 out of 63 classes are Q-rational despite no bitangent
line being rational: a Steiner complex (set of 6 bitangent pairs) can be
Galois-stable as a partition even when individual lines are not. In both
cases the 7 Q-rational classes split across the Q-defined orbits (4 in the
size-28 orbit and 3 in the size-21 orbit for Klein twist; 6 in the size-6
orbit and 1 in the singleton for Fermat). This explains why Edge has the
richest arithmetic structure: 10
distinct Q-rational Igusa classes vs 4 (Klein twist) and 5 (Fermat).

### Reduced automorphism group prevalence

All 63 Pryms have RA ⊇ Z/2 for every quartic studied. This is a consequence
of the large automorphism groups of these quartics.

| Quartic | # with (Z/2)² | # with Z/2 only | Igusa classes with (Z/2)² |
|---------|----------------|-----------------|----------------------------|
| Klein twist | 21 | 42 | 1 of 4 (class 2) |
| Fermat | 7 | 56 | 2 of 5 (classes 4, 5) |
| Edge | 7 | 56 | 2 of 10 (classes 6, 9) |

The Klein twist has the most (Z/2)² symmetry (33% vs 11%).

### Z/3 vs (Z/2)² complementarity

A striking pattern across all three quartics: **Z/3 and (Z/2)² are nearly
complementary.**

- **Klein twist:** Classes 1, 3, 4 have RA ⊇ S₃ (Z/3 but not (Z/2)²).
  Class 2 (21 members) has RA ⊇ (Z/2)² but no Z/3.
- **Fermat:** Classes 2, 3 have RA ⊇ S₃ (Z/3 but not (Z/2)²). Class 4 has
  RA ⊇ (Z/2)² but no Z/3. Class 5 (the unique singleton) has RA = S₄.
- **Edge:** Class 9 has RA ⊇ (Z/2)² but no Z/3. Classes 7, 10 have RA ⊇ S₃
  (Z/3 but not (Z/2)²). Only class 6 (j = 54000, CM by √−3) has RA ⊇ D₆.

The complexes with both (Z/2)² and Z/3 are always the most "special" Pryms:
the CM curves (j = 54000 for Edge, j = 8000 for Fermat).

### Isogeny of (Z/2)² quotient elliptic curves

For each (Z/2)² class, the Jacobian decomposes J ~ E₁ × E₂:

| Quartic | Class | E₁, E₂ j-invariants | Isogenous? |
|---------|-------|-----------------------|------------|
| Klein twist | 2 | roots of `t² + 7184t + 16777216` (in Q(√−7)) | **twist-isogenous** |
| Fermat | 5 | j = 8000, j = 8000 | trivially yes |
| Fermat | 4 | j = 128, j = 128 | trivially yes |
| Edge | 6 | j = 54000, j = 54000 | trivially yes |
| Edge | 9 | j = −11664/625, j = 3538944/25 | **2-isogenous over Q(√969)** |

### Collinear triple density

The density 1/5 appears repeatedly across curves and class sizes.

| Quartic | Class | Size n | # triples | Density |
|---------|-------|--------|-----------|---------|
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

The 6-element classes consistently yield exactly 4 collinear triples =
C(6,3)/5. For 3-element classes, the maximum 1 triple = C(3,3) = 100% if
collinear (Edge class 8).

---

## H¹(C, F₂) = J(C)[2] as an F₂[Aut(C)]-module

For each curve we compute the geometric automorphism group `Aut(C_Q̄)` (by
working over a finite field F_q where the full geometric Aut and all 28
bitangents are F_q-rational), build the induced action of `Aut(C)` on
`J(C)[2] ≅ F₂⁶ = H¹(C, F₂)` via its action on bitangent half-divisors,
and decompose the resulting F₂[Aut(C)]-module.

Computed by `aut_j2_modules.m` (raw output: `results/aut_j2_modules.log`).

### Klein twist — Aut = PSL(2,7), order 168 (computed over F₂₉)

| | |
|---|---|
| **Composition factors** | `3 ⊕ 3` (two distinct absolutely irreducible 3-dim reps) |
| **Indecomposable summands** | two 3-dim irreducibles |
| **Semisimple?** | **Yes** |

`H¹(C_twist, F₂) ≅ V ⊕ V*` as F₂[PSL(2,7)]-modules, where `V` is the natural
3-dim representation of `PSL(2,7) ≅ GL(3, F₂)` and `V*` is its dual. The two
3-dim irreducibles are non-isomorphic (in characteristic 2 they are the only
non-trivial irreducibles of `GL(3,2)` of dimension < 8). The Weil pairing on
J[2] is the perfect duality `V × V* → F₂` underlying this decomposition.
This is the canonical Klein-quartic identification of `J[2]` with `V ⊕ V*`.

### Fermat — Aut = (Z/4)² ⋊ S₃, order 96 (computed over F₄₁)

| | |
|---|---|
| **Composition factors** | dimensions `1, 2, 2, 1` (4 factors total, all absolutely irreducible) |
| **Indecomposable summands** | a single uniserial 6-dim summand with composition series `1, 2, 2, 1` |
| **Semisimple?** | **No** |

`H¹(Fermat, F₂)` is **indecomposable** as an F₂[Aut]-module: the entire 6-dim
space sits in a single non-split tower with composition factors of dimensions
1, 2, 2, 1. Magma identifies the group as `C4²:C3:C2 = (Z/4)² ⋊ S₃`. The
failure of semisimplicity is consistent with `2 | |Aut(Fermat)| = 96`.

### Edge — Aut = S₄, order 24 (computed over F₁₉)

| | |
|---|---|
| **Composition factors** | dimensions `1, 2, 1, 2` (4 factors total, all absolutely irreducible) |
| **Indecomposable summands** | two non-split 3-dim summands, each with composition factors `1, 2` |
| **Semisimple?** | **No** |

`H¹(Edge, F₂)` decomposes as a direct sum of **two** indecomposable 3-dim
F₂[S₄]-modules with opposite extension directions:
`0 → trivial → V₁ → irred(2) → 0` and `0 → irred(2) → V₂ → trivial → 0`.
The two `irred(2)` factors are isomorphic: the unique 2-dim simple
F₂[S₄]-module, inflated from `S₃ = GL(2, F₂)` via `S₄ → S₄/V₄ ≅ S₃`.
Restriction to the `S₃` subgroup is **semisimple**: `trivial ⊕ trivial ⊕ irred(2) ⊕ irred(2)`.

### Cross-curve summary

| Curve | Aut(C_Q̄) | order | irreducibles in J[2] | semisimple? |
|---|---|---|---|---|
| Klein twist | `PSL(2,7)` | 168 | `V ⊕ V*` (two 3-dim) | **yes** |
| Fermat | `(Z/4)² ⋊ S₃` | 96 | uniserial `1 ⊂ 2 ⊂ 2 ⊂ 1` (single indec.) | no |
| Edge | `S₄` | 24 | two 3-dim indecs, each `1 ⊂ 2` | no |

Only Klein twist gives a semisimple J[2] — and there it is forced because
`gcd(|PSL(2,7)|, 2) = 2` divides only "minimally" in the sense that the
representation theory of `GL(3, F₂)` over F₂ happens to make the two natural
3-dim modules projective (and hence injective) inside `J[2]`. For Fermat
and Edge, the larger 2-Sylow content of `Aut(C)` produces genuine non-split
extensions in J[2].

---

## Jacobian decompositions

For each quartic C, the Jacobian J(C) is isogenous over Q to E³ for an
elliptic curve E. The identification is made by factoring the L-polynomial
of C mod p at small primes and matching the degree-2 factors against known
elliptic curves.

| Curve | E | Cremona label | j(E) | Conductor | CM? | Match type |
|---|---|---|---|---|---|---|
| Klein twist | 49a1 | `49a1` | −3375 | 49 | Z[(1+√−7)/2] (disc −7) | exact |
| Fermat | twist of 32a | `32a1` or `32a2` | 1728 | 32 | Z[i] (disc −4) | twist |
| Edge | twist of 15a1 | `15a1` | 111284641/50625 | 15 | **non-CM** | twist |

**Edge details:** Bad reduction at p = 5 and p = 7. The Cremona search
(conductors 1–1000) found `15a1` as a twist match: `a_p(J) = ±a_p(15a1)`
at all good primes. Only 16 supersingular primes up to 10000
(`{7, 23, 31, 79, 167, 431, 479, 983, 1303, 1607, 1871, 2351, 4799, 6263, 6271, 9551}`),
consistent with non-CM density.

**a_p data for Edge (first 21 good primes):**
`{(11,−4), (13,−2), (17,−2), (19,4), (23,0), (29,−2), (31,0), (37,10), (41,−10), (43,−4), (47,−8), (53,−10), (59,4), (61,−2), (67,−12), (71,−8), (73,10), (79,0), (83,−12), (89,6), (97,2)}`

Computed by `ss_jacobian.m` (Phase 1) and `ss_jacobian_phase2.m`;
results in `results/ss_jacobian.log`.

## Reproducing
```
$ cd Klein_quartic/two_torsion
$ magma -b tests.m            # genus-2 Pryms / Igusa / elliptic j data
$ magma -b aut_j2_modules.m   # F₂[Aut(C)]-module structure of J(C)[2]
$ magma -b ss_jacobian.m      # Jacobian L-poly factorization and ss primes
```
This refreshes `results/SUMMARY.txt`, `results/{klein_twist,fermat,edge}.log`,
`results/aut_j2_modules.log`, and `results/ss_jacobian.log`.

---

## Appendix: explicit collinear triples

All unordered triples {x, y, z} of complex indices within each Igusa class
satisfying x + y + z = 0 in J[2] ≅ F₂⁶.

### Klein twist

**Class 1** (28 elements, 56 triples):
{3,4,34}, {3,10,13}, {3,20,35}, {3,25,49}, {3,38,63}, {3,52,57}, {4,9,13}, {4,20,37}, {4,26,49}, {4,40,63}, {4,53,57}, {7,9,37}, {7,10,35}, {7,13,20}, {7,18,29}, {7,27,45}, {7,39,59}, {9,10,34}, {9,26,39}, {9,27,53}, {9,29,40}, {10,25,39}, {10,27,52}, {10,29,38}, {13,27,57}, {13,29,63}, {13,39,49}, {18,20,63}, {18,24,45}, {18,35,38}, {18,37,40}, {18,51,59}, {20,45,57}, {20,49,59}, {24,27,29}, {24,38,52}, {24,40,53}, {24,48,51}, {24,57,63}, {25,26,34}, {25,35,59}, {25,38,51}, {25,48,52}, {26,37,59}, {26,40,51}, {26,48,53}, {27,39,48}, {29,39,51}, {34,35,37}, {34,38,40}, {34,52,53}, {35,45,52}, {37,45,53}, {45,48,59}, {48,49,57}, {49,51,63}

**Class 2** (21 elements, 28 triples):
{1,11,30}, {1,22,58}, {1,28,60}, {1,47,55}, {2,5,17}, {2,15,56}, {2,21,58}, {2,28,61}, {5,8,11}, {5,32,56}, {5,47,61}, {8,22,32}, {8,43,61}, {8,46,62}, {11,22,56}, {11,43,47}, {15,17,32}, {15,21,30}, {15,46,55}, {17,28,47}, {17,55,60}, {21,43,46}, {21,61,62}, {22,60,62}, {28,58,62}, {30,43,55}, {30,56,58}, {32,46,60}

**Class 3** (7 elements, 7 triples):
{6,16,41}, {6,19,33}, {6,23,42}, {16,19,42}, {16,23,33}, {19,23,41}, {33,41,42}

**Class 4** (7 elements, 7 triples):
{12,14,36}, {12,31,50}, {12,44,54}, {14,31,54}, {14,44,50}, {31,36,44}, {36,50,54}

### Fermat

**Class 1** (24 elements, 64 triples):
{5,15,41}, {5,16,39}, {5,21,51}, {5,22,50}, {5,25,45}, {5,26,44}, {5,47,61}, {5,49,60}, {6,15,39}, {6,16,41}, {6,21,50}, {6,22,51}, {6,25,44}, {6,26,45}, {6,47,60}, {6,49,61}, {9,15,45}, {9,16,44}, {9,21,49}, {9,22,47}, {9,25,41}, {9,26,39}, {9,50,61}, {9,51,60}, {10,15,44}, {10,16,45}, {10,21,47}, {10,22,49}, {10,25,39}, {10,26,41}, {10,50,60}, {10,51,61}, {13,15,61}, {13,16,60}, {13,21,26}, {13,22,25}, {13,39,49}, {13,41,47}, {13,44,51}, {13,45,50}, {14,15,60}, {14,16,61}, {14,21,25}, {14,22,26}, {14,39,47}, {14,41,49}, {14,44,50}, {14,45,51}, {15,21,30}, {15,22,29}, {16,21,29}, {16,22,30}, {25,29,61}, {25,30,60}, {26,29,60}, {26,30,61}, {29,39,51}, {29,41,50}, {29,44,49}, {29,45,47}, {30,39,50}, {30,41,51}, {30,44,47}, {30,45,49}

**Classes 2, 3** (16 elements each, 0 triples each).

**Class 4** (6 elements, 4 triples):
{3,38,63}, {3,40,62}, {4,38,62}, {4,40,63}

### Edge

**Class 3** (12 elements, 8 triples):
{3,4,34}, {3,44,61}, {4,45,61}, {17,37,38}, {17,41,56}, {34,44,45}, {37,41,55}, {38,55,56}

**Class 4** (6 elements, 4 triples):
{11,21,58}, {11,35,63}, {21,24,35}, {24,58,63}

**Class 5** (6 elements, 4 triples):
{18,19,62}, {18,22,53}, {19,22,54}, {53,54,62}

**Class 8** (3 elements, 1 triple):
{12,20,40}
