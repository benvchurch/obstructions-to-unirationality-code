# Klein_quartic/two_torsion/ Cleanup Report

## Files KEPT (new, general-purpose)

### `steiner_genus2.m` (NEW)
General-purpose pipeline: given a smooth quartic over Q, computes bitangent lines
(over the splitting field), Steiner complexes, witnessing conics, quartic
decompositions aF = L_iL_jL_kL_l + bQ^2, and genus-2 curves via the
determinantal pencil det(Q1 + 2tQ2 + t^2 Q3).

### `hensel_decomp.m` (NEW)
General-purpose Hensel lifting search: given a smooth quartic over Q, finds
quadric decompositions F = Q1*Q3 - Q2^2 by exhaustive search over F_p, Hensel
lifts to high p-adic precision, and attempts LLL recognition. Classifies
results by Aut(C) orbits on J[2].

---

## Files to DELETE (with summaries)

### Root `two_torsion/` files

| File | What it does | Why delete |
|------|-------------|------------|
| `bitangent_data.m` | Library: computes 28 bitangent lines to C_twist over Q(sqrt(-7)) via Groebner basis. Exports `K`, `w`, `bitangent_lines`. | Hardcoded for C_twist. Functionality subsumed by `steiner_genus2.m`. |
| `bitangents.m` | Self-contained exploration: finds 28 bitangent lines over F_p and Q(sqrt(-7)), classifies by Galois action and Z/3Z orbits. Defines `IsBitangentRestriction`, `FindBitangentsFp`, etc. | Exploratory. Overlaps with `bitangent_data.m` and `steiner.m`. |
| `steiner.m` | Full pipeline (1035 lines): bitangent lines -> Steiner complexes -> conics -> quartic decompositions -> genus-2 curves -> j-invariants -> Z/3Z orbits. All over C_twist. | Replaced by `steiner_genus2.m` (general-purpose version). |
| `syzygetic_final.m` | Verifies the rational syzygetic identity -F + l1l2l3l4 = 7Q^2 for C_twist's 4 Q-rational bitangent lines. | One-off verification, C_twist specific. |
| `syzygetic_search.m` | Searches for syzygetic tetrads over F_71 by brute force (all C(28,4) tetrads). | Exploratory search script, C_twist specific. |
| `syzygetic_verify.m` | Lifts one syzygetic tetrad from F_71 to Q via rational reconstruction. | Follow-up to syzygetic_search, C_twist specific. |
| `syzygetic_verify2.m` | Tests two tetrads over Q(sqrt(-7)) with general conic ansatz. | Debug/exploratory, C_twist specific. |
| `explicit_example.m` | Shows two non-isomorphic genus-2 curves from the same Steiner complex (#7). Loads bitangent_data.m. Contains the **buggy** MakeGenus2. | Superseded by verify_example.m which fixes the bug, and both superseded by steiner_genus2.m. |
| `verify_example.m` | Corrects the genus-2 pencil scaling (b absorbed into Q1 and Q2). Compares old vs new for all 15 pairs in Complex #7. | Bug-fix script. The corrected formula is now in steiner_genus2.m. |
| `check_isogeny.m` | Tests whether elliptic curves from different PSL(2,7) orbits' j-invariants are isogenous via a_p^2 overlap. | Exploratory, first attempt. Superseded by check_isogeny_correct.m. |
| `check_isogeny2.m` | Refined isogeny test: factors mp23 over Q(sqrt(7)), searches Cremona database for matching traces. | Exploratory, superseded by check_isogeny_correct.m. |
| `check_isogeny3.m` | Full pipeline: Steiner decomps -> genus-2 curves -> Igusa invariants -> point counting vs E=49a1. | Substantial but exploratory, C_twist specific. |
| `check_isogeny_correct.m` | Rigorous isogeny test via CM field criterion (squarefree part of a_p^2 - 4p). The cleanest of the isogeny files. | Polished but C_twist specific. Self-contained investigation, not needed for general pipeline. |
| `check_j23_internal.m` | Tests whether the two 7-orbits (mp2 vs mp3 roots) give isogenous curves. | Companion to check_isogeny_correct.m, C_twist specific. |
| `debug_orbits.m` | Debugs FindOrbit failures for specific Steiner complexes. | Debug code. |
| `debug_roots.m` | Investigates underdetermined conic computation by using all 12 bitangent lines. | Debug code. |
| `supersingular_stats.m` | Collects supersingular reduction statistics for j1 and j23 up to 100K primes. | Data collection, C_twist specific. |
| `supersingular_stats2.m` | Optimized version, extends to 1M primes with splitting type analysis. | Data collection, C_twist specific. |

### `two_torsion/quadric/` files

| File | What it does | Why delete |
|------|-------------|------------|
| `klein_decomp_representatives.m` | **Final answer**: records verified (delta, epsilon, gamma) for all 4 PSL(2,7) orbits over Q(zeta_7). Defines `Decomposition(del,eps,gam)`. | Klein-specific reference data. Results documented in MEMORY.md. |
| `klein_decomp_hensel.m` | Core Hensel lifting: F_29 exhaustive search -> linearized Newton Hensel lift -> LLL recognition. Lifts all 18 Q1/Q2/Q3 coefficients. | Replaced by `hensel_decomp.m` (general version). |
| `klein_decomp_parametric.m` | **Key algorithm**: derives 3-parameter standard form (delta, epsilon, gamma), searches F_29, Hensel lifts with brute-force Newton correction (p^3 per step), LLL recognition. | Replaced by `hensel_decomp.m` (general version). |
| `klein_decomp_lift.m` | Applies PSL(2,7) to Q-rational base decomposition over Q(zeta_7), classifies all 168 images. | Klein-specific group-theoretic approach. |
| `klein_decomp_lift12.m` | Targets orbits 1 and 2 specifically: enumerates all F_29 standard-form starts, brute-force Hensel lift. | Klein-specific. Subsumed by parametric approach. |
| `klein_decomp_padic.m` | Alternative: factors F+Q2^2 directly over Q(zeta_7) with small perturbations of F_29 lift. | Exploratory alternative approach. |
| `klein_decomp_search.m` | Simplest script: brute force Q-rational decompositions with integer Q2 in [-3..3]. | Only finds orbit 4. Subsumed by hensel_decomp.m. |
| `klein_decomp_Qzeta7.m` | Sparse Q2 search over Z[zeta_7] with various scalings lambda. | Shotgun approach, Klein-specific. |
| `klein_decomp_scaled.m` | Brute force n*F = Q1*Q3 - Q2^2 with integer scaling n, orbit classification over F_29. | First attempt at scaled decompositions. |
| `klein_decomp_scaled2.m` | Minor iteration on klein_decomp_scaled.m with improved output ordering. | Duplicate of scaled.m. |
| `klein_decomp_bivar.m` | Multi-strategy script with several abandoned approaches (CRT, bitangent pairs, 6-parameter search). | Highly exploratory with dead code. |
| `klein_decomp_denom.m` | Hensel lift to 29^16 precision, test denominators d=1..49 for (1/d)*Z[zeta_7] recognition. | Specialized lifting tool for orbits 1,2. |
| `klein_decomp_galois.m` | Checks Galois conjugate distribution of orbit-3 decomposition across PSL(2,7) orbits. | Klein-specific diagnostic. |
| `klein_decomp_add.m` | Demonstrates J[2] addition table from PSL(2,7)-transformed decompositions. | Klein-specific structural analysis. |
| `klein_decomp_orbits123.m` | Finds orbits 1-3 via sparse Z[zeta_7] Q2 with mod-29 prefilter. | Klein-specific search. |
| `klein_decomp_verify12.m` | Verifies all 4 orbit representatives with explicit (1/2)*Z[zeta_7] parameters. | Klein-specific verification. Same data as representatives.m. |
| `klein_decomp_table.m` | Formatted table of all F_29 decompositions with addition table and orbit analysis. | Klein-specific display script. |
| `klein_classify_decomps.m` | Classifies 15 Q-rational decompositions by PSL(2,7) orbit (confirms all hit orbit 4). | Klein-specific classification. |
| `klein_orbit.m` | Foundational: computes PSL(2,7) orbits on J[2]\{0}, classifies Q-rational conics/decompositions. Most documented file. | Klein-specific. Orbit infrastructure now in hensel_decomp.m. |
| `klein_conic_Qzeta7.m` | Searches for Z[zeta_7] conics with all-even divisor by F_29 enumeration. | Klein-specific conic search. |
| `klein_verify_lifts.m` | Verifies Q(zeta_7) conic representatives at p=43 and over Q(zeta_7) function field. | Klein-specific verification. |
| `twist_classify.m` | Classifies Q-rational decompositions of C_twist by PSL(2,7) orbit using AutomorphismGroup. | C_twist specific. |
| `twist_conic_Qsqrt7.m` | Searches for Z[sqrt(-7)] conics of C_twist, double-validated at p=29 and p=43. | C_twist specific. |
| `twist_decomp_search.m` | Scaled Q-rational decomposition search for C_twist. Incomplete automorphism code. | C_twist specific, incomplete. |
