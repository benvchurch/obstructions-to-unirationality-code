# Fermat Quartic Two-Torsion

This directory studies rational and phantom `2`-torsion on the Jacobian of the Fermat quartic, together with the corresponding étale double covers, Brauer obstructions, and descent questions.

The recurring mathematical problem is:

`find a Galois-invariant class in J[2] -> determine whether it comes from a line bundle over Q -> decide whether the associated double cover descends`

There are four main strands:

1. `setup`: bitangents, rational subspaces, local Picard data, and local solubility;
2. `quadric`: quadric decompositions `F = Q1*Q3 - Q2^2` and the `J[2]` classes they define;
3. `descent`: explicit cocycles, automorphisms, and phantom-class descent tests;
4. `covers`: Brauer obstruction computations and checks on the corresponding genus-`5` covers.

## Where To Start

Read this branch in the following order:

1. [`brauer_obstruction_report.tex`](/home/benc/Documents/Grad School/Code/Shioda Conjecture Code/Fermat_quartic/two_torsion/brauer_obstruction_report.tex)
2. [`setup/bitangents_and_Vrat.m`](/home/benc/Documents/Grad School/Code/Shioda Conjecture Code/Fermat_quartic/two_torsion/setup/bitangents_and_Vrat.m)
3. [`quadric/classify_classes.m`](/home/benc/Documents/Grad School/Code/Shioda Conjecture Code/Fermat_quartic/two_torsion/quadric/classify_classes.m)
4. [`descent/verify_descent.m`](/home/benc/Documents/Grad School/Code/Shioda Conjecture Code/Fermat_quartic/two_torsion/descent/verify_descent.m)
5. [`covers/brauer_via_picard.m`](/home/benc/Documents/Grad School/Code/Shioda Conjecture Code/Fermat_quartic/two_torsion/covers/brauer_via_picard.m)

That gives the mathematical story before dropping into the individual experiments.

## Internal Structure

### High-level note

- [`brauer_obstruction_report.tex`](/home/benc/Documents/Grad School/Code/Shioda Conjecture Code/Fermat_quartic/two_torsion/brauer_obstruction_report.tex): main written account of the Fermat quartic `2`-torsion story and the Brauer obstruction.
- [`brauer_obstruction_report.pdf`](/home/benc/Documents/Grad School/Code/Shioda Conjecture Code/Fermat_quartic/two_torsion/brauer_obstruction_report.pdf): compiled version of the note.

### `setup/`

Foundational scripts for identifying the rationally visible part of `J[2]` and checking local conditions.

- [`setup/bitangents_and_Vrat.m`](/home/benc/Documents/Grad School/Code/Shioda Conjecture Code/Fermat_quartic/two_torsion/setup/bitangents_and_Vrat.m): bitangent computations and the rational subspace `V_rat`.
- [`setup/local_solubility.m`](/home/benc/Documents/Grad School/Code/Shioda Conjecture Code/Fermat_quartic/two_torsion/setup/local_solubility.m): local-solubility checks.
- [`setup/picard_local.m`](/home/benc/Documents/Grad School/Code/Shioda Conjecture Code/Fermat_quartic/two_torsion/setup/picard_local.m): local Picard calculations.

### `quadric/`

Constructs and classifies quadric decompositions of the Fermat quartic and identifies which `J[2]` classes they represent.

Representative themes:
- searching for decompositions over different fields;
- classifying classes by field of definition;
- orbit computations for the resulting classes;
- bitangent and conic residue data.

### `descent/`

This is the descent and phantom-class laboratory.

Representative themes:
- explicit Galois actions and cocycles;
- identifying special classes `eta`;
- comparing twists and conjugates;
- producing and testing phantom `2`-torsion classes;
- verifying whether associated covers descend.

### `covers/`

This collects scripts that test the cover side of the story more directly:
- whether a `J[2]` class corresponds to an actual cover over `Q`;
- how the Brauer obstruction is detected via Picard or Jacobian computations;
- whether candidate cover classes agree across different constructions.

## File Index

| File | Role | Math content | Status |
| --- | --- | --- | --- |
| `brauer_obstruction_report.tex` | Note source | Main writeup on Brauer obstruction and descent for the Fermat quartic | source |
| `brauer_obstruction_report.pdf` | Compiled note | Rendered research note | generated deliverable |
| `brauer_obstruction_report.aux`, `brauer_obstruction_report.log`, `brauer_obstruction_report.out` | TeX build artifacts | Auxiliary LaTeX files | generated |
| `setup/bitangents_and_Vrat.m` | Helper | Computes bitangents and the rationally generated subspace `V_rat` of `J[2]` | source |
| `setup/local_solubility.m` | Helper | Local-solubility checks relevant to descent and cover existence | source |
| `setup/picard_local.m` | Helper | Local Picard-group computations | source |
| `quadric/Q2_general_search.m` | Search | General search for quadratic/quadric decompositions | source |
| `quadric/bitangent_decomps.m` | Helper | Builds decompositions from bitangent configurations | source |
| `quadric/check_Qi_point.m` | Check | Field-specific consistency checks over `Q(i)` | source |
| `quadric/classify_classes.m` | Core source | Verifies methodology and classifies quadric decompositions by `J[2]` class | source |
| `quadric/conic_residue.m` | Helper | Conic-residue computations associated with decomposition data | source |
| `quadric/exhaustive_F3.m` | Search | Exhaustive finite-field search over `F_3` or related test cases | source |
| `quadric/gl2_orbits.m` | Helper | Orbit computations under `GL_2`-type actions on class data | source |
| `quadric/group_actions_J2.m` | Helper | Group-action analysis on `J[2]` | source |
| `quadric/scaled_decomps.m` | Helper | Studies decompositions up to scaling | source |
| `quadric/search_over_Q.m` | Search | Searches for decompositions defined over `Q` | source |
| `quadric/search_over_Qi.m` | Search | Searches for decompositions over `Q(i)` | source |
| `quadric/search_over_Qsqrt3.m` | Search | Searches for decompositions over `Q(sqrt(-3))` or the indicated quadratic field context | source |
| `quadric/splitting_fields.m` | Helper | Computes or compares splitting fields of decomposition data | source |
| `quadric/twist_decomps.m` | Helper | Decomposition behavior under twisting | source |
| `covers/brauer_multicheck.m` | Check | Multiple consistency checks for Brauer-obstruction calculations | source |
| `covers/brauer_via_jacobian.m` | Experiment | Detects the obstruction through Jacobian-side calculations | source |
| `covers/brauer_via_picard.m` | Experiment | Detects the obstruction through Picard-group and function-field calculations | source |
| `covers/check_cover_class.m` | Check | Checks agreement of candidate cover classes | source |
| `covers/missing_cover_F3.m` | Experiment | Finite-field evidence for a missing or obstructed cover class | source |
| `descent/aut_D.m` | Helper | Automorphism computations for the genus-`5` cover `D` | source |
| `descent/check_Vrat_intersection.m` | Check | Compares special classes with the rational bitangent subspace `V_rat` | source |
| `descent/check_conjugate.m` | Check | Conjugation consistency checks for classes or decompositions | source |
| `descent/cocycle.m` | Core source | Explicit cocycle computations for descent | source |
| `descent/compare_J2_Lpoly.m` | Check | Compares `J[2]` data with `L`-polynomial information | source |
| `descent/compare_J2_rational.m` | Check | Compares rational `J[2]` descriptions from different constructions | source |
| `descent/compare_J2_subspaces.m` | Check | Compares subspaces of `J[2]` arising from different geometric inputs | source |
| `descent/compare_twists.m` | Check | Relates the Fermat quartic to its twists in the descent story | source |
| `descent/descent_criterion.m` | Core source | Implements or tests the descent criterion for the cover/class | source |
| `descent/eta_stabilizer.m` | Helper | Computes the stabilizer of the distinguished `eta` class | source |
| `descent/explicit_auts.m` | Helper | Makes automorphism computations explicit for descent arguments | source |
| `descent/generic_quartic_search.m` | Search | Looks for similar phantom-`2` phenomena in more general quartics | source |
| `descent/identify_eta.m` | Helper | Identifies the relevant `eta` class in `J[2]` | source |
| `descent/lift_constants.m` | Helper | Computes constants needed in lifting or cocycle formulas | source |
| `descent/phantom_Qi.m` | Experiment | Phantom `2`-torsion analysis over `Q(i)` | source |
| `descent/phantom_cocycle.m` | Experiment | Cocycle computations for phantom classes | source |
| `descent/phantom_quartic.m` | Experiment | Phantom-class analysis for a different quartic example | source |
| `descent/sigma_action.m` | Helper | Computes the Galois action of `sigma` in the descent setup | source |
| `descent/tau_action.m` | Helper | Computes the Galois action of `tau` in the descent setup | source |
| `descent/verify_class.m` | Check | Verifies that a computed divisor or decomposition represents the intended class | source |
| `descent/verify_descent.m` | Driver/check | End-to-end verification that the genus-`5` curve descends to `Q` even when the cover does not | source |

## How The Pieces Fit Together

A useful mental ordering is:

1. `setup`: identify the rationally visible `2`-torsion and local constraints;
2. `quadric`: build candidate `2`-torsion classes from explicit quartic decompositions;
3. `descent`: decide whether those classes descend as line bundles and whether the associated covers descend;
4. `covers`: cross-check the cover picture from Picard-group and Jacobian viewpoints.

## Suggested Documentation Convention

For this branch, the labels that matter most are:

- `helper`: reusable routine or narrowly focused computation
- `search`: exploratory script scanning many possibilities
- `check`: validation of an assertion or agreement between methods
- `experiment`: a one-off computation that may not be part of the final canonical pipeline
- `note`: explanatory mathematical writeup

This branch is mathematically coherent, but it is not a single linear program; the file labels above are meant to make that explicit.
