# Codebase Guide

This repository is a Magma research codebase for studying product-quotient surfaces, quotient curves, Jacobians of special genus-3 curves, and related descent and 2-torsion questions. The code is not organized as a single package; it is closer to a shared library of reusable Magma routines plus project-specific scripts for the examples and the quartic-curve investigations.

## 1. Mental model of the repository

Most of the code falls into one of four layers.

1. `Core library`  
   Reusable routines for:
   - product-quotient surface invariants,
   - genus and monodromy of intermediate covers,
   - spherical generating systems for Galois covers,
   - Jacobian/cohomology decomposition.

2. `Example and verification drivers`  
   Scripts that run the core routines on concrete groups and curves appearing in the paper or in exploratory computations.

3. `Curve-specific research branches`  
   Larger subtrees devoted to a specific curve or family, especially the Klein quartic and Fermat quartic. These contain both reusable helpers and one-off experiments.

4. `Outputs and notes`  
   Generated logs, tables, PDFs, LaTeX writeups, and subgroup lattice diagrams that record the outcome of computations.

In practice, a typical computation starts with a finite group `G` and a spherical generating sequence `seq` describing a `G`-cover of `P^1`, then moves through the following chain:

`group data -> curve cover -> intermediate quotients -> Jacobian/cohomology data -> surface invariants / descent / 2-torsion analysis`

## 2. Core mathematical files

### `invariants.m`

This is the main library for product-quotient surfaces of the form
`(C1 x C2)/G`.

It implements:
- cyclic quotient singularity bookkeeping via continued fractions,
- baskets of singularities,
- local correction terms `k`, `e`, `l`,
- surface invariants such as `K2`, Segre number, and diagonal form number,
- fundamental-group computations for product-quotient surfaces,
- Hodge-diamond style summaries.

Mathematically, this file is where the surface side of the project lives. If a script asks whether a quotient surface is of general type, has positive diagonal form number, or has trivial fundamental group, this is usually the file doing the work.

### `intermediate_extensions.m`

This file studies intermediate quotients `C/H` inside a `G`-cover `C -> C/G`.

It implements:
- genus computations using the permutation action of `G` on cosets of `H`,
- monodromy for intermediate covers,
- transfer of branch data through subgroup chains.

The central idea is Riemann-Hurwitz: starting from a spherical generating sequence for `G`, the code computes how that data looks after passing to a quotient by a subgroup `H`.

This file is the bridge between group-theoretic input and the geometry of quotient curves.

### `group_reps.m`

This is the representation-theoretic layer.

It implements:
- searches for spherical generating systems and Belyi data,
- equivalence of generating sequences up to conjugacy, Hurwitz moves, and automorphisms,
- decomposition of rational cohomology representations,
- group-ring/Jacobian decomposition computations.

Mathematically, it answers questions like:
- does a group admit a 3-point cover with given ramification orders?
- what is the genus of the resulting curve?
- how does `H^1(C, Q)` decompose as a `Q[G]`-module?
- what elliptic or higher-dimensional factors should appear in `Jac(C)`?

### `hilbert_modular_forms.m`

This file is more data-driven than the three above. It records explicit Hilbert modular form data over a totally real cubic field and uses that data to identify elliptic curve factors via Hecke eigenvalues and supersingular-prime tests.

This is relevant when the Jacobian decomposition predicts elliptic factors and the goal is to identify them arithmetically rather than only representation-theoretically.

### `subgroups.m`, `subgroup_schemes.m`, `general_type.m`, `mixed_case.m`, `Gamma0.m`, `ray_class_field_checks.m`, `LMFDB_api.m`

These are supporting scripts rather than a single unified library.

- `subgroups.m` and `subgroup_schemes.m` focus on subgroup lattices and Galois-invariant subgroup questions.
- `general_type.m` is an exhaustive search-style script for testing many sequence pairs and looking for surfaces with prescribed numerical behavior.
- `mixed_case.m` and `Gamma0.m` are specialized experiments.
- `ray_class_field_checks.m` and `LMFDB_api.m` support arithmetic checks and comparisons with external number-theoretic data.

## 3. Top-level driver scripts

### `compute_examples.m`

This is the main exploratory driver at the top level. It loads `invariants.m`, `intermediate_extensions.m`, and `group_reps.m`, then runs through a collection of groups and spherical generating data.

Typical uses:
- search for promising product-quotient surfaces,
- inspect subgroup quotients `C/H`,
- compute Jacobian decompositions,
- test examples such as Hurwitz curves, Fricke-Macbeath, Accola-Maclachlan, and dihedral cases.

If you want to understand how the reusable routines are meant to be combined, this is one of the first files to read.

### `verify_examples.m`

This is closer to a theorem-verification script than an exploratory notebook. It checks the specific subgroup cases used in the main theorem, especially for `PSL(2,13)`, by verifying:
- triviality of the surface fundamental group,
- positivity of the diagonal form number.

### `pi1_tests.m`

This is a focused test script for fundamental-group computations and should be read together with the `Pi1` routines in `invariants.m`.

## 4. Example and test directories

### `examples/`

These are curated case studies such as:
- `genus17.m`: the Hurwitz curve of genus 17,
- `genus118.m`,
- `groups1344.m`,
- `groups768.m`.

These scripts usually take one concrete automorphism group or curve and work out subgroup genera, Jacobian factors, or quotient geometry in more detail than the top-level exploratory scripts.

### `tests/`

These are smaller focused scripts checking specific assertions or computations:
- supersingular-prime searches,
- congruence tests,
- Wilson operators,
- singularity-index bounds,
- quadratic twists,
- explicit elliptic-curve checks,
- subgroup/centralizer computations.

The `tests` directory is heterogeneous: some files are genuine tests, others are compact computational experiments.

## 5. Quartic-curve branches

## `Klein_quartic/`

This directory contains computations centered on the Klein quartic and closely related curves.

### `Klein_quartic/Klein_quartic.m`

This is a compact driver for the classical Klein quartic with automorphism group `PSL(2,7)`. It computes Belyi data, rational cohomology decompositions, and mod-2 representation behavior of the Jacobian.

### `Klein_quartic/Klein_quartic_models.m`

This file contains explicit models and coordinate realizations for the Klein quartic side of the project.

### `Klein_quartic/Klein_quartic_semidirect.m`

This studies a semidirect-product construction related to quartic automorphisms and mod-2 representations.

### `Klein_quartic/twist/`

This subtree studies twists of the Klein quartic, especially arithmetic descent and local/global obstruction questions.

Representative topics:
- twist fields,
- local solubility,
- crossed homomorphisms and `H^1`,
- local obstructions over cubic fields.

### `Klein_quartic/two_torsion/`

This is currently the largest and most active specialized subtree. It studies the `J[2]`-geometry of genus-3 quartics, especially the Klein quartic twist and related examples.

It is best read as four subprojects:

- `setup/`  
  Preparatory routines for rank and local calculations.

- `covers/`  
  Construction of mod-2 covers and related double-cover data.

- `elliptic_curve_factors_tests/`  
  Checks that the Prym or Jacobian factors match expected elliptic curves and isogeny classes.

- `ss_*`, `j128_*`, `aut_j2_modules.m`  
  Arithmetic and Galois-representation analysis of 2-torsion, especially orbit structure, Jacobian factors, and supersingular-prime coincidences.

The main driver here is [`Klein_quartic/two_torsion/tests.m`](/home/benc/Documents/Grad School/Code/Shioda Conjecture Code/Klein_quartic/two_torsion/tests.m), which runs the Steiner/Prym pipeline on several quartics and writes logs and summaries under `results/`.

Two note files are especially important:
- [`Klein_quartic/two_torsion/pipeline_math.md`](/home/benc/Documents/Grad School/Code/Shioda Conjecture Code/Klein_quartic/two_torsion/pipeline_math.md) explains the geometry behind bitangents, theta characteristics, Steiner complexes, and genus-2 Pryms.
- [`Klein_quartic/two_torsion/PRYM_INVARIANTS.md`](/home/benc/Documents/Grad School/Code/Shioda Conjecture Code/Klein_quartic/two_torsion/PRYM_INVARIANTS.md) records the invariant data being tracked for Prym computations.

The `results/` and `results.pre_refactor/` directories are output archives, not source libraries.

## `Fermat_quartic/`

This branch focuses on the Fermat quartic and its automorphisms.

### `Fermat_quartic/Fermat_aut.m`

This builds explicit automorphism-group actions, including semidirect-product realizations and residual mod-2 representation experiments.

### `Fermat_quartic/fermat_quartic_aut_action.m`

This studies explicit automorphism actions on the quartic and related modules.

### `Fermat_quartic/two_torsion/`

This branch studies rational and phantom 2-torsion on the Jacobian of the Fermat quartic and related quartics.

It is organized by task:

- `setup/`  
  Bitangents, rational 2-torsion subspaces, local Picard data, and local solubility.

- `quadric/`  
  Searches for quadric decompositions `F = Q1*Q3 - Q2^2`, orbit classification, splitting fields, and constructions of 2-torsion classes.

- `descent/`  
  Explicit Galois-descent calculations, cocycles, automorphisms, phantom classes, and verification scripts.

- `covers/`  
  Brauer obstruction checks and explicit cover-class computations.

The best high-level entry point is [`Fermat_quartic/two_torsion/brauer_obstruction_report.tex`](/home/benc/Documents/Grad School/Code/Shioda Conjecture Code/Fermat_quartic/two_torsion/brauer_obstruction_report.tex), which explains the mathematical goal of this directory: determining when Galois-invariant `2`-torsion classes give étale double covers that fail to descend because of a Brauer obstruction.

## 6. Other research directories

### `Elliptic Surfaces/`

These files are separate experiments on explicit elliptic surfaces and finite-group actions. They are less tied to the product-quotient workflow, but they belong to the same overall research program around surface geometry and arithmetic.

### `Bauer and Pignatelli code/`

This directory contains inherited or adapted code from the Bauer-Pignatelli and Bauer-Catanese-Grunewald-Pignatelli papers. It is useful historical context and sometimes supplies algorithms that the newer top-level scripts build on.

### `diagrams/`

This directory contains generated subgroup-lattice diagrams in LaTeX, Graphviz, and PDF form. These are outputs supporting the geometry and group theory, not core executable code.

### `LMFDB_data/`

This directory stores external arithmetic data used for comparisons or imports. It is auxiliary input rather than algorithmic source code.

## 7. How to read the code

A good reading order is:

1. [`invariants.m`](/home/benc/Documents/Grad School/Code/Shioda Conjecture Code/invariants.m)
2. [`intermediate_extensions.m`](/home/benc/Documents/Grad School/Code/Shioda Conjecture Code/intermediate_extensions.m)
3. [`group_reps.m`](/home/benc/Documents/Grad School/Code/Shioda Conjecture Code/group_reps.m)
4. [`compute_examples.m`](/home/benc/Documents/Grad School/Code/Shioda Conjecture Code/compute_examples.m)
5. one focused branch, either:
   - [`Klein_quartic/two_torsion/pipeline_math.md`](/home/benc/Documents/Grad School/Code/Shioda Conjecture Code/Klein_quartic/two_torsion/pipeline_math.md), or
   - [`Fermat_quartic/two_torsion/brauer_obstruction_report.tex`](/home/benc/Documents/Grad School/Code/Shioda Conjecture Code/Fermat_quartic/two_torsion/brauer_obstruction_report.tex)

That order goes from reusable infrastructure to concrete geometry.

## 8. Terminology used throughout the repository

Some recurring words have a specific meaning in this codebase.

- `seq`  
  Usually a spherical generating sequence for a finite group, often encoding branch cycles of a `G`-cover of `P^1`.

- `rep`, `reps`  
  Usually representatives of generating systems up to conjugacy, Hurwitz equivalence, or automorphism.

- `IntermediateMonodromy`  
  Passes from a `G`-cover to the induced monodromy on an intermediate quotient `C/H`.

- `basket`  
  The multiset of cyclic quotient singularities of the product-quotient surface.

- `diagonal form number`  
  The intersection-theoretic quantity being used to test positivity in the paper.

- `Prym`  
  Usually refers to the principally polarized abelian surface associated to an étale double cover of a genus-3 curve, often realized in the code via a genus-2 Jacobian.

- `phantom 2-torsion`  
  A Galois-invariant class in `J[2]` that does not come from the expected rational geometric constructions and may fail to descend as a line bundle.

## 9. Caveats about the organization

- This is research code, so exploratory scripts and reusable routines live side by side.
- Some files are polished notes, while others are one-off experiments that record a successful computation.
- Several directories contain generated logs and PDFs mixed with source.
- The most current work appears to be in `Klein_quartic/two_torsion/`, which also has recent refactoring-related output files.

If you want to keep documenting the repository further, the next useful step would be a per-file index for the two largest research branches:
- `Klein_quartic/two_torsion/`
- `Fermat_quartic/two_torsion/`
