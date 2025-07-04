# Shioda Conjecture Research Code

This repository contains research code related to the Shioda Conjecture and Bauer surfaces with geometric genus 0.

## Overview

This project implements computational methods for studying algebraic surfaces, particularly focusing on:
- Hilbert modular forms
- Group representations
- Subgroup lattices
- Zeta functions
- Intermediate extensions

## Repository Structure

### Core Files
- `hilbert_modular_forms.m` - Use Hilbert modular forms to compute j-invariant of elliptic curve factor in jacobian
- `group_reps.m` - Group representation computations for computing cohomology of curves
- `subgroups.m` - Subgroup lattice calculations
- `invariants.m` - Computation of surface invariants
- `compute_examples.m` - Example computations and tests

### Zeta Function Module
The `zeta_function/` directory contains specialized code for:
- Zeta function computations
- Lifting algorithms
- Correctness checks
- Runtime comparisons

### Diagrams
The `diagrams/` directory contains LaTeX-generated visualizations of:
- Subgroup lattices
- Quotient curves

## Getting Started

This code is written in Magma, a computational algebra system. To run the examples:

1. Install Magma
2. Load the relevant files: `load "compute_examples.m";`
3. Run the test functions

## Research Context

This work is supplemental to the paper "Obstructions to unirationality for product-quotient surfaces over \overline{\mathbb{F}_p}", which relates to the Shioda Conjecture. The code implements various computational techniques for studying these surfaces and their associated invariants.

## Files

- **Mathematical computations**: `.m` files contain the main computational code
- **Signatures**: `.sig` files contain function signatures for Magma
- **Documentation**: README files in subdirectories
- **Output**: Various output files from computations

## Contributing

This is research code. For questions or collaboration, please contact the repository owner.
