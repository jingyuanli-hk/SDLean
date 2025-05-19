# SD-Lean

Formal Lean 4 development based on  "Geometric Formalization of First-Order Stochastic Dominance in N Dimensions:  A Tractable Path to Multi-Dimensional Economic Decision Analysis"  [FSD_ND.pdf](./FSD_ND.pdf).

## Overview

This repository contains Lean 4 formalizations of results from the paper "Geometric Formalization of First-Order Stochastic Dominance in N Dimensions:  A Tractable Path to Multi-Dimensional Economic Decision Analysis". The main focus is on formalizing first-order stochastic dominance (FSD) and its connection to expected utility, in both one and N dimensions.

## Structure

- OneDim.lean`: 1D (real line) formalization.
- MultiDim.lean`: N-dimensional formalization.
- Main.lean`: Entry point aggregating all modules.

## Building

```bash
lake build
```

## Contributing

- Mathlib.Analysis.Calculus.Deriv.Basic
