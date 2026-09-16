# The exact Poisson--binomial comparison in every dimension

Christopher D. Long

This repository contains the current preprint and LaTeX source for a sharp Poisson--binomial comparison theorem in every dimension.

## Preprint

- [PDF](poisson_binomial_comparison.pdf)
- [LaTeX source](poisson_binomial_comparison.tex)

The current manuscript is dated September 13, 2026.

## Abstract

For coordinatewise ordered Bernoulli parameters with a prescribed total mean gap, the maximum difference of count tails is minimized by homogeneous parameters. For a nondegenerate gap $0<\Delta<n$, in odd dimension $n=2m+1\ge3$ the two minimizers are the homogeneous pairs whose likelihood ratios equal one at count $m$ or $m+1$; in even dimension $n\ge4$ the unique minimizer is the complementary homogeneous pair. We prove the comparison and these equality statements by a global stationary-point reduction, with all boundary faces included. A normalized switch-mass identity orders the homogeneous switching values. The same extremizers give the exact product total-variation minimum. The exceptional two-dimensional equality families are classified in the appendix.

## Building

The paper is self-contained and has no external bibliography or figure files. With a standard TeX installation:

```sh
latexmk -pdf poisson_binomial_comparison.tex
```

The compiled PDF is intentionally tracked in the repository.
