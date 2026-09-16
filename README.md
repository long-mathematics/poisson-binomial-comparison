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

## Lean formalization

The repository also contains a Lean 4 project with mathlib. The current scope is
the elementary finite algebra of Poisson--binomial masses and tails, the exact tail
objective, and the two-dimensional minimum value. The higher-dimensional comparison
theorem, benchmark, and complete two-dimensional equality classification have not
been formalized.

- Lean: `leanprover/lean4:v4.34.0`, pinned in `lean-toolchain`.
- mathlib: release `v4.34.0`, pinned to commit
  `5ed2965256430c3649e86755f9576b54eca72435` in `lakefile.toml`.
- `lake-manifest.json` locks the resolved dependency revisions.

With [elan](https://lean-lang.org/install/) installed, run from the repository root:

```sh
lake exe cache get Mathlib.Basic.Real.Basic \
  Mathlib.Algebra.BigOperators.Ring.Finset \
  Mathlib.Algebra.BigOperators.Group.Finset.Powerset \
  Mathlib.Algebra.Order.BigOperators.Group.Finset \
  Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset \
  Mathlib.Order.Interval.Finset.Nat \
  Mathlib.Algebra.BigOperators.Intervals \
  Mathlib.Data.Finset.Lattice.Fold \
  Mathlib.Algebra.BigOperators.Fin \
  Mathlib.Tactic.Ring \
  Mathlib.Tactic.Linarith
lake build
```

The first command downloads compiled mathlib dependencies for the current imports.
Elan installs the pinned Lean toolchain automatically if needed. Lake dependencies
and build artifacts live in the ignored `.lake/` directory.

`PoissonBinomialComparison/Basic.lean` defines `pbMass`, `pbTail`, `meanGap`, and
`tailDiff` in the `PoissonBinomialComparison` namespace. A Bernoulli outcome is its
finite set of successful coordinates; the count is the cardinality of that set.
`bernoulliWeight` gives the product-law weight, while `pbMassOn` and `pbTailOn`
allow any finite coordinate set, including one with a coordinate deleted.

The file proves nonnegativity for parameters in `[0, 1]`, normalization, the
tail-as-sum-of-masses formula, mass and tail recurrences, the finite-sum formula
for the mean gap, and support and zero-threshold identities. Algebraic identities
hold for arbitrary real parameters. Natural-number counts use successor-indexed
recurrences, with the zero-count case stated separately. These are finite algebraic
representations; no measure-theoretic probability spaces are constructed.

`PoissonBinomialComparison/Tail.lean` proves the general tail-sum identity and its
tail-difference version. It defines `ValidParameters`, `AdmissiblePair`, and
`tailObjective`. In positive dimension, `tailObjective` is the exact nonempty
finite maximum over thresholds `1, ..., n`, without adjoining zero to the set of
values. Only dimension zero uses the separate convention `tailObjective = 0`.
The interface proves threshold bounds, an upper-bound characterization, and
attainment of the maximum.

`PoissonBinomialComparison/TwoDimensional.lean` proves `D₁ + D₂ = Δ`, the two-tail
maximum formula, and `twoDimensional_lower_bound`. The lower bound is algebraic
and holds even without the admissibility assumptions. The theorem
`complementaryPair_two_attains` shows that for every `0 ≤ Δ ≤ 2` the constant
vectors `p_i = (1 + Δ/2)/2` and `q_i = (1 - Δ/2)/2` are admissible, have gap `Δ`,
and attain objective `Δ/2`.

`PoissonBinomialComparison.lean` is the library entry point.
`Main.lean` is a minimal executable that imports the library.
Both the library and executable are default build targets. To run the executable:

```sh
lake exe poisson_binomial_comparison
```
