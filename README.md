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

The Lean 4 development formalizes the manuscript, including the main comparison,
all equality cases, product total variation, endpoints, and the two-dimensional
appendix. The
[coverage and continuation ledger](FORMALIZATION_STATUS.md) is the authoritative
record of theorem coverage, manuscript correspondence, and final validation;
the module guide below gives the principal entry points.

- Lean: `leanprover/lean4:v4.34.0`, pinned in `lean-toolchain`.
- mathlib: release `v4.34.0`, pinned to commit
  `5ed2965256430c3649e86755f9576b54eca72435` in `lakefile.toml`.
- `lake-manifest.json` locks all resolved dependency revisions.

With [elan](https://lean-lang.org/install/) installed, run from the repository root:

```sh
lake exe cache get
lake build
```

The first command downloads the compiled cache for the pinned mathlib revision.
Elan installs the pinned Lean toolchain automatically if needed. Dependencies and
build artifacts live in the ignored `.lake/` directory. To check an individual
module, for example:

```sh
lake build PoissonBinomialComparison.GlobalHomogeneity
```

All declarations live in the `PoissonBinomialComparison` namespace. The library
entry point is [PoissonBinomialComparison.lean](PoissonBinomialComparison.lean).
Both the library and the small `Main.lean` executable are default build targets;
`lake exe poisson_binomial_comparison` runs that executable. The mathematical
validation is the Lean build, rather than the executable's informational output.

### Representation

A Bernoulli outcome is the finite set of successful coordinates; its count is
that set's cardinality. `bernoulliWeight` gives the product-law weight, and
`pbMass` is the manuscript's subset sum. `pbMassOn` and `pbTailOn` permit any
finite coordinate set, including deletions. `productTV` is the finite sum of
absolute differences between these outcome weights, divided by two. No
measure-theoretic probability spaces are needed. Analytic benchmark formulas use
mathlib's real derivatives and interval integrals.

For positive dimension, `tailObjective` is exactly the nonempty maximum over
thresholds `1, ..., n`; zero is not inserted into that maximum. Dimension zero
has the separate convention `tailObjective = 0`. Some intermediate proofs use
integer counts with mass zero below zero, or recursive Bernoulli convolutions;
their equivalences with the subset-sum laws are proved. `benchmark` is the central
switching value, with the manuscript's prescribed values at gaps zero and `n`.

### Module guide

- **Finite laws and base case:** `Basic`, `Tail`, `Coordinate`, `Endpoints`,
  `Reflection`, and `Reindex` provide the algebraic foundations.
  `TwoDimensional` proves the base inequality and attainment;
  `TwoDimensionalEquality` gives the complete exceptional appendix classification.
- **Bernoulli comparisons:** `LogConcavity`, `LikelihoodRatio`, `ActiveThresholds`,
  `Adjoining`, and `HomogeneousBlockMode` establish the count-law inequalities and
  derivative criteria. `MaximalAtom` and `DeletionMixture` supply the maximal-atom
  and two-positive-gap bounds.
- **Homogeneous benchmark:** `SwitchFunctions`, `SwitchDerivative`,
  `SwitchOrdering`, `HomogeneousMinimum`, and `HomogeneousEquality` identify the
  central switches and their exact minimizers. `BenchmarkConcavity`,
  `BenchmarkExplicit`, and `OddSwitchParameter` cover strict concavity and the
  explicit even, odd, and dimension-three formulas. `BenchmarkAttainment`
  constructs pairs attaining the benchmark.
- **Global minimizer reduction:** `DimensionImprovement`, `MinimizerReduction`,
  `TailKKT`, `SplitPerturbation`, `LowerCoordinateClassification`, and
  `CommonHomogeneousCoordinates` feed into `GlobalHomogeneity`. Its theorem
  `IsGapMinimizer.homogeneous` uses comparison in the preceding dimension to
  prove that every interior-gap global minimizer in dimension at least three is
  a strictly interior homogeneous pair.
- **Final comparisons:** `GlobalComparison` assembles dimension induction and
  the tail-objective equality classification. `TotalVariation`,
  `TotalVariationBounds`, and `TotalVariationHomogeneous` connect finite product
  total variation with the count-tail objective. `MainTheorem` exposes both
  sharp comparisons, simultaneous attainment, even and odd product equality
  cases, and the endpoint classifications. Consult the ledger for the final
  validation status.

The proofs include documented equivalent alternatives to manuscript arguments:
the two-deletion mixture is factored directly into a Bernoulli law, and the
positive-plus-zero lower-block exclusion first adjoins variables at the original
parameter and then increases the entire block. These alternatives preserve the
stated conclusions and allow deterministic background parameters.
