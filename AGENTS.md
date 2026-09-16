# Repository instructions

This repository contains a mathematical research preprint.

## Primary document

The primary source is `poisson_binomial_comparison.tex`.

Compile with:

```sh
latexmk -pdf poisson_binomial_comparison.tex
```

The compiled `poisson_binomial_comparison.pdf` is intentionally tracked.

## Mathematical integrity

- Do not alter theorem, proposition, lemma, corollary, or conjecture statements unless explicitly instructed.
- Do not silently weaken or strengthen hypotheses or conclusions.
- Do not silently repair a suspected mathematical error. Flag it and explain the issue first.
- Preserve mathematical notation unless a task explicitly concerns notation.
- When changing a proof, inspect downstream results that depend on the changed argument.
- Distinguish substantive mathematical changes from editorial, typographical, and repository changes.

## LaTeX conventions

- Preserve the existing document style and notation.
- Do not introduce unnecessary packages or macros.
- Keep existing labels stable whenever possible.
- Resolve broken references and citations caused by edits.
- The bibliography is contained directly in the TeX source; there is currently no external `.bib` file.

## Validation

Before completing a task that changes the manuscript:

1. Compile the paper with `latexmk -pdf poisson_binomial_comparison.tex`.
2. Check the final LaTeX log for undefined references or citations.
3. Review the complete diff.
4. Report substantive mathematical changes separately from editorial or mechanical changes.

## Generated files

Do not commit LaTeX auxiliary files. The final compiled PDF is the exception and should remain tracked.
