# Mathlib audit

Audit date: 2026-07-03.

Parent repo checked: <https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME>.
The parent pins Lean to `leanprover/lean4:v4.29.0-rc6` and Mathlib to commit
`07642720480157414db592fa85b626dafb71355b`.

## Existing Gaussian material at the pinned commit

- `Mathlib/Probability/Distributions/Gaussian/Real.lean` defines
  `ProbabilityTheory.gaussianPDFReal`, `gaussianPDF`, and `gaussianReal` on
  `R`.  It proves basic density facts, affine image laws, characteristic and
  moment-generating functions (`charFun_gaussianReal`, `mgf_gaussianReal`),
  mean/variance identities, `gaussianReal_ext_iff`, and convolution of real
  Gaussian laws.
- `Mathlib/Probability/Distributions/Gaussian/Basic.lean` defines
  `ProbabilityTheory.IsGaussian` for Banach-space measures through all real
  continuous linear projections.  It proves real Gaussian instances, stability
  under continuous linear maps, products, convolution, and the characteristic
  function criterion `isGaussian_iff_charFunDual_eq`.
- `Mathlib/Probability/Distributions/Gaussian/CharFun.lean` proves the
  Banach/Hilbert characteristic-function characterization with explicit mean
  and covariance bilinear form:
  `isGaussian_iff_gaussian_charFunDual`, `isGaussian_iff_gaussian_charFun`,
  `gaussian_charFunDual_congr`, `gaussian_charFun_congr`, and uniqueness
  lemmas such as `IsGaussian.ext`.
- `Mathlib/Probability/Distributions/Gaussian/HasGaussianLaw/Basic.lean`
  provides `HasGaussianLaw` for random variables and closure under continuous
  linear maps, sums, products/projections, and `MemLp` for finite moments.
- `Mathlib/Probability/Moments/CovarianceBilin.lean` provides
  `covarianceBilin`, `covarianceOperator`, positivity, basis/Pi expansion
  lemmas, and map formulas.

## Confirmed gaps at the pinned commit

- No `Mathlib/Probability/Distributions/Gaussian/Multivariate.lean` exists at
  `07642720480157414db592fa85b626dafb71355b`.
- There is no finite-dimensional constructor from arbitrary symmetric PSD
  covariance data `C : (n -> R) -> (n -> R) -> R` to a measure on `R^n`.
- There is no reusable Wick/Isserlis theorem over a finite pairing type.
- There is no Gaussian integration-by-parts theorem packaged for finite
  Gaussian vectors.
- There are no explicit dimension-uniform moment constants aimed at the
  Balaban small-field regime.
- There is no finite lattice massive free field package with covariance
  `(-Delta + m^2)^{-1}` and an explicit exponential decay rate in `m`.

## Upstream drift note

GitHub code search on 2026-07-03 shows that current Mathlib `master` has a
`Mathlib/Probability/Distributions/Gaussian/Multivariate.lean` file.  It is not
available in the parent repo's pinned commit.  Any future upstreaming work
should first diff that file against the interfaces here before duplicating
finite-dimensional constructions.
