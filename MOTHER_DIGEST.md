# Mother-facing digest

Date: 2026-07-04

This digest records the current Lean names that the parent repository can
consume without importing frontier branches.  It is a routing note, not a
claim of continuum construction, Yang-Mills mass gap progress, or OS/Wightman
reconstruction.

## Import surface

Parent import:

```lean
import Interfaces
```

The root module `Interfaces.lean` re-exports the closed fact modules below and
the conditional interfaces.  Public interface names are tracked in
`INTERFACES.md`; changes to those names or types should be treated as interface
changes.

## Closed Lean facts on main

| Name | File | What it supplies |
| --- | --- | --- |
| `GaussianField.GaussianVectorSpec.charExponent_zero_arg` | `LeanGaussianField/GaussianVector.lean` | The target characteristic exponent vanishes at the zero test vector. |
| `GaussianField.GaussianVectorSpec.charExponent_zero_spec` | `LeanGaussianField/GaussianVector.lean` | The zero mean/covariance specification has identically zero exponent. |
| `GaussianField.GaussianVectorSpec.diag_nonneg` | `LeanGaussianField/CovarianceBounds.lean` | Positive semidefinite covariance implies nonnegative diagonal entries. |
| `GaussianField.GaussianVectorSpec.covariance_sq_le` | `LeanGaussianField/CovarianceBounds.lean` | Squared Cauchy-Schwarz control for covariance entries. |
| `GaussianField.GaussianVectorSpec.abs_covariance_le` | `LeanGaussianField/CovarianceBounds.lean` | Absolute covariance control by diagonal square roots. |
| `GaussianField.GaussianVectorSpec.std` | `LeanGaussianField/CovarianceBounds.lean` | Standard centered finite Gaussian specification data. |
| `GaussianField.Pairing.weight_empty` | `LeanGaussianField/PairingLemmas.lean` | Empty Wick pairing has weight one. |
| `GaussianField.Pairing.abs_weight_le_pow` | `LeanGaussianField/PairingLemmas.lean` | Pairing-weight bound from per-edge covariance bounds. |
| `GaussianField.abs_weight_le_of_diag` | `LeanGaussianField/WickBound.lean` | Wick-weight bound from a uniform diagonal covariance bound. |
| `GaussianField.abs_weight_std_le_one` | `LeanGaussianField/WickBound.lean` | Standard-spec Wick weights are bounded by one. |
| `GaussianField.quadraticForm_neg` | `LeanGaussianField/CharExponentFacts.lean` | Negating the test vector leaves the covariance quadratic form unchanged. |
| `GaussianField.GaussianVectorSpec.norm_exp_charExponent_le_one` | `LeanGaussianField/CharExponentFacts.lean` | The target Gaussian characteristic exponential has norm at most one. |
| `GaussianField.GaussianVectorSpec.charExponent_neg` | `LeanGaussianField/CharExponentFacts.lean` | Negating the test vector conjugates the target characteristic exponent. |
| `GaussianField.GaussianVectorSpec.exp_charExponent_neg` | `LeanGaussianField/CharExponentFacts.lean` | The target characteristic exponential has conjugate symmetry under negating the test vector. |
| `GaussianField.GaussianVectorSpec.norm_exp_charExponent_neg` | `LeanGaussianField/CharExponentFacts.lean` | Conjugate symmetry preserves the norm of the target characteristic exponential. |
| `GaussianField.GaussianVectorSpec.exp_charExponent_zero_arg` | `LeanGaussianField/CharExponentFacts.lean` | The target characteristic exponential is normalized at the zero test vector. |
| `GaussianField.GaussianVectorSpec.exp_charExponent_zero_spec` | `LeanGaussianField/CharExponentFacts.lean` | The zero specification has identically one target characteristic exponential. |
| `GaussianField.GaussianVectorSpec.norm_exp_charExponent_zero_arg` | `LeanGaussianField/CharExponentFacts.lean` | The zero-test-vector normalization also rewrites in norm form. |
| `GaussianField.GaussianVectorSpec.norm_exp_charExponent_zero_spec` | `LeanGaussianField/CharExponentFacts.lean` | The zero-specification normalization also rewrites in norm form. |
| `GaussianField.GaussianVectorSpec.charFun_realizationOneDim` | `LeanGaussianField/RealizationOneDim.lean` | One-dimensional Mathlib `gaussianReal` realization matches the target exponent. |
| `GaussianField.GaussianVectorSpec.norm_charFun_realizationOneDim_le_one` | `LeanGaussianField/RealizationOneDim.lean` | The realized one-dimensional characteristic function has norm at most one. |
| `GaussianField.GaussianVectorSpec.charFun_realizationOneDim_zero_arg` | `LeanGaussianField/RealizationOneDim.lean` | The realized one-dimensional characteristic function is normalized at zero. |
| `GaussianField.GaussianVectorSpec.charFun_realizationOneDim_neg` | `LeanGaussianField/RealizationOneDim.lean` | The realized one-dimensional characteristic function has conjugate symmetry under test-vector negation. |
| `GaussianField.GaussianVectorSpec.norm_charFun_realizationOneDim_neg` | `LeanGaussianField/RealizationOneDim.lean` | Conjugate symmetry preserves the norm of the realized one-dimensional characteristic function. |
| `GaussianField.GaussianVectorSpec.norm_charFun_realizationOneDim_zero_arg` | `LeanGaussianField/RealizationOneDim.lean` | The realized one-dimensional characteristic function has norm one at zero. |
| `GaussianField.GaussianVectorSpec.charFun_realizationOneDim_zero_spec` | `LeanGaussianField/RealizationOneDim.lean` | The realized one-dimensional zero specification has identically one characteristic function. |
| `GaussianField.GaussianVectorSpec.norm_charFun_realizationOneDim_zero_spec` | `LeanGaussianField/RealizationOneDim.lean` | The realized one-dimensional zero specification has characteristic-function norm one. |
| `GaussianField.GaussianVectorSpec.exists_realization_fin_one` | `LeanGaussianField/RealizationOneDim.lean` | Existence of the one-dimensional realized law. |
| `GaussianField.GaussianVectorSpec.exists_realization_fin_one_norm_le_one` | `LeanGaussianField/RealizationOneDim.lean` | Existence of the one-dimensional realized law with the characteristic-function norm bound packaged. |
| `GaussianField.GaussianVectorSpec.exists_realization_fin_one_normalized_norm_le_one` | `LeanGaussianField/RealizationOneDim.lean` | Existence of the one-dimensional realized law with zero normalization and the norm bound packaged. |
| `GaussianField.GaussianVectorSpec.exists_realization_fin_one_zero_spec_norm_one` | `LeanGaussianField/RealizationOneDim.lean` | Existence of the one-dimensional zero-specification realized law with identically-one characteristic function and norm-one forms packaged. |

## Explicit hypotheses still carried by interfaces

These are deliberate data fields on `main`, not hidden axioms:

| Name | File | Hypothesis boundary |
| --- | --- | --- |
| `GaussianField.HasGaussianVectorLaw.characteristic_exponent_eq` | `LeanGaussianField/GaussianVector.lean` | A supplied characteristic function matches `spec.charExponent`. |
| `GaussianField.HasGaussianVectorLaw.Uniqueness.eq_of_hasGaussianVectorLaw` | `LeanGaussianField/GaussianVector.lean` | Uniqueness of realized laws from the supplied Gaussian-law witness. |
| `GaussianField.IsserlisInterface.isserlis` | `LeanGaussianField/Interfaces.lean` | Wick/Isserlis moment identity is supplied as interface data. |
| `GaussianField.UniformMomentBoundInterface.coordinate_moment_le` | `LeanGaussianField/Interfaces.lean` | Coordinate moment bounds are supplied for each finite family. |
| `GaussianField.LatticeCovarianceDecayInterface.decay` | `LeanGaussianField/Interfaces.lean` | Finite-lattice covariance decay is supplied as explicit data. |

## Consumption notes

- For small-field covariance bookkeeping, prefer
  `GaussianVectorSpec.diag_nonneg`, `GaussianVectorSpec.abs_covariance_le`,
  and `abs_weight_le_of_diag`.
- For a test oracle on the standard specification, use
  `abs_weight_std_le_one`.
- For one-dimensional realization checks, use
  `GaussianVectorSpec.charFun_realizationOneDim`,
  `GaussianVectorSpec.norm_charFun_realizationOneDim_le_one`,
  `GaussianVectorSpec.charFun_realizationOneDim_zero_arg`,
  `GaussianVectorSpec.charFun_realizationOneDim_neg`,
  `GaussianVectorSpec.norm_charFun_realizationOneDim_neg`,
  `GaussianVectorSpec.norm_charFun_realizationOneDim_zero_arg`,
  `GaussianVectorSpec.charFun_realizationOneDim_zero_spec`,
  `GaussianVectorSpec.norm_charFun_realizationOneDim_zero_spec`, and
  `GaussianVectorSpec.exists_realization_fin_one`.
- For consumers that need both the realized one-dimensional law and the
  characteristic-function norm oracle in one witness, use
  `GaussianVectorSpec.exists_realization_fin_one_norm_le_one`.  If the same
  witness should also carry `charFun μ 0 = 1`, use
  `GaussianVectorSpec.exists_realization_fin_one_normalized_norm_le_one`.
- For the degenerate one-dimensional zero specification as a packaged
  consumer oracle, use
  `GaussianVectorSpec.exists_realization_fin_one_zero_spec_norm_one`.
- For characteristic-function normalization oracles, use
  `GaussianVectorSpec.exp_charExponent_zero_arg` and
  `GaussianVectorSpec.exp_charExponent_zero_spec`.
- For characteristic-function conjugate-symmetry oracles, use
  `GaussianVectorSpec.charExponent_neg`,
  `GaussianVectorSpec.exp_charExponent_neg`, and
  `GaussianVectorSpec.norm_exp_charExponent_neg`.
- For norm-form normalization oracles, use
  `GaussianVectorSpec.norm_exp_charExponent_zero_arg` and
  `GaussianVectorSpec.norm_exp_charExponent_zero_spec`.
- For conditional parent interfaces, use `isserlis_formula`,
  `uniform_coordinate_moment_bound`, and `lattice_covariance_decay` only with
  their corresponding explicit interface witnesses.
