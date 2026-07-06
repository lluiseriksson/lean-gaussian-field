# Mother-facing digest

Date: 2026-07-06

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
| `GaussianField.GaussianVectorSpec.covariance_eq_zero_of_diag_left` | `LeanGaussianField/CovarianceBounds.lean` | If a PSD covariance has zero diagonal at `i`, all row entries `C i j` vanish. |
| `GaussianField.GaussianVectorSpec.covariance_eq_zero_of_diag_right` | `LeanGaussianField/CovarianceBounds.lean` | If a PSD covariance has zero diagonal at `j`, all column entries `C i j` vanish. |
| `GaussianField.GaussianVectorSpec.std` | `LeanGaussianField/CovarianceBounds.lean` | Standard centered finite Gaussian specification data. |
| `GaussianField.GaussianVectorSpec.std_mean` | `LeanGaussianField/CovarianceBounds.lean` | The standard specification is centered, exposed as a direct rewrite. |
| `GaussianField.GaussianVectorSpec.std_covariance` | `LeanGaussianField/CovarianceBounds.lean` | Standard-spec covariance rewrites directly to the identity kernel. |
| `GaussianField.GaussianVectorSpec.std_covariance_self` | `LeanGaussianField/CovarianceBounds.lean` | Standard-spec diagonal covariance rewrites to one. |
| `GaussianField.GaussianVectorSpec.std_covariance_of_ne` | `LeanGaussianField/CovarianceBounds.lean` | Standard-spec off-diagonal covariance entries vanish from an inequality proof. |
| `GaussianField.Pairing.weight_empty` | `LeanGaussianField/PairingLemmas.lean` | Empty Wick pairing has weight one. |
| `GaussianField.Pairing.card_pairs_eq_card_div_two` | `LeanGaussianField/PairingLemmas.lean` | A pairing has exactly `Fintype.card ι / 2` edges. |
| `GaussianField.Pairing.pairs_nonempty_iff_nonempty` | `LeanGaussianField/PairingLemmas.lean` | A pairing has at least one edge exactly when the index type is nonempty. |
| `GaussianField.Pairing.card_pairs_pos_iff_nonempty` | `LeanGaussianField/PairingLemmas.lean` | A pairing has positive edge count exactly when the index type is nonempty. |
| `GaussianField.Pairing.card_pairs_eq_zero_iff_not_nonempty` | `LeanGaussianField/PairingLemmas.lean` | A pairing has zero edges exactly when the index type is empty. |
| `GaussianField.Pairing.pairs_empty_iff_isEmpty` | `LeanGaussianField/PairingLemmas.lean` | A pairing has no edges exactly when the index type carries an `IsEmpty` witness. |
| `GaussianField.Pairing.card_pairs_eq_zero_iff_isEmpty` | `LeanGaussianField/PairingLemmas.lean` | A pairing has zero edge count exactly when the index type carries an `IsEmpty` witness. |
| `GaussianField.Pairing.weight_eq_zero_of_mem` | `LeanGaussianField/PairingLemmas.lean` | Any zero covariance factor on a pairing edge forces the full Wick weight to vanish. |
| `GaussianField.Pairing.abs_weight_le_pow` | `LeanGaussianField/PairingLemmas.lean` | Pairing-weight bound from per-edge covariance bounds. |
| `GaussianField.abs_weight_le_of_diag` | `LeanGaussianField/WickBound.lean` | Wick-weight bound from a uniform diagonal covariance bound. |
| `GaussianField.weight_eq_zero_of_diag_left` | `LeanGaussianField/WickBound.lean` | If a paired left endpoint has zero diagonal covariance, the associated Wick weight vanishes. |
| `GaussianField.weight_eq_zero_of_diag_right` | `LeanGaussianField/WickBound.lean` | If a paired right endpoint has zero diagonal covariance, the associated Wick weight vanishes. |
| `GaussianField.weight_std_eq_zero_of_mem` | `LeanGaussianField/WickBound.lean` | In the standard specification, a chosen pairing edge forces the full Wick weight to vanish. |
| `GaussianField.weight_std_eq_zero_of_nonempty` | `LeanGaussianField/WickBound.lean` | In the standard specification, every nonempty pairing has zero Wick weight. |
| `GaussianField.weight_std_eq_one_of_pairs_empty` | `LeanGaussianField/WickBound.lean` | In the standard specification, an empty pairing has Wick weight one. |
| `GaussianField.weight_std_eq_if_pairs_empty` | `LeanGaussianField/WickBound.lean` | Standard-spec Wick weight as the empty-pairing indicator: `1` for empty pairings, `0` otherwise. |
| `GaussianField.weight_std_nonneg` | `LeanGaussianField/WickBound.lean` | Standard-spec Wick weights are nonnegative. |
| `GaussianField.weight_std_le_one` | `LeanGaussianField/WickBound.lean` | Standard-spec Wick weights are bounded above by one. |
| `GaussianField.weight_std_eq_zero_iff_pairs_nonempty` | `LeanGaussianField/WickBound.lean` | Standard-spec Wick weight vanishes exactly for nonempty pairings. |
| `GaussianField.weight_std_eq_one_iff_pairs_empty` | `LeanGaussianField/WickBound.lean` | Standard-spec Wick weight is one exactly for empty pairings. |
| `GaussianField.weight_std_eq_zero_iff_nonempty` | `LeanGaussianField/WickBound.lean` | Standard-spec Wick weight vanishes exactly when the index type is nonempty. |
| `GaussianField.weight_std_eq_one_iff_not_nonempty` | `LeanGaussianField/WickBound.lean` | Standard-spec Wick weight is one exactly when the index type is empty. |
| `GaussianField.weight_std_eq_zero_of_index_nonempty` | `LeanGaussianField/WickBound.lean` | Standard-spec Wick weight vanishes when `[Nonempty ι]` is available. |
| `GaussianField.weight_std_eq_one_of_index_isEmpty` | `LeanGaussianField/WickBound.lean` | Standard-spec Wick weight is one when `[IsEmpty ι]` is available. |
| `GaussianField.weight_std_eq_one_iff_isEmpty` | `LeanGaussianField/WickBound.lean` | Standard-spec Wick weight is one exactly when the index type carries an `IsEmpty` witness. |
| `GaussianField.weight_std_ne_zero_iff_isEmpty` | `LeanGaussianField/WickBound.lean` | Standard-spec Wick weight is nonzero exactly when the index type carries an `IsEmpty` witness. |
| `GaussianField.abs_weight_std_eq_zero_iff_nonempty` | `LeanGaussianField/WickBound.lean` | Standard-spec Wick weight has magnitude zero exactly when the index type is nonempty. |
| `GaussianField.abs_weight_std_eq_one_iff_isEmpty` | `LeanGaussianField/WickBound.lean` | Standard-spec Wick weight has magnitude one exactly when the index type carries an `IsEmpty` witness. |
| `GaussianField.abs_weight_std_eq_zero_of_index_nonempty` | `LeanGaussianField/WickBound.lean` | Standard-spec Wick weight has magnitude zero when `[Nonempty ι]` is available. |
| `GaussianField.abs_weight_std_eq_one_of_index_isEmpty` | `LeanGaussianField/WickBound.lean` | Standard-spec Wick weight has magnitude one when `[IsEmpty ι]` is available. |
| `GaussianField.abs_weight_std_eq_if_pairs_empty` | `LeanGaussianField/WickBound.lean` | Standard-spec Wick weight magnitude as the empty-pairing indicator. |
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
| `GaussianField.GaussianVectorSpec.exists_realization_fin_one_normalized_symmetric_norm_le_one` | `LeanGaussianField/RealizationOneDim.lean` | Existence of the one-dimensional realized law with zero normalization, conjugate symmetry, and the norm bound packaged. |
| `GaussianField.GaussianVectorSpec.exists_realization_fin_one_zero_spec_norm_one` | `LeanGaussianField/RealizationOneDim.lean` | Existence of the one-dimensional zero-specification realized law with identically-one characteristic function and norm-one forms packaged. |
| `GaussianField.GaussianVectorSpec.exists_realization_fin_one_zero_spec_symmetric_norm_one` | `LeanGaussianField/RealizationOneDim.lean` | Existence of the one-dimensional zero-specification realized law with identically-one characteristic function, conjugate symmetry, and norm-one forms packaged. |

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
  `GaussianVectorSpec.covariance_eq_zero_of_diag_left`,
  `GaussianVectorSpec.covariance_eq_zero_of_diag_right`, and
  `abs_weight_le_of_diag`.  For direct rewriting under the standard
  specification, use `GaussianVectorSpec.std_mean`,
  `GaussianVectorSpec.std_covariance`, `GaussianVectorSpec.std_covariance_self`,
  and `GaussianVectorSpec.std_covariance_of_ne` instead of unfolding
  `GaussianVectorSpec.std`.
- For Wick terms containing a degenerate covariance edge, use
  `Pairing.weight_eq_zero_of_mem`; if the zero comes from a paired zero
  diagonal, use `weight_eq_zero_of_diag_left` or
  `weight_eq_zero_of_diag_right`.
- For pairing cardinality normalization, use
  `Pairing.card_pairs_eq_card_div_two` to rewrite the number of Wick edges as
  half the number of indices.  Use `Pairing.pairs_nonempty_iff_nonempty` when
  a consumer wants to replace pairing nonemptiness by index-type nonemptiness.
  Use `Pairing.card_pairs_pos_iff_nonempty` or
  `Pairing.card_pairs_eq_zero_iff_not_nonempty` when the consumer works with
  `P.pairs.card` directly.  Use `Pairing.pairs_empty_iff_isEmpty` or
  `Pairing.card_pairs_eq_zero_iff_isEmpty` when the consumer already has an
  `IsEmpty ι` witness or wants to produce one from pairing emptiness.
- For a test oracle on the standard specification, use
  `weight_std_eq_zero_of_mem` when a specific edge is known,
  `weight_std_eq_zero_of_nonempty` when the pairing is known nonempty,
  `weight_std_eq_one_of_pairs_empty` when the pairing has no edges, and
  `weight_std_eq_if_pairs_empty` when the consumer wants the single
  empty/nonempty case split.  Use `weight_std_nonneg` and
  `weight_std_le_one` when the consumer only needs signed interval control
  for a standard Wick term.  Use `weight_std_eq_zero_iff_pairs_nonempty`
  when a zero-weight standard Wick term should be converted back to
  pairing nonemptiness, `weight_std_eq_one_iff_pairs_empty` when a
  unit-weight standard Wick term should be converted back to pairing
  emptiness, and `weight_std_eq_zero_iff_nonempty` when the consumer wants
  the equivalent nonempty index-type condition.  Use
  `weight_std_eq_one_iff_not_nonempty` when a unit-weight standard Wick term
  should be converted directly to emptiness of the index type.  Use
  `weight_std_eq_zero_of_index_nonempty` or
  `weight_std_eq_one_of_index_isEmpty` when the index-type instance is already
  in the local context and a direct rewrite is preferable.  Use
  `weight_std_eq_one_iff_isEmpty` when the consumer wants to exchange a
  unit-weight standard Wick term with an explicit `IsEmpty ι` witness.  Use
  `weight_std_ne_zero_iff_isEmpty` when the consumer tracks nonzero standard
  Wick weights rather than the exact value `1`.  Use
  `abs_weight_std_eq_zero_iff_nonempty` when the consumer tracks vanishing
  absolute value and wants to detect nonempty index types.  Use
  `abs_weight_std_eq_one_iff_isEmpty` when the consumer tracks saturated
  absolute value rather than signed value.  Use
  `abs_weight_std_eq_if_pairs_empty` when the consumer wants one direct
  empty/nonempty case split for the absolute standard Wick weight.  Use
  `abs_weight_std_eq_zero_of_index_nonempty` or
  `abs_weight_std_eq_one_of_index_isEmpty` when the relevant index-type
  instance is already in context and the consumer wants a direct absolute
  rewrite.  Use `abs_weight_std_le_one` for the uniform absolute-value bound.
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
  If it should also carry conjugate symmetry under test-vector negation, use
  `GaussianVectorSpec.exists_realization_fin_one_normalized_symmetric_norm_le_one`.
- For the degenerate one-dimensional zero specification as a packaged
  consumer oracle, use
  `GaussianVectorSpec.exists_realization_fin_one_zero_spec_norm_one`.
  If the same zero-specification witness should also carry conjugate symmetry,
  use
  `GaussianVectorSpec.exists_realization_fin_one_zero_spec_symmetric_norm_one`.
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
