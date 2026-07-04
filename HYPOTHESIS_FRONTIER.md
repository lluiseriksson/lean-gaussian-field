# Hypothesis frontier

Branch: `main`

## Lean placeholders

- No `.lean` placeholders are present on `main`.
- CI rejects `sorry` and `admit` in `.lean` files on `main`.
- Statement-first obligations live on `frontier/M1` under
  `LeanGaussianField/Frontier/` and are listed below.

## Explicit hypotheses carried by interfaces

- `GaussianField.GaussianVectorSpec.covariance_psd`: covariance data must be
  supplied with a positive-semidefinite proof.
- `GaussianField.HasGaussianVectorLaw.characteristic_exponent_eq`:
  existence/realization of the finite-dimensional Gaussian law, and its
  identification with the target characteristic exponent, are explicit data.
- `GaussianField.HasGaussianVectorLaw.Uniqueness.eq_of_hasGaussianVectorLaw`:
  uniqueness of realized Gaussian vector laws is an explicit hypothesis.
- `GaussianField.IsserlisInterface.isserlis`: the Wick/Isserlis moment identity
  is not yet proved in `main`; the moment functional is explicit data.
- `GaussianField.UniformMomentBoundInterface.coordinate_moment_le`: uniform
  moment bounds are not yet proved in `main`; coordinate moments and the bound
  are explicit data for each finite family.
- `GaussianField.LatticeCovarianceDecayInterface.decay`: finite-lattice
  covariance decay is not yet proved in `main`; mass, amplitude, covariance,
  decay profile, and decay estimate are explicit data.

## Closed facts on `main`

M0 layer (previous iteration):

- `GaussianVectorSpec.zero`, `charExponent_zero_arg`, `charExponent_zero_spec`.

Covariance layer (`CovarianceBounds.lean`):

- `bilinForm`, `bilinForm_self`, `bilinForm_add_left`, `bilinForm_add_right`,
  `bilinForm_single`, `quadraticForm_single_add_single`: bilinear expansion of
  the covariance form on coordinate vectors.
- `GaussianVectorSpec.diag_nonneg`: PSD forces a nonnegative diagonal.
- `GaussianVectorSpec.covariance_sq_le`,
  `GaussianVectorSpec.abs_covariance_le`: Cauchy-Schwarz — every covariance
  entry is bounded by the diagonal (discriminant argument).
- `GaussianVectorSpec.std`: the standard specification, with proved PSD.

Pairing layer (`PairingLemmas.lean`):

- `Pairing.ext`, `DecidableEq (Pairing ι)`, `Fintype (Pairing ι)`:
  pairings form a finite type, so Wick sums over ALL pairings are `Finset`
  sums with no auxiliary data.
- `Pairing.two_mul_card_pairs`: double counting, `2 * #pairs = card ι`.
- `Pairing.even_card`, `Pairing.isEmpty_of_odd_card`: parity obstruction.
- `Pairing.empty`, `Pairing.weight_empty`: the empty pairing has weight 1.
- `Pairing.abs_weight_eq`, `Pairing.abs_weight_le_pow`: Wick-weight bounds.

Characteristic-exponent layer (`CharExponentFacts.lean`):

- `quadraticForm_neg`, `charExponent_eq`, `charExponent_re`,
  `charExponent_im`, `charExponent_re_nonpos`,
  `norm_exp_charExponent_le_one`, `charExponent_neg`,
  `exp_charExponent_neg`, `norm_exp_charExponent_neg`,
  `exp_charExponent_zero_arg`, `exp_charExponent_zero_spec`,
  `norm_exp_charExponent_zero_arg`, `norm_exp_charExponent_zero_spec`: the
  target characteristic exponential of any specification is bounded by one,
  has conjugate symmetry under test-vector negation, and the zero-argument /
  zero-spec normalization oracles reduce to one, also in norm form.

M2 seed (`WickBound.lean`):

- `abs_weight_le_of_diag`: |Wick weight| ≤ (sup diagonal)^{#pairs}, uniform in
  the dimension.  `abs_weight_std_le_one` as consumer test.

## Frontier obligations (branch `frontier/M1`, statement-first, sorried)

- `exists_gaussian_realization`: construction of the law from arbitrary PSD
  covariance, via Mathlib `isGaussian_iff_gaussian_charFun` (see
  MATHLIB_AUDIT.md).
- `isserlis_of_realization`: Wick/Isserlis over `Fintype (Pairing ι)`.
- `integral_prod_eq_zero_of_odd`: vanishing odd moments (consumer test).
- `card_pairing_fin`: #pairings of 2n points = (2n-1)!!.
- `massiveMatrix_posDef`, `massiveMatrix_isUnit`,
  `massiveMatrix_inv_posSemidef`, `massiveMatrix_inv_decay`: massive lattice
  free field; decay constants still existential — MUST become explicit
  (A = m⁻², r = log(1 + m²/‖L‖)) before closing M3.

## Distance to the target

The dimension-uniform control chain diagonal → Cauchy-Schwarz → Wick-weight
bound is now proved unconditionally.  What separates `main` from closing M1 is
purely the analytic realization block (existence of the law and the
differentiation-of-characteristic-function argument for Isserlis); the
combinatorial side (finiteness of pairings, parity, counting up to the
(2n-1)!! identity) is done or reduced to `card_pairing_fin`.


## Second push (2026-07-03, afternoon control pass) — merged to main

`RealizationOneDim.lean`:

- `realizationOneDim`: every one-dimensional specification is realized by
  Mathlib's `gaussianReal`, variance fed by `diag_nonneg` (proved this
  morning, merged to `main`).
- `charFun_realizationOneDim`: **the bridge to Mathlib's Gaussian** —
  `charFun` of the realizing measure equals `exp (charExponent)` exactly
  (via `charFun_gaussianReal` at the pin; see `MATHLIB_AUDIT.md`).
- `norm_charFun_realizationOneDim_le_one`: norm bound for the realized
  one-dimensional characteristic function, routed through the closed
  exponent bound `norm_exp_charExponent_le_one`.
- `charFun_realizationOneDim_zero_arg`,
  `charFun_realizationOneDim_neg`,
  `norm_charFun_realizationOneDim_zero_arg`: closed normalization and
  conjugate-symmetry oracles for the realized one-dimensional characteristic
  function.
- `exists_realization_fin_one`: smallest-case discharge of the M1
  realization pattern. The general `exists_gaussian_realization`
  (product measures + PSD square root) remains on `frontier/M1`.

First measure-theoretic content of the repository.
