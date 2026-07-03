import LeanGaussianField.GaussianVector
import LeanGaussianField.PairingLemmas
import LeanGaussianField.CovarianceBounds
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Frontier: milestone M1 statement surface

Statement-first targets for M1.  Every `sorry` in this file is a frontier
obligation tracked in `HYPOTHESIS_FRONTIER.md`; this file must NEVER be merged
to `main`.

References: Isserlis, 1918, formula (1), p. 136; Janson, 1997, Theorem 1.28,
p. 22; Kallenberg, 2002, Theorem 5.3, p. 87.
-/

open scoped BigOperators Nat
open MeasureTheory

namespace GaussianField

variable {ι : Type*} [Fintype ι]

/-- Existence and characteristic-function identification of the law of a
finite-dimensional Gaussian specification.  Mathlib route (per
MATHLIB_AUDIT.md): `isGaussian_iff_gaussian_charFun` on
`EuclideanSpace ℝ ι`, transported to the pi type. -/
theorem exists_gaussian_realization (spec : GaussianVectorSpec ι) :
    ∃ μ : Measure (ι → ℝ), IsProbabilityMeasure μ ∧
      ∀ t : ι → ℝ,
        (∫ x, Complex.exp (Complex.I * ((∑ i, t i * x i : ℝ) : ℂ)) ∂μ)
          = Complex.exp (spec.charExponent t) := by
  sorry

/-- Isserlis/Wick for a realized centered Gaussian family: the full mixed
moment is the sum of Wick weights over all pairings of the index set.  The
sum ranges over the `Fintype` instance from `PairingLemmas`. -/
theorem isserlis_of_realization [DecidableEq ι] [LinearOrder ι]
    (spec : GaussianVectorSpec ι) (hmean : ∀ i, spec.mean i = 0)
    (μ : Measure (ι → ℝ)) [IsProbabilityMeasure μ]
    (hchar : ∀ t : ι → ℝ,
      (∫ x, Complex.exp (Complex.I * ((∑ i, t i * x i : ℝ) : ℂ)) ∂μ)
        = Complex.exp (spec.charExponent t))
    (hint : Integrable (fun x : ι → ℝ => ∏ i, x i) μ) :
    (∫ x, ∏ i, x i ∂μ)
      = ∑ π : Pairing ι, π.weight spec.covariance := by
  sorry

/-- Odd centered moments vanish: with no pairing available the Wick sum is
empty.  Follows from `isserlis_of_realization` plus
`Pairing.isEmpty_of_odd_card`; stated separately as the first consumer test
of the M1 interface. -/
theorem integral_prod_eq_zero_of_odd [DecidableEq ι] [LinearOrder ι]
    (spec : GaussianVectorSpec ι) (hmean : ∀ i, spec.mean i = 0)
    (hodd : ¬ Even (Fintype.card ι))
    (μ : Measure (ι → ℝ)) [IsProbabilityMeasure μ]
    (hchar : ∀ t : ι → ℝ,
      (∫ x, Complex.exp (Complex.I * ((∑ i, t i * x i : ℝ) : ℂ)) ∂μ)
        = Complex.exp (spec.charExponent t))
    (hint : Integrable (fun x : ι → ℝ => ∏ i, x i) μ) :
    (∫ x, ∏ i, x i ∂μ) = 0 := by
  sorry

/-- The pairing count: `(2n)!! ... = (2n-1)!!` pairings of `2n` points.
Needed to convert Wick sums into the classical `(2k-1)!! σ^{2k}` moment
formulas of milestone M2. -/
theorem card_pairing_fin (n : ℕ) :
    Fintype.card (Pairing (Fin (2 * n))) = (2 * n - 1)‼ := by
  sorry

end GaussianField
