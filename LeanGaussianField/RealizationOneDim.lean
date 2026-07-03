import LeanGaussianField.GaussianVector
import LeanGaussianField.CovarianceBounds
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# One-dimensional realization: the M1 seed on real measures

First measure-theoretic content of the repository: every one-dimensional
Gaussian specification is realized by Mathlib's `gaussianReal`, with the
characteristic function equal to `exp (charExponent)` exactly.  This
discharges the realization pattern of milestone M1 in the smallest case,
using only `charFun_gaussianReal` from the pinned Mathlib (see
`MATHLIB_AUDIT.md`) and `diag_nonneg` proved on `main` this morning.  The
general finite-dimensional realization (product measures plus a
PSD square root) remains the frontier target `exists_gaussian_realization`.

Reference: Kallenberg, 2002, Theorem 5.3, p. 87 (characteristic functions
identify finite-dimensional Gaussian laws).
-/

namespace GaussianField

namespace GaussianVectorSpec

open MeasureTheory ProbabilityTheory

/-- The Mathlib Gaussian measure realizing a one-dimensional
specification: mean `m 0`, variance `C 0 0` (nonnegative by `diag_nonneg`). -/
noncomputable def realizationOneDim (spec : GaussianVectorSpec (Fin 1)) :
    Measure ℝ :=
  gaussianReal (spec.mean 0) ⟨spec.covariance 0 0, spec.diag_nonneg 0⟩

instance (spec : GaussianVectorSpec (Fin 1)) :
    IsProbabilityMeasure spec.realizationOneDim := by
  unfold realizationOneDim
  infer_instance

/-- **The bridge to Mathlib's Gaussian.**  The characteristic function of
the realizing measure is exactly the exponential of the specification's
characteristic exponent. -/
theorem charFun_realizationOneDim (spec : GaussianVectorSpec (Fin 1))
    (t : Fin 1 → ℝ) :
    charFun spec.realizationOneDim (t 0)
      = Complex.exp (spec.charExponent t) := by
  unfold realizationOneDim
  rw [charFun_gaussianReal]
  congr 1
  simp only [charExponent, quadraticForm, Fin.sum_univ_one, NNReal.coe_mk]
  push_cast
  ring

/-- Existence form: every one-dimensional Gaussian specification is realized
by a probability measure on `ℝ` whose characteristic function is
`exp (charExponent)`.  Smallest-case discharge of the M1 realization
pattern; the frontier keeps the general statement. -/
theorem exists_realization_fin_one (spec : GaussianVectorSpec (Fin 1)) :
    ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧
      ∀ t : Fin 1 → ℝ, charFun μ (t 0) = Complex.exp (spec.charExponent t) :=
  ⟨spec.realizationOneDim, inferInstance,
    fun t => spec.charFun_realizationOneDim t⟩

end GaussianVectorSpec

end GaussianField
