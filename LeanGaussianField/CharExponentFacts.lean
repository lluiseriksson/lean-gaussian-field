import LeanGaussianField.GaussianVector
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Analytic facts about the Gaussian characteristic exponent

Real/imaginary decomposition of `charExponent`, nonpositivity of its real
part, and the resulting bound `‖exp (charExponent t)‖ ≤ 1`: the target
characteristic function of any Gaussian specification is bounded by one, as a
characteristic function must be.

Reference: Kallenberg, 2002, "Foundations of Modern Probability", Lemma 5.1,
p. 84, for `|φ| ≤ 1`.
-/

open scoped BigOperators

namespace GaussianField

namespace GaussianVectorSpec

variable {ι : Type*} [Fintype ι]

/-- Normal form of the characteristic exponent. -/
theorem charExponent_eq (spec : GaussianVectorSpec ι) (t : ι → ℝ) :
    spec.charExponent t
      = Complex.I * ((∑ i, t i * spec.mean i : ℝ) : ℂ)
        - ((quadraticForm spec.covariance t / 2 : ℝ) : ℂ) := by
  unfold charExponent
  push_cast
  ring

/-- The real part of the characteristic exponent is minus half the quadratic
form. -/
@[simp] theorem charExponent_re (spec : GaussianVectorSpec ι) (t : ι → ℝ) :
    (spec.charExponent t).re = -(quadraticForm spec.covariance t / 2) := by
  rw [charExponent_eq]
  simp [Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im]

/-- The imaginary part of the characteristic exponent is the mean pairing. -/
@[simp] theorem charExponent_im (spec : GaussianVectorSpec ι) (t : ι → ℝ) :
    (spec.charExponent t).im = ∑ i, t i * spec.mean i := by
  rw [charExponent_eq]
  simp [Complex.sub_im, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im]

/-- Positive semidefiniteness forces a nonpositive real part. -/
theorem charExponent_re_nonpos (spec : GaussianVectorSpec ι) (t : ι → ℝ) :
    (spec.charExponent t).re ≤ 0 := by
  rw [charExponent_re]
  have h := spec.covariance_psd t
  linarith

/-- The target characteristic function is bounded by one. -/
theorem norm_exp_charExponent_le_one (spec : GaussianVectorSpec ι)
    (t : ι → ℝ) :
    ‖Complex.exp (spec.charExponent t)‖ ≤ 1 := by
  rw [Complex.norm_exp]
  calc Real.exp (spec.charExponent t).re
      ≤ Real.exp 0 := Real.exp_le_exp.mpr (spec.charExponent_re_nonpos t)
    _ = 1 := Real.exp_zero

/-- The target characteristic exponential is normalized at the zero test
vector. -/
@[simp] theorem exp_charExponent_zero_arg (spec : GaussianVectorSpec ι) :
    Complex.exp (spec.charExponent fun _ => 0) = 1 := by
  simp

/-- The target characteristic exponential of the zero specification is
identically one. -/
@[simp] theorem exp_charExponent_zero_spec (t : ι → ℝ) :
    Complex.exp ((GaussianVectorSpec.zero ι).charExponent t) = 1 := by
  simp

end GaussianVectorSpec

end GaussianField
