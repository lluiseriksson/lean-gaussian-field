import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Complex.Basic
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

/-!
# Finite-dimensional Gaussian specifications

This file specifies finite-dimensional Gaussian probability laws using Mathlib's
actual dual characteristic function. Uniqueness is proved below. General existence
is not asserted; the zero-covariance Dirac realization is checked explicitly.
-/

open scoped BigOperators
open MeasureTheory

namespace GaussianField

variable {ι : Type*}

/-- Quadratic form associated to a covariance kernel on a finite index set. -/
noncomputable def quadraticForm [Fintype ι] (covariance : ι → ι → ℝ)
    (t : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, t i * covariance i j * t j

/-- Mean/covariance data for a finite-dimensional Gaussian candidate.

The positive-semidefinite condition is explicit data.  This structure does not
claim that a measure with this characteristic function has been constructed.
-/
structure GaussianVectorSpec (ι : Type*) [Fintype ι] where
  mean : ι → ℝ
  covariance : ι → ι → ℝ
  covariance_symm : ∀ i j, covariance i j = covariance j i
  covariance_psd : ∀ t : ι → ℝ, 0 ≤ quadraticForm covariance t

namespace GaussianVectorSpec

variable [Fintype ι]

/-- The exponent `i <t,m> - (1/2) t C t` of the target characteristic
function for finite-dimensional Gaussian data.
-/
noncomputable def charExponent (spec : GaussianVectorSpec ι) (t : ι → ℝ) : ℂ :=
  (((∑ i, t i * spec.mean i : ℝ) : ℂ) * Complex.I)
    - (((quadraticForm spec.covariance t : ℝ) : ℂ) / 2)

/-- The degenerate centered Gaussian specification with zero covariance.

Reference: Kallenberg, 2002, Theorem 5.3, p. 87, for the finite-dimensional
characteristic-function convention used by the surrounding M0 interface.
-/
noncomputable def zero (ι : Type*) [Fintype ι] : GaussianVectorSpec ι where
  mean := fun _ => 0
  covariance := fun _ _ => 0
  covariance_symm := by
    intro i j
    rfl
  covariance_psd := by
    intro t
    simp [quadraticForm]

/-- The characteristic exponent of any Gaussian specification is zero at the
origin.

Reference: Kallenberg, 2002, Theorem 5.3, p. 87, for characteristic functions
as the finite-dimensional law identifier.
-/
@[simp]
theorem charExponent_zero_arg (spec : GaussianVectorSpec ι) :
    spec.charExponent (fun _ => 0) = 0 := by
  simp [charExponent, quadraticForm]

/-- The degenerate zero specification has identically zero characteristic
exponent.

Reference: Kallenberg, 2002, Theorem 5.3, p. 87, for the finite-dimensional
characteristic-function convention used by the surrounding M0 interface.
-/
@[simp]
theorem charExponent_zero_spec (t : ι → ℝ) :
    (zero ι).charExponent t = 0 := by
  simp [zero, charExponent, quadraticForm]

end GaussianVectorSpec

/-- Coordinates of a continuous real linear functional in the standard finite basis. -/
noncomputable def dualCoordinates [Fintype ι]
    (L : StrongDual ℝ (ι → ℝ)) : ι → ℝ := by
  classical
  exact fun i => L (Pi.single i 1)

/-- The dual convention is exactly the finite dot-product convention. -/
theorem dualCoordinates_apply [Fintype ι] (L : StrongDual ℝ (ι → ℝ)) (x : ι → ℝ) :
    L x = ∑ i, dualCoordinates L i * x i := by
  classical
  have hx : (∑ i, x i • (Pi.single i (1 : ℝ) : ι → ℝ)) = x := by
    ext j
    simp [Pi.single_apply]
  calc
    L x = L (∑ i, x i • (Pi.single i (1 : ℝ) : ι → ℝ)) := congrArg L hx.symm
    _ = ∑ i, dualCoordinates L i * x i := by
      simp [dualCoordinates, map_sum, map_smul, mul_comm]

/-- A probability measure realizes the specification when its actual characteristic
function is the exponential of the specified exponent. PSD, including singular
covariances, remains the only covariance assumption in GaussianVectorSpec. -/
structure HasGaussianVectorLaw [Fintype ι]
    (spec : GaussianVectorSpec ι) (μ : Measure (ι → ℝ)) : Prop where
  probability : IsProbabilityMeasure μ
  characteristic_eq : ∀ L : StrongDual ℝ (ι → ℝ),
    charFunDual μ L = Complex.exp (spec.charExponent (dualCoordinates L))

namespace HasGaussianVectorLaw

variable [Fintype ι]

/-- Actual uniqueness of finite Gaussian probability laws; no external uniqueness
hypothesis or supplied characteristic-function surrogate is used. -/
protected theorem ext {spec : GaussianVectorSpec ι} {μ ν : Measure (ι → ℝ)}
    (hμ : HasGaussianVectorLaw spec μ) (hν : HasGaussianVectorLaw spec ν) :
    μ = ν := by
  letI := hμ.probability
  letI := hν.probability
  apply Measure.ext_of_charFunDual
  funext L
  exact (hμ.characteristic_eq L).trans (hν.characteristic_eq L).symm

/-- The singular zero-covariance case is admitted by the repaired contract. -/
theorem zero_dirac :
    HasGaussianVectorLaw (GaussianVectorSpec.zero ι) (Measure.dirac (0 : ι → ℝ)) := by
  constructor
  · infer_instance
  · intro L
    simp [charFunDual_dirac]

end HasGaussianVectorLaw

end GaussianField
