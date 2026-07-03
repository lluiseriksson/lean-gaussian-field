import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Complex.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace

/-!
# Finite-dimensional Gaussian specifications

This file records finite-dimensional Gaussian laws through their characteristic
function.  Existence and identification with Mathlib's characteristic function
are not asserted here; realizations are carried explicitly.
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

end GaussianVectorSpec

/-- A measure realizes a finite-dimensional Gaussian specification.

Reference: Kallenberg, 2002, Theorem 5.3, p. 87, for uniqueness of probability
laws from characteristic functions.  The actual identification with Mathlib's
`charFun` is a future theorem; for now the characteristic function is supplied
as explicit data.
-/
structure HasGaussianVectorLaw [Fintype ι] [MeasurableSpace (ι → ℝ)]
    (spec : GaussianVectorSpec ι) (μ : Measure (ι → ℝ))
    (characteristic : (ι → ℝ) → ℂ) : Prop where
  characteristic_exponent_eq :
    ∀ t : ι → ℝ, characteristic t = spec.charExponent t

namespace HasGaussianVectorLaw

variable [Fintype ι]

/-- Explicit uniqueness hypothesis for realized finite-dimensional Gaussian laws.

This is a frontier hypothesis on `main`, not an axiom.
-/
structure Uniqueness [MeasurableSpace (ι → ℝ)] (spec : GaussianVectorSpec ι) : Prop where
  eq_of_hasGaussianVectorLaw :
    ∀ {μ ν : Measure (ι → ℝ)} {χμ χν : (ι → ℝ) → ℂ},
      HasGaussianVectorLaw spec μ χμ → HasGaussianVectorLaw spec ν χν → μ = ν

/-- Uniqueness wrapper, conditional on `HasGaussianVectorLaw.Uniqueness`. -/
protected theorem ext [MeasurableSpace (ι → ℝ)] {spec : GaussianVectorSpec ι}
    (h : Uniqueness spec) {μ ν : Measure (ι → ℝ)}
    {χμ χν : (ι → ℝ) → ℂ}
    (hμ : HasGaussianVectorLaw spec μ χμ) (hν : HasGaussianVectorLaw spec ν χν) :
    μ = ν := by
  exact h.eq_of_hasGaussianVectorLaw hμ hν

end HasGaussianVectorLaw

end GaussianField
