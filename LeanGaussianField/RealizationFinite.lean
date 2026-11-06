import LeanGaussianField.GaussianVector
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.Matrix.Order

/-! Finite Gaussian realization by a PSD square root, a product of standard
Gaussians, and translation. Singular covariance and empty index types are allowed.
This constructs the existing characteristic-function law; it proves no moment formula. -/

open scoped BigOperators Matrix MatrixOrder
open MeasureTheory ProbabilityTheory Matrix

namespace GaussianField
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem spec_posSemidef (spec : GaussianVectorSpec ι) :
    Matrix.PosSemidef spec.covariance := by
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  constructor
  · ext i j
    simpa using spec.covariance_symm j i
  · intro x
    simpa [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc, quadraticForm]
      using spec.covariance_psd x

noncomputable def matrixMap (B : Matrix ι ι ℝ) : (ι → ℝ) →L[ℝ] (ι → ℝ) :=
  ContinuousLinearMap.pi (fun i => ∑ j, B i j • ContinuousLinearMap.proj j)

theorem matrixMap_apply (B : Matrix ι ι ℝ) (x : ι → ℝ) (i : ι) :
    matrixMap B x i = ∑ j, B i j * x j := by
  simp [matrixMap]

theorem dual_matrixMap (B : Matrix ι ι ℝ) (L : StrongDual ℝ (ι → ℝ)) (j : ι) :
    dualCoordinates (L.comp (matrixMap B)) j = ∑ i, dualCoordinates L i * B i j := by
  rw [dualCoordinates, ContinuousLinearMap.comp_apply, dualCoordinates_apply]
  simp [matrixMap_apply, Pi.single_apply]

theorem gram_identity (B : Matrix ι ι ℝ) (t : ι → ℝ) :
    (∑ j, (∑ i, t i * B i j)^2) = quadraticForm (B * B.transpose) t := by
  simp only [quadraticForm, Matrix.mul_apply, Matrix.transpose_apply, pow_two,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem standard_charFunDual_real (L : StrongDual ℝ ℝ) :
    charFunDual (gaussianReal 0 1) L = Complex.exp (-((L 1 : ℝ) : ℂ)^2 / 2) := by
  have hx (x : ℝ) : L x = x * L 1 := by
    simpa using L.map_smul x (1 : ℝ)
  calc
    charFunDual (gaussianReal 0 1) L = charFun (gaussianReal 0 1) (L 1) := by
      rw [charFunDual_apply, charFun_apply_real]
      congr 1
      funext x
      rw [hx x]
      simp [mul_comm]
    _ = _ := by simp [charFun_gaussianReal, neg_div]

noncomputable def standardPi : Measure (ι → ℝ) := Measure.pi (fun _ => gaussianReal 0 1)

instance : IsProbabilityMeasure (standardPi (ι := ι)) := by
  unfold standardPi
  infer_instance

theorem standardPi_charFunDual (L : StrongDual ℝ (ι → ℝ)) :
    charFunDual standardPi L = Complex.exp (-(∑ i, (dualCoordinates L i : ℂ)^2) / 2) := by
  rw [standardPi, charFunDual_pi]
  simp_rw [standard_charFunDual_real]
  rw [← Complex.exp_sum]
  congr 1
  simp only [dualCoordinates, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.single_apply]
  rw [← Finset.sum_div, ← Finset.sum_neg_distrib]
  congr 2
  funext i
  congr 4
  ext j
  simp [Pi.single_apply]

theorem exists_law_of_factor (spec : GaussianVectorSpec ι) (B : Matrix ι ι ℝ)
    (hB : B * B.transpose = spec.covariance) :
    ∃ μ, HasGaussianVectorLaw spec μ := by
  let A := matrixMap B
  let ν : Measure (ι → ℝ) := standardPi.map A
  let μ : Measure (ι → ℝ) := ν.map (· + spec.mean)
  haveI : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map (by fun_prop)
  haveI : IsProbabilityMeasure μ := Measure.isProbabilityMeasure_map (by fun_prop)
  refine ⟨μ, ⟨inferInstance, ?_⟩⟩
  intro L
  change charFunDual (ν.map (· + spec.mean)) L = _
  rw [charFunDual_map_add_const]
  change charFunDual (standardPi.map A) L * _ = _
  rw [charFunDual_map, standardPi_charFunDual, ← Complex.exp_add]
  congr 1
  have hq : (∑ i, (dualCoordinates (L.comp A) i : ℂ)^2) =
      (quadraticForm spec.covariance (dualCoordinates L) : ℂ) := by
    simp_rw [A, dual_matrixMap]
    exact_mod_cast (gram_identity B (dualCoordinates L)).trans (by rw [hB])
  rw [hq, dualCoordinates_apply]
  simp only [GaussianVectorSpec.charExponent, Complex.ofReal_sum, Complex.ofReal_mul]
  ring

set_option backward.isDefEq.respectTransparency false in
theorem exists_gaussian_law (spec : GaussianVectorSpec ι) :
    ∃ μ, HasGaussianVectorLaw spec μ := by
  let C : Matrix ι ι ℝ := spec.covariance
  let B : Matrix ι ι ℝ := CFC.sqrt (A := Matrix ι ι ℝ) C
  have hpos : 0 ≤ C := (spec_posSemidef spec).nonneg
  have hs : B.transpose = B := by
    have hh := (CFC.sqrt_nonneg (A := Matrix ι ι ℝ) C).posSemidef.isHermitian
    simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using hh
  apply exists_law_of_factor spec B
  rw [hs]
  exact CFC.sqrt_mul_sqrt_self C hpos

#print axioms GaussianField.exists_gaussian_law
end GaussianField
