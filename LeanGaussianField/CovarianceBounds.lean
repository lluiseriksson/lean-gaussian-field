import LeanGaussianField.GaussianVector
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Covariance bounds from positive semidefiniteness

Bilinearity of the covariance form, nonnegativity of the diagonal, and the
Cauchy-Schwarz bound `|C i j| ≤ √(C i i) * √(C j j)` for any
`GaussianVectorSpec`.  These are the seed of the dimension-uniform moment
bounds of milestone M2: every off-diagonal covariance entry is controlled by
the diagonal alone.

Reference: Janson, 1997, "Gaussian Hilbert Spaces", Remark 1.3, p. 4, for
Cauchy-Schwarz on covariance kernels via the discriminant argument.
-/

open scoped BigOperators

namespace GaussianField

variable {ι : Type*} [Fintype ι]

/-- Coordinate vector with value `a` at `i` and zero elsewhere. -/
def coord [DecidableEq ι] (i : ι) (a : ℝ) : ι → ℝ :=
  fun k => if k = i then a else 0

/-- Bilinear form associated to a covariance kernel on a finite index set. -/
noncomputable def bilinForm (covariance : ι → ι → ℝ) (s t : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, s i * covariance i j * t j

@[simp] theorem bilinForm_self (C : ι → ι → ℝ) (t : ι → ℝ) :
    bilinForm C t t = quadraticForm C t := rfl

theorem bilinForm_add_left (C : ι → ι → ℝ) (s₁ s₂ t : ι → ℝ) :
    bilinForm C (s₁ + s₂) t = bilinForm C s₁ t + bilinForm C s₂ t := by
  unfold bilinForm
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [Pi.add_apply]
  ring

theorem bilinForm_add_right (C : ι → ι → ℝ) (s t₁ t₂ : ι → ℝ) :
    bilinForm C s (t₁ + t₂) = bilinForm C s t₁ + bilinForm C s t₂ := by
  unfold bilinForm
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [Pi.add_apply]
  ring

/-- Evaluation of the bilinear form on coordinate vectors. -/
theorem bilinForm_single [DecidableEq ι] (C : ι → ι → ℝ) (i j : ι) (a b : ℝ) :
    bilinForm C (coord i a) (coord j b) = a * C i j * b := by
  unfold bilinForm
  rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
  · rw [Finset.sum_eq_single_of_mem j (Finset.mem_univ j)]
    · simp [coord]
    · intro k _ hk
      simp [coord, hk]
  · intro k _ hk
    have h0 : coord i a k = 0 := by simp [coord, hk]
    simp [h0]

/-- The quadratic form on a two-coordinate vector, for a symmetric kernel. -/
theorem quadraticForm_single_add_single [DecidableEq ι]
    (C : ι → ι → ℝ) (hC : ∀ i j, C i j = C j i) (i j : ι) (a b : ℝ) :
    quadraticForm C (coord i a + coord j b)
      = a * C i i * a + 2 * (a * C i j * b) + b * C j j * b := by
  rw [← bilinForm_self, bilinForm_add_left, bilinForm_add_right,
    bilinForm_add_right, bilinForm_single, bilinForm_single, bilinForm_single,
    bilinForm_single, hC j i]
  ring

namespace GaussianVectorSpec

variable [DecidableEq ι]

/-- The diagonal of a PSD covariance is nonnegative. -/
theorem diag_nonneg (spec : GaussianVectorSpec ι) (i : ι) :
    0 ≤ spec.covariance i i := by
  have h := spec.covariance_psd (coord i 1 + coord i 0)
  rw [quadraticForm_single_add_single _ spec.covariance_symm] at h
  nlinarith [h]

/-- Cauchy-Schwarz for PSD covariance kernels, squared form.

Reference: Janson, 1997, Remark 1.3, p. 4; proof by nonpositive discriminant
of `x ↦ Q(x·eᵢ + eⱼ)`.
-/
theorem covariance_sq_le (spec : GaussianVectorSpec ι) (i j : ι) :
    spec.covariance i j ^ 2 ≤ spec.covariance i i * spec.covariance j j := by
  have key : ∀ x : ℝ,
      0 ≤ spec.covariance i i * x ^ 2 + 2 * spec.covariance i j * x
        + spec.covariance j j := by
    intro x
    have h := spec.covariance_psd (coord i x + coord j 1)
    rw [quadraticForm_single_add_single _ spec.covariance_symm] at h
    nlinarith [h]
  have key' : ∀ x : ℝ,
      0 ≤ spec.covariance i i * (x * x)
        + (2 * spec.covariance i j) * x + spec.covariance j j := by
    intro x
    specialize key x
    nlinarith
  have hd := discrim_le_zero key'
  rw [discrim] at hd
  nlinarith [hd]

/-- Cauchy-Schwarz for PSD covariance kernels: every entry is bounded by the
diagonal.  This is the dimension-uniform control used by milestone M2. -/
theorem abs_covariance_le (spec : GaussianVectorSpec ι) (i j : ι) :
    |spec.covariance i j|
      ≤ Real.sqrt (spec.covariance i i) * Real.sqrt (spec.covariance j j) := by
  have h := spec.covariance_sq_le i j
  have h1 : |spec.covariance i j| = Real.sqrt (spec.covariance i j ^ 2) :=
    (Real.sqrt_sq_eq_abs _).symm
  rw [h1, ← Real.sqrt_mul (spec.diag_nonneg i)]
  exact Real.sqrt_le_sqrt h

/-- If a PSD covariance has a zero diagonal entry, every covariance entry in
the corresponding row is zero. -/
theorem covariance_eq_zero_of_diag_left (spec : GaussianVectorSpec ι) (i j : ι)
    (hii : spec.covariance i i = 0) :
    spec.covariance i j = 0 := by
  have hsq := spec.covariance_sq_le i j
  have hsq_nonpos : spec.covariance i j ^ 2 ≤ 0 := by
    simpa [hii] using hsq
  nlinarith [sq_nonneg (spec.covariance i j)]

/-- If a PSD covariance has a zero diagonal entry, every covariance entry in
the corresponding column is zero. -/
theorem covariance_eq_zero_of_diag_right (spec : GaussianVectorSpec ι) (i j : ι)
    (hjj : spec.covariance j j = 0) :
    spec.covariance i j = 0 := by
  calc
    spec.covariance i j = spec.covariance j i := spec.covariance_symm i j
    _ = 0 := spec.covariance_eq_zero_of_diag_left j i hjj

end GaussianVectorSpec

/-- The standard Gaussian specification: zero mean, identity covariance. -/
noncomputable def GaussianVectorSpec.std (ι : Type*) [Fintype ι] [DecidableEq ι] :
    GaussianVectorSpec ι where
  mean := fun _ => 0
  covariance := fun i j => if i = j then 1 else 0
  covariance_symm := by
    intro i j
    by_cases h : i = j
    · simp [h]
    · simp [h, Ne.symm h]
  covariance_psd := by
    intro t
    have hdiag : quadraticForm (fun i j => if i = j then (1 : ℝ) else 0) t
        = ∑ i, t i * t i := by
      unfold quadraticForm
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
      · simp
      · intro j _ hj
        simp [Ne.symm hj]
    rw [hdiag]
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg (t i)

end GaussianField
