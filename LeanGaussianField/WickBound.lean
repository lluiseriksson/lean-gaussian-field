import LeanGaussianField.CovarianceBounds
import LeanGaussianField.PairingLemmas

/-!
# Dimension-uniform Wick weight bounds

Combining Cauchy-Schwarz on PSD covariance kernels with the pairing weight
bound: every Wick weight of a Gaussian specification is controlled by the
supremum of the covariance diagonal alone, uniformly in the index set.  This
is the combinatorial seed of the milestone M2 moment bounds consumed by the
small-field regime of `hRpoly` in the parent repository.

Reference: Janson, 1997, "Gaussian Hilbert Spaces", Theorem 1.28, p. 22, and
Remark 1.3, p. 4.
-/

open scoped BigOperators

namespace GaussianField

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]

/-- Wick weights of a Gaussian specification are bounded by the supremum of
the covariance diagonal, raised to the number of pairs.  The bound is uniform
in the dimension `card ι`. -/
theorem abs_weight_le_of_diag (spec : GaussianVectorSpec ι) (P : Pairing ι)
    {B : ℝ} (hdiag : ∀ i, spec.covariance i i ≤ B) :
    |P.weight spec.covariance| ≤ B ^ P.pairs.card := by
  refine P.abs_weight_le_pow fun p hp => ?_
  have h0i : 0 ≤ spec.covariance p.1 p.1 := spec.diag_nonneg p.1
  have hB0 : 0 ≤ B := le_trans h0i (hdiag p.1)
  have hcs := spec.abs_covariance_le p.1 p.2
  have h1 : Real.sqrt (spec.covariance p.1 p.1) ≤ Real.sqrt B :=
    Real.sqrt_le_sqrt (hdiag p.1)
  have h2 : Real.sqrt (spec.covariance p.2 p.2) ≤ Real.sqrt B :=
    Real.sqrt_le_sqrt (hdiag p.2)
  have hmul : Real.sqrt (spec.covariance p.1 p.1)
        * Real.sqrt (spec.covariance p.2 p.2)
      ≤ Real.sqrt B * Real.sqrt B :=
    mul_le_mul h1 h2 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hBB : Real.sqrt B * Real.sqrt B = B := Real.mul_self_sqrt hB0
  linarith

/-- For the standard specification every Wick weight has magnitude at most
one. -/
theorem abs_weight_std_le_one (P : Pairing ι) :
    |P.weight (GaussianVectorSpec.std ι).covariance| ≤ 1 := by
  have hdiag : ∀ i, (GaussianVectorSpec.std ι).covariance i i ≤ 1 := by
    intro i
    simp [GaussianVectorSpec.std]
  simpa using abs_weight_le_of_diag (GaussianVectorSpec.std ι) P hdiag

end GaussianField
