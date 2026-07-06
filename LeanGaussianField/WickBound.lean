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

/-- If a paired left endpoint has zero diagonal covariance, the Wick weight
vanishes. -/
theorem weight_eq_zero_of_diag_left (spec : GaussianVectorSpec ι)
    (P : Pairing ι) {p : ι × ι} (hp : p ∈ P.pairs)
    (hdiag : spec.covariance p.1 p.1 = 0) :
    P.weight spec.covariance = 0 := by
  exact P.weight_eq_zero_of_mem hp
    (spec.covariance_eq_zero_of_diag_left p.1 p.2 hdiag)

/-- If a paired right endpoint has zero diagonal covariance, the Wick weight
vanishes. -/
theorem weight_eq_zero_of_diag_right (spec : GaussianVectorSpec ι)
    (P : Pairing ι) {p : ι × ι} (hp : p ∈ P.pairs)
    (hdiag : spec.covariance p.2 p.2 = 0) :
    P.weight spec.covariance = 0 := by
  exact P.weight_eq_zero_of_mem hp
    (spec.covariance_eq_zero_of_diag_right p.1 p.2 hdiag)

/-- In the standard specification, any pairing edge has zero covariance
factor, since pairing edges connect distinct indices. -/
theorem weight_std_eq_zero_of_mem (P : Pairing ι) {p : ι × ι}
    (hp : p ∈ P.pairs) :
    P.weight (GaussianVectorSpec.std ι).covariance = 0 := by
  exact P.weight_eq_zero_of_mem hp (by
    have hne : p.1 ≠ p.2 := ne_of_lt (P.ordered p hp)
    change (if p.1 = p.2 then (1 : ℝ) else 0) = 0
    simp [hne])

/-- A nonempty standard-specification pairing has zero Wick weight. -/
theorem weight_std_eq_zero_of_nonempty (P : Pairing ι)
    (hP : P.pairs.Nonempty) :
    P.weight (GaussianVectorSpec.std ι).covariance = 0 := by
  rcases hP with ⟨p, hp⟩
  exact weight_std_eq_zero_of_mem P hp

/-- An empty standard-specification pairing has Wick weight one. -/
theorem weight_std_eq_one_of_pairs_empty (P : Pairing ι)
    (hP : P.pairs = ∅) :
    P.weight (GaussianVectorSpec.std ι).covariance = 1 := by
  simp [Pairing.weight, hP]

/-- In the standard specification, a Wick weight is exactly the empty-pairing
indicator. -/
theorem weight_std_eq_if_pairs_empty (P : Pairing ι) :
    P.weight (GaussianVectorSpec.std ι).covariance =
      if P.pairs = ∅ then 1 else 0 := by
  by_cases hP : P.pairs = ∅
  · simp [hP, weight_std_eq_one_of_pairs_empty P hP]
  · have hne : P.pairs.Nonempty := Finset.nonempty_iff_ne_empty.mpr hP
    simp [hP, weight_std_eq_zero_of_nonempty P hne]

/-- In the standard specification, every Wick weight is nonnegative. -/
theorem weight_std_nonneg (P : Pairing ι) :
    0 ≤ P.weight (GaussianVectorSpec.std ι).covariance := by
  rw [weight_std_eq_if_pairs_empty]
  by_cases hP : P.pairs = ∅ <;> simp [hP]

/-- In the standard specification, every Wick weight is at most one. -/
theorem weight_std_le_one (P : Pairing ι) :
    P.weight (GaussianVectorSpec.std ι).covariance ≤ 1 := by
  rw [weight_std_eq_if_pairs_empty]
  by_cases hP : P.pairs = ∅ <;> simp [hP]

/-- In the standard specification, a Wick weight vanishes exactly for
nonempty pairings. -/
theorem weight_std_eq_zero_iff_pairs_nonempty (P : Pairing ι) :
    P.weight (GaussianVectorSpec.std ι).covariance = 0 ↔ P.pairs.Nonempty := by
  constructor
  · intro hzero
    by_contra hempty
    have hP : P.pairs = ∅ := Finset.not_nonempty_iff_eq_empty.mp hempty
    have hone := weight_std_eq_one_of_pairs_empty P hP
    linarith
  · intro hP
    exact weight_std_eq_zero_of_nonempty P hP

/-- In the standard specification, a Wick weight is one exactly for the
empty pairing. -/
theorem weight_std_eq_one_iff_pairs_empty (P : Pairing ι) :
    P.weight (GaussianVectorSpec.std ι).covariance = 1 ↔ P.pairs = ∅ := by
  constructor
  · intro hone
    by_contra hP
    have hne : P.pairs.Nonempty := Finset.nonempty_iff_ne_empty.mpr hP
    have hzero := weight_std_eq_zero_of_nonempty P hne
    have : (0 : ℝ) = 1 := by
      rw [← hzero, hone]
    norm_num at this
  · intro hP
    exact weight_std_eq_one_of_pairs_empty P hP

/-- In the standard specification, a Wick weight vanishes exactly when the
index type is nonempty. -/
theorem weight_std_eq_zero_iff_nonempty (P : Pairing ι) :
    P.weight (GaussianVectorSpec.std ι).covariance = 0 ↔ Nonempty ι := by
  rw [weight_std_eq_zero_iff_pairs_nonempty, Pairing.pairs_nonempty_iff_nonempty]

/-- In the standard specification, a Wick weight is one exactly when the
index type is empty. -/
theorem weight_std_eq_one_iff_not_nonempty (P : Pairing ι) :
    P.weight (GaussianVectorSpec.std ι).covariance = 1 ↔ ¬ Nonempty ι := by
  rw [weight_std_eq_one_iff_pairs_empty]
  constructor
  · intro hP hι
    have hne : P.pairs.Nonempty := (Pairing.pairs_nonempty_iff_nonempty P).mpr hι
    exact hne.ne_empty hP
  · intro hι
    exact Finset.not_nonempty_iff_eq_empty.mp fun hP =>
      hι ((Pairing.pairs_nonempty_iff_nonempty P).mp hP)

/-- In the standard specification, a Wick weight on a nonempty index type
vanishes. -/
theorem weight_std_eq_zero_of_index_nonempty (P : Pairing ι) [Nonempty ι] :
    P.weight (GaussianVectorSpec.std ι).covariance = 0 :=
  (weight_std_eq_zero_iff_nonempty P).mpr inferInstance

/-- In the standard specification, a Wick weight on an empty index type is
one. -/
theorem weight_std_eq_one_of_index_isEmpty (P : Pairing ι) [IsEmpty ι] :
    P.weight (GaussianVectorSpec.std ι).covariance = 1 :=
  (weight_std_eq_one_iff_not_nonempty P).mpr fun hι =>
    hι.elim isEmptyElim

/-- In the standard specification, a Wick weight is one exactly when the
index type carries an `IsEmpty` witness. -/
theorem weight_std_eq_one_iff_isEmpty (P : Pairing ι) :
    P.weight (GaussianVectorSpec.std ι).covariance = 1 ↔ IsEmpty ι := by
  rw [weight_std_eq_one_iff_pairs_empty, Pairing.pairs_empty_iff_isEmpty]

/-- In the standard specification, a Wick weight is nonzero exactly when the
index type carries an `IsEmpty` witness. -/
theorem weight_std_ne_zero_iff_isEmpty (P : Pairing ι) :
    P.weight (GaussianVectorSpec.std ι).covariance ≠ 0 ↔ IsEmpty ι := by
  constructor
  · intro hne
    exact ⟨fun i => hne ((weight_std_eq_zero_iff_nonempty P).mpr ⟨i⟩)⟩
  · intro hι hzero
    have hone : P.weight (GaussianVectorSpec.std ι).covariance = 1 :=
      (weight_std_eq_one_iff_isEmpty P).mpr hι
    linarith

/-- In the standard specification, a Wick weight has magnitude zero exactly
when the index type is nonempty. -/
theorem abs_weight_std_eq_zero_iff_nonempty (P : Pairing ι) :
    |P.weight (GaussianVectorSpec.std ι).covariance| = 0 ↔ Nonempty ι := by
  rw [abs_eq_zero, weight_std_eq_zero_iff_nonempty]

/-- In the standard specification, a Wick weight has magnitude one exactly
when the index type carries an `IsEmpty` witness. -/
theorem abs_weight_std_eq_one_iff_isEmpty (P : Pairing ι) :
    |P.weight (GaussianVectorSpec.std ι).covariance| = 1 ↔ IsEmpty ι := by
  constructor
  · intro habs
    by_cases hι : Nonempty ι
    · have hzero : P.weight (GaussianVectorSpec.std ι).covariance = 0 :=
        weight_std_eq_zero_of_index_nonempty P
      rw [hzero] at habs
      norm_num at habs
    · exact ⟨fun i => hι ⟨i⟩⟩
  · intro hι
    have hone : P.weight (GaussianVectorSpec.std ι).covariance = 1 :=
      (weight_std_eq_one_iff_isEmpty P).mpr hι
    rw [hone]
    norm_num

/-- In the standard specification, a Wick weight has magnitude zero on a
nonempty index type. -/
theorem abs_weight_std_eq_zero_of_index_nonempty (P : Pairing ι) [Nonempty ι] :
    |P.weight (GaussianVectorSpec.std ι).covariance| = 0 :=
  (abs_weight_std_eq_zero_iff_nonempty P).mpr inferInstance

/-- In the standard specification, a Wick weight has magnitude one on an empty
index type. -/
theorem abs_weight_std_eq_one_of_index_isEmpty (P : Pairing ι) [IsEmpty ι] :
    |P.weight (GaussianVectorSpec.std ι).covariance| = 1 :=
  (abs_weight_std_eq_one_iff_isEmpty P).mpr inferInstance

/-- For the standard specification every Wick weight has magnitude at most
one. -/
theorem abs_weight_std_le_one (P : Pairing ι) :
    |P.weight (GaussianVectorSpec.std ι).covariance| ≤ 1 := by
  have hdiag : ∀ i, (GaussianVectorSpec.std ι).covariance i i ≤ 1 := by
    intro i
    simp [GaussianVectorSpec.std]
  simpa using abs_weight_le_of_diag (GaussianVectorSpec.std ι) P hdiag

end GaussianField
