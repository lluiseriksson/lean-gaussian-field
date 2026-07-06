import LeanGaussianField.Pairing
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Structure theory of finite pairings

Extensionality, decidable equality, and finiteness of `Pairing ι`; the
double-counting identity `2 * pairs.card = card ι`; nonexistence on
odd-cardinality index types; and Wick-weight bounds.

Reference: Janson, 1997, "Gaussian Hilbert Spaces", Theorem 1.28, p. 22, for
the role of pairings in Wick/Isserlis moment identities.
-/

open scoped BigOperators

namespace GaussianField

namespace Pairing

variable {ι : Type*} [DecidableEq ι] [LinearOrder ι]

/-- Pairings are determined by their pair set. -/
@[ext] theorem ext : ∀ {P Q : Pairing ι}, P.pairs = Q.pairs → P = Q
  | ⟨_, _, _⟩, ⟨_, _, _⟩, rfl => rfl

instance : DecidableEq (Pairing ι) := fun P Q =>
  decidable_of_iff (P.pairs = Q.pairs) ⟨ext, fun h => by rw [h]⟩

noncomputable instance [Fintype ι] : Fintype (Pairing ι) :=
  Fintype.ofInjective Pairing.pairs fun _ _ h => ext h

/-- The two members of a pair are distinct. -/
theorem fst_ne_snd {P : Pairing ι} {p : ι × ι} (hp : p ∈ P.pairs) :
    p.1 ≠ p.2 :=
  ne_of_lt (P.ordered p hp)

/-- A pair with distinct entries is incident to exactly two indices. -/
theorem card_filter_index {κ : Type*} [DecidableEq κ] [Fintype κ]
    (p : κ × κ) (hne : p.1 ≠ p.2) :
    (Finset.univ.filter fun i : κ => p.1 = i ∨ p.2 = i).card = 2 := by
  have hset : (Finset.univ.filter fun i : κ => p.1 = i ∨ p.2 = i)
      = {p.1, p.2} := by
    ext i
    simp [eq_comm]
  rw [hset, Finset.card_pair hne]

/-- Double counting of pair-index incidences: a pairing of `ι` has exactly
`card ι / 2` pairs. -/
theorem two_mul_card_pairs [Fintype ι] (P : Pairing ι) :
    2 * P.pairs.card = Fintype.card ι := by
  have hswap :
      (∑ i : ι, ∑ p ∈ P.pairs, if p.1 = i ∨ p.2 = i then (1 : ℕ) else 0)
        = ∑ p ∈ P.pairs, ∑ i : ι, if p.1 = i ∨ p.2 = i then (1 : ℕ) else 0 :=
    Finset.sum_comm
  have hleft : ∀ i : ι,
      (∑ p ∈ P.pairs, if p.1 = i ∨ p.2 = i then (1 : ℕ) else 0) = 1 := by
    intro i
    rw [← Finset.card_filter]
    exact P.covers_once i
  have hright : ∀ p ∈ P.pairs,
      (∑ i : ι, if p.1 = i ∨ p.2 = i then (1 : ℕ) else 0) = 2 := by
    intro p hp
    rw [← Finset.card_filter]
    exact card_filter_index p (fst_ne_snd hp)
  calc 2 * P.pairs.card
      = ∑ _p ∈ P.pairs, 2 := by
        rw [Finset.sum_const, smul_eq_mul, mul_comm]
    _ = ∑ p ∈ P.pairs, ∑ i : ι, if p.1 = i ∨ p.2 = i then (1 : ℕ) else 0 :=
        (Finset.sum_congr rfl hright).symm
    _ = ∑ i : ι, ∑ p ∈ P.pairs, if p.1 = i ∨ p.2 = i then (1 : ℕ) else 0 :=
        hswap.symm
    _ = ∑ _i : ι, 1 := Finset.sum_congr rfl fun i _ => hleft i
    _ = Fintype.card ι := by simp

/-- A pairing has exactly half as many pairs as there are indices. -/
theorem card_pairs_eq_card_div_two [Fintype ι] (P : Pairing ι) :
    P.pairs.card = Fintype.card ι / 2 := by
  have h := P.two_mul_card_pairs
  omega

/-- A pairing has an edge exactly when the indexed type is nonempty. -/
theorem pairs_nonempty_iff_nonempty [Fintype ι] (P : Pairing ι) :
    P.pairs.Nonempty ↔ Nonempty ι := by
  constructor
  · rintro ⟨p, _hp⟩
    exact ⟨p.1⟩
  · rintro ⟨i⟩
    by_contra hpairs
    have hempty : P.pairs = ∅ := Finset.not_nonempty_iff_eq_empty.mp hpairs
    have hcover := P.covers_once i
    simp [hempty] at hcover

/-- A pairing has a positive number of edges exactly when the indexed type is
nonempty. -/
theorem card_pairs_pos_iff_nonempty [Fintype ι] (P : Pairing ι) :
    0 < P.pairs.card ↔ Nonempty ι := by
  rw [Finset.card_pos, pairs_nonempty_iff_nonempty]

/-- A pairing has zero edges exactly when the indexed type is empty. -/
theorem card_pairs_eq_zero_iff_not_nonempty [Fintype ι] (P : Pairing ι) :
    P.pairs.card = 0 ↔ ¬ Nonempty ι := by
  constructor
  · intro hcard hι
    have hpos : 0 < P.pairs.card := (card_pairs_pos_iff_nonempty P).mpr hι
    omega
  · intro hι
    apply Nat.eq_zero_of_not_pos
    intro hpos
    exact hι ((card_pairs_pos_iff_nonempty P).mp hpos)

/-- Index types carrying a pairing have even cardinality. -/
theorem even_card [Fintype ι] (P : Pairing ι) : Even (Fintype.card ι) := by
  have h := P.two_mul_card_pairs
  exact ⟨P.pairs.card, by omega⟩

/-- There are no pairings of an odd-cardinality index type. -/
theorem isEmpty_of_odd_card [Fintype ι] (h : ¬ Even (Fintype.card ι)) :
    IsEmpty (Pairing ι) :=
  ⟨fun P => h P.even_card⟩

/-- The empty pairing on an empty index type. -/
def empty (ι : Type*) [DecidableEq ι] [LinearOrder ι] [IsEmpty ι] :
    Pairing ι where
  pairs := ∅
  ordered := by
    intro p hp
    simp at hp
  covers_once := fun i => isEmptyElim i

@[simp] theorem weight_empty [IsEmpty ι] (C : ι → ι → ℝ) :
    (empty ι).weight C = 1 := by
  simp [weight, empty]

/-- If one edge factor is zero, the whole Wick weight is zero. -/
theorem weight_eq_zero_of_mem (P : Pairing ι) {C : ι → ι → ℝ} {p : ι × ι}
    (hp : p ∈ P.pairs) (hzero : C p.1 p.2 = 0) :
    P.weight C = 0 := by
  exact Finset.prod_eq_zero hp hzero

/-- The absolute value of a Wick weight is the product of entry magnitudes. -/
theorem abs_weight_eq (P : Pairing ι) (C : ι → ι → ℝ) :
    |P.weight C| = ∏ p ∈ P.pairs, |C p.1 p.2| := by
  simpa [weight] using Finset.abs_prod P.pairs fun p => C p.1 p.2

/-- Wick weights are bounded by any uniform bound on covariance entries,
raised to the number of pairs.  Note the bound does not depend on `card ι`
beyond the exponent. -/
theorem abs_weight_le_pow (P : Pairing ι) {C : ι → ι → ℝ} {B : ℝ}
    (hB : ∀ p ∈ P.pairs, |C p.1 p.2| ≤ B) :
    |P.weight C| ≤ B ^ P.pairs.card := by
  rw [abs_weight_eq]
  calc ∏ p ∈ P.pairs, |C p.1 p.2|
      ≤ ∏ _p ∈ P.pairs, B :=
        Finset.prod_le_prod (fun p _ => abs_nonneg _) hB
    _ = B ^ P.pairs.card := Finset.prod_const B

end Pairing

end GaussianField
