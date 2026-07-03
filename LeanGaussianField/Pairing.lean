import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic

/-!
# Finite pairings

This file gives a small reusable type for Wick/Isserlis statements.  It is
kept combinatorial and independent of probability theory.
-/

open scoped BigOperators

namespace GaussianField

/-- A finite pairing of a linearly ordered index type.

The pairs are oriented by the ambient order, so `(i, j)` and `(j, i)` are not
both valid representatives.  The `covers_once` field says that each index is
contained in exactly one pair.
-/
structure Pairing (ι : Type*) [DecidableEq ι] [LinearOrder ι] where
  pairs : Finset (ι × ι)
  ordered : ∀ p ∈ pairs, p.1 < p.2
  covers_once : ∀ i : ι, (pairs.filter fun p => p.1 = i ∨ p.2 = i).card = 1

namespace Pairing

variable {ι : Type*} [DecidableEq ι] [LinearOrder ι]

/-- The Wick weight of a pairing for a covariance kernel. -/
def weight (P : Pairing ι) (covariance : ι → ι → ℝ) : ℝ :=
  ∏ p ∈ P.pairs, covariance p.1 p.2

end Pairing

end GaussianField
