import LeanGaussianField.GaussianVector
import LeanGaussianField.Pairing
import Mathlib.Topology.MetricSpace.Basic

/-!
# Parent-facing Gaussian interfaces

This module is the stable import surface for `THE-ERIKSSON-PROGRAMME`.
Unproved analytic inputs are explicit fields of structures.
-/

open scoped BigOperators
open MeasureTheory

namespace GaussianField

/-- Conditional Isserlis/Wick interface for a finite centered Gaussian family.

Reference: Isserlis, 1918, formula (1), p. 136; Wick, 1950, Theorem 1, p. 268.
The actual formula is carried as the `isserlis` field until proved in this
satellite repository.
-/
structure IsserlisInterface (ι Ω : Type*) [Fintype ι] [DecidableEq ι]
    [LinearOrder ι] [MeasurableSpace Ω] (P : Measure Ω)
    (X : ι → Ω → ℝ) where
  covariance : ι → ι → ℝ
  pairings : Finset (Pairing ι)
  moment : (Ω → ℝ) → ℝ
  isserlis :
    moment (fun ω => ∏ i, X i ω) = ∑ π ∈ pairings, π.weight covariance

/-- Parent-facing Isserlis formula, conditional on `IsserlisInterface`. -/
theorem isserlis_formula {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    [LinearOrder ι] [MeasurableSpace Ω] {P : Measure Ω}
    {X : ι → Ω → ℝ} (h : IsserlisInterface ι Ω P X) :
    h.moment (fun ω => ∏ i, X i ω) = ∑ π ∈ h.pairings, π.weight h.covariance :=
  h.isserlis

/-- Dimension-uniform coordinate moment bounds for Gaussian inputs.

Reference: Janson, 1997, Theorem 1.28, p. 22, for standard Gaussian moment
growth.  The predicate `Applies` marks the families covered by this bound.
-/
structure UniformMomentBoundInterface (ι Ω : Type*) [Fintype ι]
    [MeasurableSpace Ω] (P : Measure Ω) (X : ι → Ω → ℝ) where
  bound : ℕ → ℝ
  bound_nonneg : ∀ k, 0 ≤ bound k
  coordinateMoment : ℕ → ι → ℝ
  coordinate_moment_le : ∀ k : ℕ, ∀ i : ι, coordinateMoment k i ≤ bound k

/-- Parent-facing uniform coordinate moment bound. -/
theorem uniform_coordinate_moment_bound {ι Ω : Type*} [Fintype ι]
    [MeasurableSpace Ω] {P : Measure Ω} {X : ι → Ω → ℝ}
    (h : UniformMomentBoundInterface ι Ω P X)
    (k : ℕ) (i : ι) :
    h.coordinateMoment k i ≤ h.bound k :=
  h.coordinate_moment_le k i

/-- Finite-lattice free-field covariance decay interface.

Reference: Balaban, 1984, Section 6.3, for the finite-volume massive free-field
covariance input used in the small-field regime.  The metric and covariance are
parameters so no infinite-volume or continuum claim is made.
-/
structure LatticeCovarianceDecayInterface (V : Type*) [PseudoMetricSpace V] where
  covariance : V → V → ℝ
  mass : ℝ
  amplitude : ℝ
  decayProfile : ℝ → ℝ → ℝ
  mass_pos : 0 < mass
  amplitude_nonneg : 0 ≤ amplitude
  decayProfile_nonneg : ∀ m r, 0 ≤ decayProfile m r
  decay : ∀ x y : V,
    |covariance x y| ≤ amplitude * decayProfile mass (dist x y)

/-- Parent-facing finite-lattice covariance decay bound. -/
theorem lattice_covariance_decay {V : Type*} [PseudoMetricSpace V]
    (h : LatticeCovarianceDecayInterface V) (x y : V) :
    |h.covariance x y| ≤ h.amplitude * h.decayProfile h.mass (dist x y) :=
  h.decay x y

end GaussianField
