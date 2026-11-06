# Interfaces

The parent repository should import:

```lean
import Interfaces
```

This compatibility barrel re-exports the closed fact modules listed in
`MOTHER_DIGEST.md`, so those facts are available from the same parent import.
The import module name is unchanged; the Gaussian-law API below has a breaking
semantic correction dated 6 November 2026. Other interfaces retain their boundaries.

Breaking changes are any changes to the names or types below.

## Finite-dimensional Gaussian law

```lean
GaussianField.GaussianVectorSpec
GaussianField.GaussianVectorSpec.charExponent
GaussianField.HasGaussianVectorLaw
GaussianField.dualCoordinates
GaussianField.dualCoordinates_apply
GaussianField.HasGaussianVectorLaw.zero_dirac
GaussianField.HasGaussianVectorLaw.ext
GaussianField.exists_gaussian_law
GaussianField.exists_law_of_factor
```

`HasGaussianVectorLaw spec μ` uses the canonical Borel measurable structure on
the finite real product. Its fields are `probability : IsProbabilityMeasure μ`
and `characteristic_eq`, asserting, for every `L : StrongDual ℝ (ι → ℝ)`,

```text
charFunDual μ L = Complex.exp (spec.charExponent (dualCoordinates L))
dualCoordinates L i = L (Pi.single i 1)
```

`dualCoordinates_apply` proves `L x = ∑ i, dualCoordinates L i * x i`, identifying
this convention with the existing coordinate exponent. `ext hμ hν` is proved
using `Measure.ext_of_charFunDual`; it takes no external uniqueness assumption.
The `probability` field supplies finiteness. No density or positive-definiteness
is required. Arbitrary PSD existence is proved in `RealizationFinite.lean`:
`exists_gaussian_law (spec : GaussianVectorSpec ι) : ∃ μ, HasGaussianVectorLaw spec μ`
under `[Fintype ι] [DecidableEq ι]`. Singular covariance and the empty index type
are included. `exists_law_of_factor spec B hB` accepts an explicit factor with
`hB : B * B.transpose = spec.covariance`; the general theorem constructs this
factor using the PSD square root. No additional analytic hypothesis is required.

### Breaking migration

| Previous API | Current API / obligation |
| --- | --- |
| `HasGaussianVectorLaw spec μ χ` | `HasGaussianVectorLaw spec μ`; remove the independent `χ`. |
| `characteristic_exponent_eq` | Supply `probability` and `characteristic_eq` for the actual measure, with `exp`. |
| Arbitrary measurable structure on `ι → ℝ` | Canonical finite-product Borel structure. |
| `HasGaussianVectorLaw.Uniqueness spec` | Removed; uniqueness is proved, not caller data. |
| `HasGaussianVectorLaw.ext hUnique hμ hν` | `HasGaussianVectorLaw.ext hμ hν`. |

There is no automatic migration of old law witnesses: they contained no constraint
on `μ`. All internal uses of the removed predicate arguments and uniqueness
structure were confined to `GaussianVector.lean` and were migrated there. That correction left both
import barrels and all other library Lean files unchanged. The subsequent finite
PSD realization adds `RealizationFinite` to both barrels without changing the
existing contract, one-dimensional realization or Wick declarations. External consumers,
including the parent repository and frontier branches, have not been migrated or
certified compatible. The contract correction alone did not close finite-dimensional existence;
`exists_gaussian_law` now supplies that separate result. Wick/Isserlis remains open.

## Isserlis

```lean
GaussianField.Pairing
GaussianField.Pairing.weight
GaussianField.IsserlisInterface
GaussianField.isserlis_formula
```

`isserlis_formula` is conditional on `IsserlisInterface`.

## Uniform moments

```lean
GaussianField.UniformMomentBoundInterface
GaussianField.uniform_coordinate_moment_bound
```

`UniformMomentBoundInterface` is parameterized by one finite family
`X : iota -> Omega -> R`.  The bound is dimension-uniform in the sense that its
type does not depend on `Fintype.card iota`; proving reusable families of such
bounds is frontier work.

## Lattice free-field covariance decay

```lean
GaussianField.LatticeCovarianceDecayInterface
GaussianField.lattice_covariance_decay
```

This is finite-lattice only.  It carries the covariance kernel, mass, amplitude,
decay profile, and decay estimate as explicit data.
