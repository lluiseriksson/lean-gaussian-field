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
is required. The zero-covariance witness is proved; arbitrary PSD existence is
still a separate obligation.

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
structure were confined to `GaussianVector.lean` and were migrated there. Both
import barrels and all other library Lean files are unchanged. External consumers,
including the parent repository and frontier branches, have not been migrated or
certified compatible. This correction does not close Wick/Isserlis or general
finite-dimensional existence.

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
