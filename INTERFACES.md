# Interfaces

The parent repository should import:

```lean
import Interfaces
```

Breaking changes are any changes to the names or types below.

## Finite-dimensional Gaussian law

```lean
GaussianField.GaussianVectorSpec
GaussianField.GaussianVectorSpec.charExponent
GaussianField.HasGaussianVectorLaw
GaussianField.HasGaussianVectorLaw.Uniqueness
GaussianField.HasGaussianVectorLaw.ext
```

`HasGaussianVectorLaw` is conditional: a supplied measure and supplied
characteristic exponent are related to
`i <t,m> - (1/2) t C t`.  The exponential form and identification with
Mathlib's `charFun` are frontier work, not claimed on `main`.

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
