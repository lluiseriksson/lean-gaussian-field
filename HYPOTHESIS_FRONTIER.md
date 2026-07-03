# Hypothesis frontier

Branch: `main`

## Lean placeholders

- No `.lean` placeholders are present on `main`.
- CI rejects `sorry` and `admit` in `.lean` files on `main`.

## Explicit hypotheses carried by interfaces

- `GaussianField.GaussianVectorSpec.covariance_psd`: covariance data must be
  supplied with a positive-semidefinite proof.
- `GaussianField.HasGaussianVectorLaw.characteristic_exponent_eq`:
  existence/realization of the finite-dimensional Gaussian law, and its
  identification with the target characteristic exponent, are explicit data.
- `GaussianField.HasGaussianVectorLaw.Uniqueness.eq_of_hasGaussianVectorLaw`:
  uniqueness of realized Gaussian vector laws is an explicit hypothesis.
- `GaussianField.IsserlisInterface.isserlis`: the Wick/Isserlis moment identity
  is not yet proved in `main`; the moment functional is explicit data.
- `GaussianField.UniformMomentBoundInterface.coordinate_moment_le`: uniform
  moment bounds are not yet proved in `main`; coordinate moments and the bound
  are explicit data for each finite family.
- `GaussianField.LatticeCovarianceDecayInterface.decay`: finite-lattice
  covariance decay is not yet proved in `main`; mass, amplitude, covariance,
  decay profile, and decay estimate are explicit data.

## Closed facts on the M0 path

- `GaussianField.GaussianVectorSpec.zero`: degenerate centered
  finite-dimensional Gaussian specification with zero covariance.
- `GaussianField.GaussianVectorSpec.charExponent_zero_arg`: the characteristic
  exponent of any specification is zero at the origin.
- `GaussianField.GaussianVectorSpec.charExponent_zero_spec`: the degenerate
  zero specification has identically zero characteristic exponent.

## Distance to the target

The repository currently provides the parent-facing statement surface and
honest conditional wrappers.  It does not yet prove the Gaussian primitives
needed by `hRpoly`.  The next frontier branch should introduce compilable
statement-first theorem files for:

- construction of finite-dimensional Gaussian laws from arbitrary PSD
  covariance;
- Wick/Isserlis over `GaussianField.Pairing`;
- Gaussian integration by parts and dimension-uniform moment constants;
- finite-lattice massive free-field covariance and exponential decay.
