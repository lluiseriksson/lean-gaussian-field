# lean-gaussian-field

<!-- RESEARCH-UPDATE-2026-09-09 -->
> **Research update · 9 September 2026:** [verified source cards, limits and next experiments](research/updates/2026-09-09.md) · [machine-readable dossier](research/updates/2026-09-09.json).

Lean 4 + Mathlib satellite for finite Gaussian primitives needed by the
small-field layer of `THE-ERIKSSON-PROGRAMME`.

This is not a proof of the Yang-Mills mass gap, not a renormalization project,
and not an infinite-dimensional field theory formalization.  It is a finite
Gaussian interface and proof staging repo for the `hRpoly` inputs used by the
parent program.

## Scope

- Lean toolchain matches the parent repo:
  `leanprover/lean4:v4.29.0-rc6`.
- Mathlib is pinned to the parent commit:
  `07642720480157414db592fa85b626dafb71355b`.
- `main` has no Lean placeholders.
- Unproved analysis is carried as explicit hypotheses, never as axioms.
- Statement-first work with placeholders belongs on `frontier/*` branches.

## Milestones

- M0: audit Mathlib Gaussian support; define finite-dimensional Gaussian
  specifications, characteristic exponents, and proved uniqueness of probability
  measures satisfying the actual characteristic-function contract.
- M1: prove Wick/Isserlis over the reusable pairing type.
- M2: prove Gaussian integration by parts and explicit dimension-uniform moment
  bounds.
- M3: finite-lattice massive free field with covariance `(-Delta + m^2)^{-1}`
  and explicit exponential covariance decay.

## Parent import surface

The parent-facing import module remains:

```lean
import Interfaces
```

See `INTERFACES.md` for exact names and `HYPOTHESIS_FRONTIER.md` for the
current honest frontier.  See `MOTHER_DIGEST.md` for a compact
mother-facing routing note with exact theorem/API names, files, hypotheses,
and suggested consumption points.

## Gaussian-law contract migration (6 November 2026)

This is a **breaking API correction**. `HasGaussianVectorLaw spec μ` now requires
probability normalization and an identity for Mathlib's actual `charFunDual μ`:
it equals `Complex.exp (spec.charExponent (dualCoordinates L))` for every continuous
real linear functional `L`. The old independent function argument and the external
`HasGaussianVectorLaw.Uniqueness` structure have been removed. The old predicate
did not constrain the measure, so its witnesses cannot be converted automatically.

`HasGaussianVectorLaw.ext hμ hν` now proves equality of measures directly from
Mathlib characteristic-function uniqueness. The covariance assumption remains PSD,
allowing singular cases; `HasGaussianVectorLaw.zero_dirac` realizes zero covariance.
General PSD realization is now proved by `exists_gaussian_law`; the moment/Isserlis
bridge remains open. The existing
one-dimensional realization is unchanged. See [the migration table](INTERFACES.md)
for field and call-site changes; external consumers have not been inspected.

After the normal `lake build`, run the semantic regression checks with:

```sh
lake env lean -j1 ContractChecks.lean
```

CI runs this check after the library build. It accepts the degenerate Dirac-zero
law and rejects both the zero measure and a wrong-mean probability Dirac law.
It also reports the axioms of the coordinate identity, uniqueness and singular
realization proofs. The existing scheduled/manual heartbeat remains separate;
contract and realization changes use the Lean workflow without the heartbeat's parent lookup.

## Finite PSD realization (6 November 2026)

`GaussianField.exists_gaussian_law spec` constructs a probability measure satisfying
`HasGaussianVectorLaw spec` for every specification on a finite index type
`[Fintype ι] [DecidableEq ι]`. `RealizationFinite.lean` maps independent standard real
Gaussians through the PSD matrix square root and translates by `spec.mean`.
The coordinate Gram identity identifies the resulting dual characteristic function
with `exp (charExponent)`. No positive-definiteness, density, inverse, or nonempty
index assumption is used. This is a standard finite-dimensional construction.

The theorem is exported by both existing import barrels. Existing contract,
one-dimensional and Wick declarations are unchanged; external consumers and frontier
branches have not been inspected or migrated. Existence does not identify the
arbitrary moment functional in `IsserlisInterface` with measure integrals or prove
integrability, Isserlis, dimension-uniform moments, or infinite-field statements.

After `lake build`, CI also runs:

```sh
lake env lean -j1 ExistenceChecks.lean
```

This checks the public `Interfaces` import, a nonzero rank-one covariance with a
nonzero mean and an explicit kernel, and an arbitrary specification on `Fin 0`.
The library and checks report proof axioms; only the standard Lean axioms are used.
