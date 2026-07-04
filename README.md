# lean-gaussian-field

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
  specifications, characteristic exponents, and conditional uniqueness of
  realized laws.
- M1: prove Wick/Isserlis over the reusable pairing type.
- M2: prove Gaussian integration by parts and explicit dimension-uniform moment
  bounds.
- M3: finite-lattice massive free field with covariance `(-Delta + m^2)^{-1}`
  and explicit exponential covariance decay.

## Parent import surface

The stable parent-facing module is:

```lean
import Interfaces
```

See `INTERFACES.md` for exact names and `HYPOTHESIS_FRONTIER.md` for the
current honest frontier.  See `MOTHER_DIGEST.md` for a compact
mother-facing routing note with exact theorem/API names, files, hypotheses,
and suggested consumption points.
