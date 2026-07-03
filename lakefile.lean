import Lake
open Lake DSL

package «LeanGaussianField» where

@[default_target]
lean_lib «LeanGaussianField» where

/-- Compatibility barrel for the parent repository. -/
@[default_target]
lean_lib «Interfaces» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
    "07642720480157414db592fa85b626dafb71355b"
