import Lake
open Lake DSL

package a276175 where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.29.0"

@[default_target]
lean_lib Proof where
  srcDir := "."
