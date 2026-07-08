import Lake
open Lake DSL

package «SummerResearch2026» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]
  -- add any additional package configuration options here

require cslib from git "https://github.com/leanprover/cslib" @ "main"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «SummerResearch2026» where
  -- add any library configuration options here
