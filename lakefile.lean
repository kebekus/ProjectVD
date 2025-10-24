import Lake
open Lake DSL

package «VD» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]
  -- add any additional package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "d62eab0cc36ea522904895389c301cf8d844fd69"

@[default_target]
lean_lib «VD» where
  -- add any library configuration options here
