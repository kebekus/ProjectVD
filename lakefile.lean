import Lake
open Lake DSL

/-- Mathlib's style/linter options. These are prefixed by `` `weak`` when used as `leanOptions`, so
that toggling them never invalidates the build cache (changing a `weak` option does not affect the
`.olean` hash). Mirrors `mathlibOnlyLinters` in Mathlib's own lakefile. -/
abbrev mathlibOnlyLinters : Array LeanOption := #[
  -- The standard set of style linters: 100-character line limit (`linter.style.longLine`),
  -- `cdot`, `lambdaSyntax`, `dollarSyntax`, `multiGoal`, `setOption`, and more.
  ⟨`linter.mathlibStandardSet, true⟩,
  ⟨`linter.style.header, true⟩,
  ⟨`linter.style.longFile, .ofNat 1500⟩,
]

/-- Options applied to building and interactively editing the `VD` library, matching the experience
of editing Mathlib itself. Mirrors `mathlibLeanOptions` in Mathlib's lakefile. -/
abbrev mathlibLeanOptions : Array LeanOption := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`autoImplicit, false⟩,
    ⟨`maxSynthPendingDepth, .ofNat 3⟩,
  ] ++ -- linters as `weak` options, so they are used by `lake build` without affecting the cache
    mathlibOnlyLinters.map fun s ↦ { s with name := `weak ++ s.name }

package «VD» where
  -- add any additional package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «VD» where
  -- Enforce Mathlib's default linters and style options.
  leanOptions := mathlibLeanOptions
