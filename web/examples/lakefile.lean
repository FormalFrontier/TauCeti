import Lake
open Lake DSL

-- SubVerso pinned to the revision Verso v4.32.0 uses, so it builds on this toolchain.
require subverso from git
  "https://github.com/leanprover/subverso" @ "verso-v4.32.0"

-- Pin Mathlib to the same commit the root TauCeti project builds against (this top-level
-- pin overrides the `master` revision TauCeti requests transitively), so the slice of the
-- library we import here compiles exactly as it does upstream.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "81a5d257c8e410db227a6665ed08f64fea08e997"

-- The real Tau Ceti library, from the repository root, so the showcased theorems are
-- type-checked against exactly the library that proves them.
require «TauCeti» from "../.."

package «examples» where

@[default_target]
lean_lib «Examples» where
