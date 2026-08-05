/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RepresentationTheory.Subrepresentation

/-!
# The extreme subrepresentations carry the extreme subspaces

Mathlib's `Subrepresentation` API records how `toSubmodule` interacts with the lattice
operations — `Subrepresentation.toSubmodule_sup` and `Subrepresentation.toSubmodule_inf`, both
`@[simp]` and both true by `rfl` — but not how it interacts with the bounded-lattice structure.
This file adds the two missing counterparts, in the same shape.

They are stated at the typeclasses `Subrepresentation` itself asks for, so they apply wherever
the abstraction does, and they let proofs about `⊥` and `⊤` subrepresentations avoid asserting
the definitional unfolding of the `BoundedOrder` instance by hand.

## Main results

* `Subrepresentation.toSubmodule_bot`
* `Subrepresentation.toSubmodule_top`
-/

public section

namespace Subrepresentation

variable {A G W : Type*} [Semiring A] [Monoid G] [AddCommMonoid W] [Module A W]
  {ρ : Representation A G W}

/-- The bottom subrepresentation carries the bottom subspace. -/
@[simp]
lemma toSubmodule_bot : (⊥ : Subrepresentation ρ).toSubmodule = ⊥ := rfl

/-- The top subrepresentation carries the top subspace. -/
@[simp]
lemma toSubmodule_top : (⊤ : Subrepresentation ρ).toSubmodule = ⊤ := rfl

end Subrepresentation
