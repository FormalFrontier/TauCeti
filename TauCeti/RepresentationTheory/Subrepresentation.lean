/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RepresentationTheory.Subrepresentation

/-!
# `toSubmodule` against the order on subrepresentations

Mathlib's `Subrepresentation` API records how `toSubmodule` interacts with the lattice
operations — `Subrepresentation.toSubmodule_sup` and `Subrepresentation.toSubmodule_inf`, both
`@[simp]` and both true by `rfl` — but not how it interacts with the bounded-lattice structure,
nor how it interacts with the order relations themselves. This file adds the four missing
counterparts, in the same shape.

They are stated at the typeclasses `Subrepresentation` itself asks for, so they apply wherever
the abstraction does. The `⊥` and `⊤` lemmas let proofs about extreme subrepresentations avoid
asserting the definitional unfolding of the `BoundedOrder` instance by hand; the `≤` and `<`
lemmas move an order statement between the two lattices, which is what lets a submodule-level
argument — a dimension count, say, or an orthogonal complement — settle a question about
subrepresentations.

## Main results

* `Subrepresentation.toSubmodule_bot`
* `Subrepresentation.toSubmodule_top`
* `Subrepresentation.toSubmodule_le_toSubmodule`
* `Subrepresentation.toSubmodule_lt_toSubmodule`
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

/-- One subrepresentation is contained in another exactly when the subspace it carries is. -/
@[simp]
lemma toSubmodule_le_toSubmodule {ρ₁ ρ₂ : Subrepresentation ρ} :
    ρ₁.toSubmodule ≤ ρ₂.toSubmodule ↔ ρ₁ ≤ ρ₂ := Iff.rfl

/-- One subrepresentation is strictly contained in another exactly when the subspace it carries
is. -/
@[simp]
lemma toSubmodule_lt_toSubmodule {ρ₁ ρ₂ : Subrepresentation ρ} :
    ρ₁.toSubmodule < ρ₂.toSubmodule ↔ ρ₁ < ρ₂ := by
  simp only [lt_iff_le_not_ge, toSubmodule_le_toSubmodule]

end Subrepresentation
