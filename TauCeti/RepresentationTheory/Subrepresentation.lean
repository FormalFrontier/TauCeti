/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.Projection
public import Mathlib.RepresentationTheory.Intertwining
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

Complementarity is the same story one step further: complementary subrepresentations carry
complementary subspaces (`Subrepresentation.isCompl_toSubmodule`), so the linear projection onto
one of them along the other is available, and it is equivariant
(`Subrepresentation.isIntertwiningMap_projectionOnto`) exactly because the complement is a
subrepresentation and not merely a subspace.  That is the usual source of an equivariant
projection onto a summand of a semisimple representation.

## Main results

* `Subrepresentation.toSubmodule_bot`
* `Subrepresentation.toSubmodule_top`
* `Subrepresentation.toSubmodule_le_toSubmodule`
* `Subrepresentation.toSubmodule_lt_toSubmodule`
* `Subrepresentation.isCompl_toSubmodule`
* `Subrepresentation.isIntertwiningMap_projectionOnto`
-/

public section

namespace Subrepresentation

section Order

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

/-- Complementary subrepresentations carry complementary subspaces. -/
theorem isCompl_toSubmodule {ρ₁ ρ₂ : Subrepresentation ρ} (h : IsCompl ρ₁ ρ₂) :
    IsCompl ρ₁.toSubmodule ρ₂.toSubmodule where
  disjoint := by
    rw [disjoint_iff, ← toSubmodule_inf, disjoint_iff.mp h.disjoint, toSubmodule_bot]
  codisjoint := by
    rw [codisjoint_iff, ← toSubmodule_sup, codisjoint_iff.mp h.codisjoint, toSubmodule_top]

end Order

section Projection

variable {A G W : Type*} [Ring A] [Monoid G] [AddCommGroup W] [Module A W]
  {ρ : Representation A G W} {ρ₁ ρ₂ : Subrepresentation ρ}

/-- The projection onto a subrepresentation along a complementary *subrepresentation* is
equivariant, so it is an intertwining map from the whole representation onto the summand.

Equivariance is exactly what the complement being stable buys: `ρ g` preserves both summands, so
it commutes with the splitting of a vector into its two components. -/
theorem isIntertwiningMap_projectionOnto (h : IsCompl ρ₁ ρ₂) :
    Representation.IsIntertwiningMap ρ ρ₁.toRepresentation
      (Submodule.projectionOnto ρ₁.toSubmodule ρ₂.toSubmodule (isCompl_toSubmodule h)) where
  isIntertwining g v := by
    set hc := isCompl_toSubmodule h
    set P := Submodule.projectionOnto ρ₁.toSubmodule ρ₂.toSubmodule hc
    obtain ⟨a, b, hab, -⟩ := Submodule.existsUnique_add_of_isCompl hc v
    subst hab
    have h1 : P (ρ g (a : W)) = ρ₁.toRepresentation g a :=
      Submodule.projectionOnto_apply_of_mem_left hc (ρ₁.apply_mem_toSubmodule g a.2)
    have h2 : P (ρ g (b : W)) = 0 :=
      Submodule.projectionOnto_apply_of_mem_right hc (ρ₂.apply_mem_toSubmodule g b.2)
    have h3 : P (a : W) = a := Submodule.projectionOnto_apply_left hc a
    have h4 : P (b : W) = 0 := Submodule.projectionOnto_apply_right hc b
    rw [map_add, map_add, map_add, h1, h2, h3, h4, add_zero, add_zero]

end Projection

end Subrepresentation
