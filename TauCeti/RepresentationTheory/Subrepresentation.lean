/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Subrepresentation
public import Mathlib.RingTheory.SimpleModule.Basic

/-!
# The underlying module of a subrepresentation

Mathlib's `Subrepresentation` API records how `toSubmodule` interacts with the lattice
operations — `Subrepresentation.toSubmodule_sup` and `Subrepresentation.toSubmodule_inf`, both
`@[simp]` and both true by `rfl` — but not how it interacts with the bounded-lattice structure,
nor how it interacts with the order relations themselves, nor how it interacts with membership.
This file adds the five missing counterparts, in the same shape. It also records that the
representation action on a subrepresentation is the restriction of the original action, that the
group-algebra action coerces to the original action, and that a subrepresentation is minimal
exactly when the `A[G]`-submodule it carries is simple.

They are stated at the typeclasses `Subrepresentation` itself asks for, so they apply wherever
the abstraction does. The `⊥` and `⊤` lemmas let proofs about extreme subrepresentations avoid
asserting the definitional unfolding of the `BoundedOrder` instance by hand; the `≤` and `<`
lemmas move an order statement between the two lattices, which is what lets a submodule-level
argument — a dimension count, say, or an orthogonal complement — settle a question about
subrepresentations; and the membership lemma does the same for a single element, so that a
carrier computed by a `toSubmodule` lemma answers a `SetLike` membership goal without unfolding
the `SetLike` instance by hand. In the same spirit,
`Subrepresentation.isSimpleModule_asSubmodule_iff` moves the notion of an irreducible constituent
across `Subrepresentation.subrepresentationSubmoduleOrderIso`, so that Mathlib's simple- and
semisimple-module API applies to minimal subrepresentations; being about `asSubmodule` it asks for
the coefficients to be a commutative ring, as `Subrepresentation.asSubmodule` and
`IsSimpleModule` between them do.

## Main results

* `Subrepresentation.mem_toSubmodule`
* `Subrepresentation.toSubmodule_bot`
* `Subrepresentation.toSubmodule_top`
* `Subrepresentation.toSubmodule_le_toSubmodule`
* `Subrepresentation.toSubmodule_lt_toSubmodule`
* `Subrepresentation.coe_toRepresentation_apply`
* `Subrepresentation.toRepresentation_apply`
* `Subrepresentation.coe_toRepresentation_asAlgebraHom_apply`
* `Subrepresentation.isSimpleModule_asSubmodule_iff`
-/

public section

namespace Subrepresentation

variable {A G W : Type*} [Semiring A] [Monoid G] [AddCommMonoid W] [Module A W]
  {ρ : Representation A G W}

/-- A vector lies in the subspace a subrepresentation carries exactly when it lies in the
subrepresentation. This is the `SetLike` instance of `Subrepresentation`, whose coercion is
`toSubmodule`, stated as a lemma so that proofs need not unfold it. -/
@[simp]
lemma mem_toSubmodule {ρ' : Subrepresentation ρ} {v : W} : v ∈ ρ'.toSubmodule ↔ v ∈ ρ' := Iff.rfl

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

/-- The action on a subrepresentation, coerced to the ambient module, is the original action. -/
@[simp]
theorem coe_toRepresentation_apply (S : Subrepresentation ρ) (g : G) (x : S.toSubmodule) :
    ((S.toRepresentation g x : S.toSubmodule) : W) = ρ g (x : W) :=
  rfl

/-- The action on a subrepresentation is the restriction of the original action. -/
theorem toRepresentation_apply (S : Subrepresentation ρ) (g : G) :
    S.toRepresentation g = (ρ g).restrict (S.apply_mem_toSubmodule g) :=
  rfl

/-- The group-algebra action on a subrepresentation, coerced to the ambient module, is the
original group-algebra action. -/
@[simp]
theorem coe_toRepresentation_asAlgebraHom_apply {k H V : Type*} [CommSemiring k] [Monoid H]
    [AddCommMonoid V] [Module k V] {σ : Representation k H V} (S : Subrepresentation σ)
    (a : MonoidAlgebra k H) (x : S.toSubmodule) :
    ((S.toRepresentation.asAlgebraHom a x : S.toSubmodule) : V) =
      σ.asAlgebraHom a (x : V) := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb =>
      simpa only [map_add, LinearMap.add_apply, Submodule.coe_add] using
        congrArg₂ (fun u v => u + v) ha hb
  | single g r =>
      simp only [Representation.asAlgebraHom_single]
      congr 1

section AsSubmodule

open scoped MonoidAlgebra

variable {A G W : Type*} [CommRing A] [Monoid G] [AddCommGroup W] [Module A W]
  {ρ : Representation A G W}

/-- A minimal subrepresentation is the same thing as a simple `A[G]`-submodule of the associated
module: the dictionary between the two ways of saying "irreducible constituent".  It is
`isSimpleModule_iff_isAtom` read across `Subrepresentation.subrepresentationSubmoduleOrderIso`. -/
@[simp]
theorem isSimpleModule_asSubmodule_iff {σ : Subrepresentation ρ} :
    IsSimpleModule A[G] σ.asSubmodule ↔ IsAtom σ :=
  isSimpleModule_iff_isAtom.trans (subrepresentationSubmoduleOrderIso.isAtom_iff σ)

end AsSubmodule

end Subrepresentation
