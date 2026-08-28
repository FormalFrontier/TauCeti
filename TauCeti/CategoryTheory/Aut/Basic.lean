/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Endomorphism

/-!
# Automorphisms in a category

This file contains general bookkeeping lemmas for automorphisms of objects in a category.

## Main results

* `TauCeti.CategoryTheory.comp_aut_pow_hom_of_comp`: iterating an automorphism that reindexes a
  family of morphisms reindexes that family by the corresponding function iterate.
-/

public section

namespace TauCeti.CategoryTheory

open _root_.CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] {X Y : C} {iota : Type*}

/-- Iterating an automorphism which reindexes a family of morphisms reindexes that family by the
corresponding function iterate. -/
theorem comp_aut_pow_hom_of_comp (gamma : Aut X) (F : iota → (Y ⟶ X)) (s : iota → iota)
    (h : ∀ i, F i ≫ gamma.hom = F (s i)) (m : ℕ) (i : iota) :
    F i ≫ (gamma ^ m).hom = F ((s^[m]) i) := by
  induction m generalizing i with
  | zero =>
      rw [pow_zero, Function.iterate_zero_apply]
      -- `Aut`'s identity is definitionally `Iso.refl`; there is no hom-level power-zero lemma.
      change _ ≫ (Iso.refl _).hom = _
      rw [Iso.refl_hom, Category.comp_id]
  | succ m ih =>
      rw [pow_succ]
      -- `Aut` multiplication is reverse categorical composition, exposed here at the hom level.
      change F i ≫ gamma.hom ≫ (gamma ^ m).hom = _
      rw [← Category.assoc, h, ih, Function.iterate_succ_apply]

end TauCeti.CategoryTheory
