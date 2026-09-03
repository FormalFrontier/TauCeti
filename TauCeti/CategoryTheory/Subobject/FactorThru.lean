/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Subobject.FactorThru

/-!
# Factorizations through subobjects

This file records two elementary forms of the universal property of a subobject. Factoring is
unchanged by precomposition with an equality-induced isomorphism, and a factorization through a
subobject is unique because its representing arrow is a monomorphism.

## Main declarations

* `CategoryTheory.Subobject.factors_eqToHom_comp_iff`: precomposition by an equality-induced
  isomorphism does not change whether a morphism factors through a subobject.
* `CategoryTheory.Subobject.factors_iff_existsUnique`: factoring through a subobject is equivalent
  to the existence of a unique lift.
-/

public section

open CategoryTheory

namespace TauCeti

universe v u

variable {C : Type u} [Category.{v} C] {X Y Z : C}

/-- Factoring through a subobject is unchanged after precomposing with the isomorphism induced by
an equality of source objects. -/
theorem _root_.CategoryTheory.Subobject.factors_eqToHom_comp_iff (P : Subobject Z) (hXY : X = Y)
    (f : Y ⟶ Z) : P.Factors (eqToHom hXY ≫ f) ↔ P.Factors f := by
  constructor
  · rw [Subobject.factors_iff, Subobject.factors_iff]
    rintro ⟨g, hg⟩
    refine ⟨eqToHom hXY.symm ≫ g, ?_⟩
    rw [Category.assoc, hg, ← Category.assoc]
    simp
  · exact Subobject.factors_of_factors_right _

/-- A morphism factors through a subobject exactly when it has a unique lift through the
subobject's representing arrow. -/
theorem _root_.CategoryTheory.Subobject.factors_iff_existsUnique (P : Subobject Y) (f : X ⟶ Y) :
    P.Factors f ↔ ∃! g : X ⟶ (P : C), g ≫ P.arrow = f := by
  constructor
  · intro hf
    refine ⟨P.factorThru f hf, P.factorThru_arrow f hf, ?_⟩
    intro g' hg'
    apply (cancel_mono P.arrow).mp
    rw [hg', P.factorThru_arrow]
  · rintro ⟨g, hg, -⟩
    rw [← hg]
    exact Subobject.factors_comp_arrow g

end TauCeti
