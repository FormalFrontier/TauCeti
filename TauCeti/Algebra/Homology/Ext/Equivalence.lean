/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import TauCeti.Algebra.Homology.Ext.Basic

/-!
# `Ext` groups are invariant under an additive equivalence

Mathlib's `CategoryTheory.Abelian.Ext.mapExactFunctor` sends `Extⁿ(X, Y)` to
`Extⁿ(F X, F Y)` for an exact additive functor `F`, and proves it bijective only under a
projective- or injective-object hypothesis.  For an equivalence no such hypothesis is needed: the
inverse equivalence supplies the inverse map, up to the transport along the unit isomorphism from
`TauCeti.extAddEquivOfIso`.

## Main definitions

* `TauCeti.extAddEquivOfEquivalence`: `Extⁿ(X, Y) ≃+ Extⁿ(e X, e Y)` for an additive equivalence
  `e`.
* `TauCeti.extLinearEquivOfEquivalence`: its `R`-linear refinement for an `R`-linear equivalence
  of `R`-linear abelian categories.  `R`-linearity of `e` is genuinely needed for the linear
  statement: an additive isomorphism of `k`-vector spaces need not preserve dimension.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

universe w v v' u u' t

variable {C : Type u} [Category.{v} C] [Abelian C] {D : Type u'} [Category.{v'} D] [Abelian D]
  [HasExt.{w} C] [HasExt.{w} D]

/-- Pushing an `Ext` class forward along an equivalence and pulling it back along the inverse
equivalence is transport along the unit isomorphism. -/
private theorem mapExactFunctor_inverse_mapExactFunctor (e : C ≌ D) [e.functor.Additive]
    {X Y : C} {n : ℕ} (α : Ext.{w} X Y n) :
    (α.mapExactFunctor e.functor).mapExactFunctor e.inverse =
      extAddEquivOfIso (e.unitIso.app X) (e.unitIso.app Y) n α := by
  have key := Ext.mapExactFunctor_comp_mk₀_natTransApp α (F := 𝟭 C)
    (G := e.functor ⋙ e.inverse) e.unitIso.hom
  rw [Ext.id_mapExactFunctor] at key
  rw [extAddEquivOfIso_apply, ← Ext.comp_mapExactFunctor]
  simp only [Iso.app_hom, Iso.app_inv]
  rw [key, Ext.mk₀_comp_mk₀_assoc]
  simp

/-- Transporting back along the unit isomorphism inverts the pushforward of an `Ext` class along
an equivalence. -/
private theorem symm_extAddEquivOfIso_mapExactFunctor (e : C ≌ D) [e.functor.Additive]
    (X Y : C) (n : ℕ) (α : Ext.{w} X Y n) :
    (extAddEquivOfIso (e.unitIso.app X) (e.unitIso.app Y) n).symm
        ((α.mapExactFunctor e.functor).mapExactFunctor e.inverse) = α := by
  rw [mapExactFunctor_inverse_mapExactFunctor]
  exact (extAddEquivOfIso _ _ n).symm_apply_apply α

/-- Pushing forward along the inverse of an equivalence is injective on `Ext` groups. -/
private theorem mapExactFunctor_inverse_injective (e : C ≌ D) [e.functor.Additive]
    (A B : D) (n : ℕ) :
    Function.Injective fun β : Ext.{w} A B n => β.mapExactFunctor e.inverse := by
  have : e.symm.functor.Additive := inferInstanceAs e.inverse.Additive
  intro β₁ β₂ h
  have h₁ := symm_extAddEquivOfIso_mapExactFunctor e.symm A B n β₁
  have h₂ := symm_extAddEquivOfIso_mapExactFunctor e.symm A B n β₂
  rw [← h₁, ← h₂]
  exact congrArg _ (congrArg (fun γ => Ext.mapExactFunctor e.symm.inverse γ) h)

/-- **`Ext` groups are invariant under an additive equivalence.**  The equivalence `e` carries
`Extⁿ(X, Y)` isomorphically onto `Extⁿ(e X, e Y)`, with the inverse supplied by the inverse
equivalence and the unit isomorphism. -/
noncomputable def extAddEquivOfEquivalence (e : C ≌ D) [e.functor.Additive] (X Y : C) (n : ℕ) :
    Ext.{w} X Y n ≃+ Ext.{w} (e.functor.obj X) (e.functor.obj Y) n where
  toFun α := α.mapExactFunctor e.functor
  invFun β := (extAddEquivOfIso (e.unitIso.app X) (e.unitIso.app Y) n).symm
    (β.mapExactFunctor e.inverse)
  map_add' α β := by simp
  left_inv α := symm_extAddEquivOfIso_mapExactFunctor e X Y n α
  right_inv β := by
    have hinj : Function.Injective fun γ : Ext.{w} (e.functor.obj X) (e.functor.obj Y) n =>
        (extAddEquivOfIso (e.unitIso.app X) (e.unitIso.app Y) n).symm
          (γ.mapExactFunctor e.inverse) :=
      (extAddEquivOfIso (e.unitIso.app X) (e.unitIso.app Y) n).symm.injective.comp
        (mapExactFunctor_inverse_injective e _ _ n)
    exact hinj (symm_extAddEquivOfIso_mapExactFunctor e X Y n _)

@[simp]
theorem extAddEquivOfEquivalence_apply (e : C ≌ D) [e.functor.Additive] {X Y : C} {n : ℕ}
    (α : Ext.{w} X Y n) :
    extAddEquivOfEquivalence e X Y n α = α.mapExactFunctor e.functor :=
  (rfl)

/-- **The `R`-linear refinement of `TauCeti.extAddEquivOfEquivalence`.**  For an `R`-linear
equivalence of `R`-linear abelian categories, `Extⁿ(X, Y)` and `Extⁿ(e X, e Y)` are isomorphic as
`R`-modules. -/
noncomputable def extLinearEquivOfEquivalence (R : Type t) [Ring R] [Linear R C] [Linear R D]
    (e : C ≌ D) [e.functor.Additive] [e.functor.Linear R] (X Y : C) (n : ℕ) :
    Ext.{w} X Y n ≃ₗ[R] Ext.{w} (e.functor.obj X) (e.functor.obj Y) n where
  __ := extAddEquivOfEquivalence e X Y n
  map_smul' r α := by simp

@[simp]
theorem extLinearEquivOfEquivalence_apply (R : Type t) [Ring R] [Linear R C] [Linear R D]
    (e : C ≌ D) [e.functor.Additive] [e.functor.Linear R] {X Y : C} {n : ℕ}
    (α : Ext.{w} X Y n) :
    extLinearEquivOfEquivalence R e X Y n α = α.mapExactFunctor e.functor :=
  (rfl)

end TauCeti
