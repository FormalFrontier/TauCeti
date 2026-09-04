/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapAdjunction
public import TauCeti.Algebra.Homology.Ext.Basic

/-!
# `Ext` groups are invariant under an additive equivalence

Mathlib's `CategoryTheory.Adjunction.extEquiv` promotes an adjunction `F ⊣ G` between exact
functors to an additive equivalence `Extⁿ(F X, Y) ≃+ Extⁿ(X, G Y)`.  For an equivalence `e` this
specialises, along `CategoryTheory.Equivalence.toAdjunction` and the transport of the target along
the unit isomorphism from `TauCeti.extAddEquivOfIso`, to the invariance of `Ext` under `e`, which
Mathlib does not state in this form.  (`CategoryTheory.Abelian.Ext.mapExactFunctor` is shown
bijective only under a projective- or injective-object hypothesis.)

## Main definitions

* `CategoryTheory.Equivalence.extAddEquiv`: `Extⁿ(X, Y) ≃+ Extⁿ(e X, e Y)` for an additive
  equivalence `e`.
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

/-- **`Ext` groups are invariant under an additive equivalence.**  The equivalence `e` carries
`Extⁿ(X, Y)` isomorphically onto `Extⁿ(e X, e Y)`.  This is `CategoryTheory.Adjunction.extEquiv`
for the adjunction `e.functor ⊣ e.inverse`, with the target transported along the unit
isomorphism. -/
noncomputable def _root_.CategoryTheory.Equivalence.extAddEquiv
    (e : C ≌ D) [e.functor.Additive] (X Y : C) (n : ℕ) :
    Ext.{w} X Y n ≃+ Ext.{w} (e.functor.obj X) (e.functor.obj Y) n :=
  (extAddEquivOfIso (Iso.refl X) (e.unitIso.app Y) n).trans e.toAdjunction.extEquiv.symm

@[simp]
theorem _root_.CategoryTheory.Equivalence.extAddEquiv_apply
    (e : C ≌ D) [e.functor.Additive] {X Y : C} {n : ℕ}
    (α : Ext.{w} X Y n) :
    e.extAddEquiv X Y n α = α.mapExactFunctor e.functor := by
  simp [Equivalence.extAddEquiv, Adjunction.extEquiv_symm_apply, Ext.mapExactFunctor_comp,
    Ext.mapExactFunctor_mk₀]

/-- **The `R`-linear refinement of `CategoryTheory.Equivalence.extAddEquiv`.**  For an `R`-linear
equivalence of `R`-linear abelian categories, `Extⁿ(X, Y)` and `Extⁿ(e X, e Y)` are isomorphic as
`R`-modules. -/
noncomputable def extLinearEquivOfEquivalence (R : Type t) [Ring R] [Linear R C] [Linear R D]
    (e : C ≌ D) [e.functor.Additive] [e.functor.Linear R] (X Y : C) (n : ℕ) :
    Ext.{w} X Y n ≃ₗ[R] Ext.{w} (e.functor.obj X) (e.functor.obj Y) n where
  __ := e.extAddEquiv X Y n
  map_smul' r α := by simp

@[simp]
theorem extLinearEquivOfEquivalence_apply (R : Type t) [Ring R] [Linear R C] [Linear R D]
    (e : C ≌ D) [e.functor.Additive] [e.functor.Linear R] {X Y : C} {n : ℕ}
    (α : Ext.{w} X Y n) :
    extLinearEquivOfEquivalence R e X Y n α = α.mapExactFunctor e.functor :=
  e.extAddEquiv_apply α

end TauCeti
