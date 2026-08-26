/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Center.Isomorphism
public import TauCeti.Algebra.AlgebraicGroup.Semisimple.Basic

/-!
# Adjoint semisimple affine groups in Hopf coordinates

A semisimple affine group over a field is **adjoint** when its scheme-theoretic center is
trivial.  For a commutative Hopf algebra `H`, closed subgroup schemes are encoded
contravariantly by Hopf ideals.  Thus the center is trivial precisely when its defining ideal is
the augmentation ideal, which cuts out the identity subgroup.

This file packages that condition as an isomorphism-invariant property of semisimple finite-type
commutative Hopf algebras.  Its characteristic pointwise form says that every universally central
algebra-valued point is the identity.  This criterion quantifies over all commutative value
algebras; testing only rational points would miss infinitesimal centers such as `mu_p` in
characteristic `p`.

## Main declarations

* `TauCeti.adjointSemisimpleCommHopfAlgProperty`: adjointness for semisimple finite-type
  commutative Hopf algebras.
* `TauCeti.AdjointSemisimpleCommHopfAlgCat`: the corresponding full subcategory.
* `TauCeti.adjointSemisimpleCommHopfAlgProperty_iff_forall_isCentralPoint_eq_one`: adjointness is
  equivalent to triviality of every universally central algebra-valued point.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§1.k and 21.4.
* T. A. Springer, *Linear Algebraic Groups*, §9.6.

This supplies the adjoint-form definition in Layer 6, "Reductive and semisimple groups", of the
ReductiveGroups roadmap.  Construction of the adjoint quotient and the classification of adjoint
forms remain downstream.
-/

public section

open CategoryTheory WithConv

namespace TauCeti

universe u

noncomputable section

variable {k : Type u} [Field k]

/-- The object property selecting adjoint semisimple affine groups in Hopf coordinates.

An object is already semisimple by belonging to `SemisimpleCommHopfAlgCat k`.  Adjointness says
that its represented center is the identity subgroup, so the center defining ideal is the
augmentation ideal. -/
def adjointSemisimpleCommHopfAlgProperty (k : Type u) [Field k] :
    ObjectProperty (SemisimpleCommHopfAlgCat.{u} k) :=
  fun H => CommHopfAlgCat.centerDefiningIdeal H.obj.obj = HopfIdeal.augmentation k H.obj.obj

/-- Membership in the adjoint property means that the center defining ideal is the augmentation
ideal. -/
@[simp]
theorem adjointSemisimpleCommHopfAlgProperty_iff
    (H : SemisimpleCommHopfAlgCat.{u} k) :
    adjointSemisimpleCommHopfAlgProperty k H ↔
      CommHopfAlgCat.centerDefiningIdeal H.obj.obj = HopfIdeal.augmentation k H.obj.obj :=
  Iff.rfl

namespace adjointSemisimpleCommHopfAlgProperty

variable {H : SemisimpleCommHopfAlgCat.{u} k}

/-- Every universally central point of an adjoint semisimple affine group is the identity. -/
theorem isCentralPoint_eq_one
    (hH : adjointSemisimpleCommHopfAlgProperty k H)
    (A : CommAlgCat.{u} k)
    (g : HopfAlgebra.points (R := k) (H := H.obj.obj) A)
    (hg : HopfAlgebra.IsCentralPoint g) : g = 1 := by
  exact
    (CommHopfAlgCat.centerDefiningIdeal_eq_augmentation_iff_forall_isCentralPoint_eq_one
      H.obj.obj).1 hH A g hg

end adjointSemisimpleCommHopfAlgProperty

/-- A semisimple affine group is adjoint exactly when every universally central point over every
commutative value algebra is the identity. -/
theorem adjointSemisimpleCommHopfAlgProperty_iff_forall_isCentralPoint_eq_one
    (H : SemisimpleCommHopfAlgCat.{u} k) :
    adjointSemisimpleCommHopfAlgProperty k H ↔
      ∀ (A : CommAlgCat.{u} k)
        (g : HopfAlgebra.points (R := k) (H := H.obj.obj) A),
        HopfAlgebra.IsCentralPoint g → g = 1 :=
  CommHopfAlgCat.centerDefiningIdeal_eq_augmentation_iff_forall_isCentralPoint_eq_one H.obj.obj

/-- Adjointness of semisimple commutative Hopf algebras is invariant under isomorphism. -/
instance (k : Type u) [Field k] :
    (adjointSemisimpleCommHopfAlgProperty k).IsClosedUnderIsomorphisms where
  of_iso {H K} e hH := by
    let e₁ : H.obj.obj ≅ K.obj.obj :=
      { hom := e.hom.hom.hom
        inv := e.inv.hom.hom
        hom_inv_id := by simp
        inv_hom_id := by simp }
    let f : H.obj.obj →ₐc[k] K.obj.obj := e₁.hom.hom
    have hf : Function.Surjective f := ConcreteCategory.bijective_of_isIso e₁.hom |>.2
    apply (adjointSemisimpleCommHopfAlgProperty_iff K).2
    apply (HopfIdeal.comap_eq_comap_iff_of_surjective e₁.hom.hom hf).mp
    calc
      (CommHopfAlgCat.centerDefiningIdeal K.obj.obj).comap e₁.hom.hom hf =
          CommHopfAlgCat.centerDefiningIdeal H.obj.obj := by
        simpa only using CommHopfAlgCat.comap_centerDefiningIdeal e₁
      _ = HopfIdeal.augmentation k H.obj.obj :=
        (adjointSemisimpleCommHopfAlgProperty_iff H).1 hH
      _ = (HopfIdeal.augmentation k K.obj.obj).comap e₁.hom.hom hf := by
        simpa only using (HopfIdeal.comap_augmentation e₁.hom.hom hf).symm

/-- The category of adjoint semisimple finite-type commutative Hopf algebras over a field. -/
abbrev AdjointSemisimpleCommHopfAlgCat (k : Type u) [Field k] :=
  (adjointSemisimpleCommHopfAlgProperty k).FullSubcategory

end

end TauCeti
