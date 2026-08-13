/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.CategoryTheory.ObjectProperty.CompleteLattice
public import TauCeti.Algebra.AlgebraicGroup.FiniteType.CommHopfAlgCat
public import TauCeti.Algebra.AlgebraicGroup.Representation.JordanDecomposition
public import TauCeti.Algebra.AlgebraicGroup.Smooth.CommHopfAlgCat

/-!
# Smooth unipotent affine groups

A smooth finite-type affine group over a field is unipotent when every point over an algebraic
closure is a unipotent element. On coordinate Hopf algebras, a geometric point is an algebra map
`H →ₐ[k] AlgebraicClosure k`, and its action on every finite-dimensional comodule supplies the
representation-theoretic test for unipotence. Smoothness is included explicitly because geometric
points alone do not detect infinitesimal structure in nonreduced group schemes.

This file packages the geometric-point criterion as an object property on finite-type commutative
Hopf algebras, separately from smoothness, and combines the two properties for the smooth case.
It also packages the smooth conjunction as a full subcategory. The equivalent nilpotence and
Jordan-factor characterizations make both properties usable without unfolding them.

This pointwise criterion is not offered as a definition for nonreduced group schemes: for example,
both `αₚ` and `μₚ` have only the identity as an algebraic-closure-valued point in characteristic
`p`, although only `αₚ` is unipotent scheme-theoretically. A future scheme-theoretic definition
must instead detect infinitesimal points.

## Main declarations

* `TauCeti.unipotentPointsCommHopfAlgProperty`: the property that every geometric point is
  unipotent; this is used together with smoothness.
* `TauCeti.smoothUnipotentCommHopfAlgProperty`: the geometric unipotence property for smooth
  finite-type commutative Hopf algebras over a field.
* `TauCeti.unipotentPointsCommHopfAlgProperty_iff_forall_isNilpotent_endOfPoint_sub_one`: the
  criterion that every geometric point acts with nilpotent difference from the identity.
* `TauCeti.smoothUnipotentCommHopfAlgProperty_iff_unipotentPart_eq_self`: the characterization by
  pointwise Jordan decomposition.
* `TauCeti.smoothUnipotentCommHopfAlgProperty_iff_semisimplePart_eq_one`: the characterization by
  trivial semisimple parts.
* `TauCeti.SmoothUnipotentCommHopfAlgCat`: the full subcategory of smooth unipotent coordinate
  Hopf algebras.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, I.2.
* T. A. Springer, *Linear Algebraic Groups*, §2.4.

This supplies the smooth case of the geometric definition required by Layer 5, "Unipotent
groups", of the ReductiveGroups roadmap.
-/

public section

open CategoryTheory WithConv

namespace TauCeti

universe u

/-- The object property asserting that every algebraic-closure-valued point acts unipotently in
every finite-dimensional representation.

This geometric-point criterion is kept separate from smoothness, as required by the roadmap. It
is not by itself a definition of unipotence for nonreduced group schemes, whose infinitesimal
structure is invisible to algebraic-closure-valued points. -/
def unipotentPointsCommHopfAlgProperty (k : Type u) [Field k] :
    ObjectProperty (FiniteTypeCommHopfAlgCat.{u, u} k) :=
  fun H ↦ ∀ g : WithConv (H →ₐ[k] AlgebraicClosure k),
    HopfAlgebra.IsUnipotentPoint g

/-- Membership in the geometric-point unipotence property means that every
algebraic-closure-valued point acts unipotently in every finite-dimensional representation. -/
@[simp]
theorem unipotentPointsCommHopfAlgProperty_iff (k : Type u) [Field k]
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    unipotentPointsCommHopfAlgProperty k H ↔
      ∀ g : WithConv (H →ₐ[k] AlgebraicClosure k),
        HopfAlgebra.IsUnipotentPoint g :=
  Iff.rfl

/-- The geometric-point unipotence property is invariant under isomorphisms of finite-type
commutative Hopf algebras. -/
instance (k : Type u) [Field k] :
    (unipotentPointsCommHopfAlgProperty k).IsClosedUnderIsomorphisms where
  of_iso {H K} e hH g := by
    let f := FiniteTypeCommHopfAlgCat.toBialgHom e.hom
    let f' := FiniteTypeCommHopfAlgCat.toBialgHom e.inv
    have h := (hH (AlgHom.mapDomain f g)).mapDomain f'
    have hcomp : f.comp f' = BialgHom.id k K := by
      rw [← FiniteTypeCommHopfAlgCat.toBialgHom_comp, e.inv_hom_id,
        FiniteTypeCommHopfAlgCat.toBialgHom_id]
    have hg : AlgHom.mapDomain f' (AlgHom.mapDomain f g) = g := by
      calc
        AlgHom.mapDomain f' (AlgHom.mapDomain f g) = AlgHom.mapDomain (f.comp f') g :=
          (DFunLike.congr_fun (AlgHom.mapDomain_comp f f') g).symm
        _ = AlgHom.mapDomain (BialgHom.id k K) g := by rw [hcomp]
        _ = g := DFunLike.congr_fun AlgHom.mapDomain_id g
    rwa [hg] at h

/-- Every geometric point is unipotent exactly when every such point acts with nilpotent
difference from the identity in every finite-dimensional comodule. -/
theorem unipotentPointsCommHopfAlgProperty_iff_forall_isNilpotent_endOfPoint_sub_one
    (k : Type u) [Field k] (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    unipotentPointsCommHopfAlgProperty k H ↔
      ∀ (g : WithConv (H →ₐ[k] AlgebraicClosure k))
        (M : FGComoduleCat.{u, u, u} k H),
          _root_.IsNilpotent (Comodule.endOfPoint M g.ofConv - 1) := by
  rw [unipotentPointsCommHopfAlgProperty_iff]
  apply forall_congr'
  exact HopfAlgebra.isUnipotentPoint_iff_forall_isNilpotent_endOfPoint_sub_one

/-- Every geometric point is unipotent exactly when its unipotent part is the point itself. -/
theorem unipotentPointsCommHopfAlgProperty_iff_unipotentPart_eq_self
    (k : Type u) [Field k] (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    unipotentPointsCommHopfAlgProperty k H ↔
      ∀ g : WithConv (H →ₐ[k] AlgebraicClosure k),
        HopfAlgebra.Point.unipotentPart k H (AlgebraicClosure k) g = g := by
  rw [unipotentPointsCommHopfAlgProperty_iff]
  apply forall_congr'
  exact HopfAlgebra.Point.isUnipotentPoint_iff_unipotentPart_eq_self k H
    (AlgebraicClosure k)

/-- Every geometric point is unipotent exactly when its semisimple part is the identity. -/
theorem unipotentPointsCommHopfAlgProperty_iff_semisimplePart_eq_one
    (k : Type u) [Field k] (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    unipotentPointsCommHopfAlgProperty k H ↔
      ∀ g : WithConv (H →ₐ[k] AlgebraicClosure k),
        HopfAlgebra.Point.semisimplePart k H (AlgebraicClosure k) g = 1 := by
  rw [unipotentPointsCommHopfAlgProperty_iff]
  apply forall_congr'
  exact HopfAlgebra.Point.isUnipotentPoint_iff_semisimplePart_eq_one k H
    (AlgebraicClosure k)

/-- The object property selecting smooth finite-type affine groups whose every geometric point is
unipotent.

The point predicate tests the action on every finitely generated comodule, which over a field is
the finite-dimensional representation-theoretic definition. The smoothness condition ensures that
the algebraic-closure-valued points detect the group scheme. -/
def smoothUnipotentCommHopfAlgProperty (k : Type u) [Field k] :
    ObjectProperty (FiniteTypeCommHopfAlgCat.{u, u} k) :=
  (smoothCommHopfAlgProperty k).inverseImage
      (forget₂ (FiniteTypeCommHopfAlgCat.{u, u} k) (CommHopfAlgCat.{u} k)) ⊓
    unipotentPointsCommHopfAlgProperty k

/-- Membership in the smooth unipotent property means smoothness together with every
algebraic-closure-valued point acting unipotently in every finite-dimensional representation. -/
@[simp]
theorem smoothUnipotentCommHopfAlgProperty_iff (k : Type u) [Field k]
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    smoothUnipotentCommHopfAlgProperty k H ↔
      Algebra.Smooth k H ∧
        ∀ g : WithConv (H →ₐ[k] AlgebraicClosure k),
          HopfAlgebra.IsUnipotentPoint g := by
  rw [smoothUnipotentCommHopfAlgProperty, ObjectProperty.prop_inf_iff,
    ObjectProperty.prop_inverseImage_iff,
    FiniteTypeCommHopfAlgCat.forget₂_commHopfAlgCat_obj,
    smoothCommHopfAlgProperty_iff, unipotentPointsCommHopfAlgProperty_iff]

/-- Smooth geometric-point unipotence is invariant under isomorphisms of finite-type commutative
Hopf algebras. -/
instance (k : Type u) [Field k] :
    (smoothUnipotentCommHopfAlgProperty k).IsClosedUnderIsomorphisms := by
  unfold smoothUnipotentCommHopfAlgProperty
  infer_instance

/-- A smooth finite-type affine group is unipotent exactly when every geometric point acts on
every finite-dimensional comodule with nilpotent difference from the identity. -/
theorem smoothUnipotentCommHopfAlgProperty_iff_forall_isNilpotent_endOfPoint_sub_one
    (k : Type u) [Field k] (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    smoothUnipotentCommHopfAlgProperty k H ↔
      Algebra.Smooth k H ∧
        ∀ (g : WithConv (H →ₐ[k] AlgebraicClosure k))
          (M : FGComoduleCat.{u, u, u} k H),
            _root_.IsNilpotent (Comodule.endOfPoint M g.ofConv - 1) := by
  rw [smoothUnipotentCommHopfAlgProperty_iff]
  refine and_congr_right fun _ ↦ ?_
  apply forall_congr'
  exact HopfAlgebra.isUnipotentPoint_iff_forall_isNilpotent_endOfPoint_sub_one

/-- A smooth finite-type affine group is unipotent exactly when the unipotent part of every
geometric point is the point itself. -/
theorem smoothUnipotentCommHopfAlgProperty_iff_unipotentPart_eq_self
    (k : Type u) [Field k] (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    smoothUnipotentCommHopfAlgProperty k H ↔
      Algebra.Smooth k H ∧
        ∀ g : WithConv (H →ₐ[k] AlgebraicClosure k),
          HopfAlgebra.Point.unipotentPart k H (AlgebraicClosure k) g = g := by
  rw [smoothUnipotentCommHopfAlgProperty_iff]
  exact and_congr_right fun _ ↦ forall_congr'
    (HopfAlgebra.Point.isUnipotentPoint_iff_unipotentPart_eq_self
      k H (AlgebraicClosure k))

/-- A smooth finite-type affine group is unipotent exactly when the semisimple part of every
geometric point is the identity. -/
theorem smoothUnipotentCommHopfAlgProperty_iff_semisimplePart_eq_one
    (k : Type u) [Field k] (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    smoothUnipotentCommHopfAlgProperty k H ↔
      Algebra.Smooth k H ∧
        ∀ g : WithConv (H →ₐ[k] AlgebraicClosure k),
          HopfAlgebra.Point.semisimplePart k H (AlgebraicClosure k) g = 1 := by
  rw [smoothUnipotentCommHopfAlgProperty_iff]
  exact and_congr_right fun _ ↦ forall_congr'
    (HopfAlgebra.Point.isUnipotentPoint_iff_semisimplePart_eq_one
      k H (AlgebraicClosure k))

/-- The category of smooth finite-type unipotent coordinate Hopf algebras over a field. -/
abbrev SmoothUnipotentCommHopfAlgCat (k : Type u) [Field k] :=
  (smoothUnipotentCommHopfAlgProperty k).FullSubcategory

end TauCeti
