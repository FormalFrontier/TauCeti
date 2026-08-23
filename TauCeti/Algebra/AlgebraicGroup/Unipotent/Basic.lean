/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.CategoryTheory.ObjectProperty.CompleteLattice
public import TauCeti.Algebra.AlgebraicGroup.FiniteType.CommHopfAlgCat
public import TauCeti.Algebra.AlgebraicGroup.Representation.JordanDecomposition.Basic
public import TauCeti.Algebra.AlgebraicGroup.Smooth.CommHopfAlgCat

/-!
# Smooth unipotent affine groups

A smooth finite-type affine group over a field is unipotent when every point over an algebraic
closure is a unipotent element. On coordinate Hopf algebras, a geometric point is an algebra map
`H →ₐ[k] AlgebraicClosure k`, and its action on every finite-dimensional comodule supplies the
representation-theoretic test for unipotence. Smoothness is included explicitly because geometric
points alone do not detect infinitesimal structure in nonreduced group schemes.

This file packages the geometric-point criterion as an object property on commutative Hopf
algebras, separately from smoothness, and combines the two properties for the finite-type smooth
case. It also packages the smooth conjunction as a full subcategory. The equivalent nilpotence
and Jordan-factor characterizations make the pointwise property usable without unfolding it.

This pointwise criterion is not offered as a definition for nonreduced group schemes: for example,
both `αₚ` and `μₚ` have only the identity as an algebraic-closure-valued point in characteristic
`p`, although only `αₚ` is unipotent scheme-theoretically. A future scheme-theoretic definition
must instead detect infinitesimal points.

## Main declarations

* `TauCeti.geometricallyUnipotentPointsCommHopfAlgProperty`: the property that every geometric
  point is unipotent; this is used together with smoothness.
* `TauCeti.smoothUnipotentCommHopfAlgProperty`: the geometric unipotence property for smooth
  finite-type commutative Hopf algebras over a field.
* `geometricallyUnipotentPointsCommHopfAlgProperty_iff_forall_isNilpotent_endOfPoint_sub_one`:
  the criterion that every geometric point acts with nilpotent difference from the identity.
* `TauCeti.geometricallyUnipotentPointsCommHopfAlgProperty_iff_forall_unipotentPart_eq_self` and
  `TauCeti.geometricallyUnipotentPointsCommHopfAlgProperty_iff_forall_semisimplePart_eq_one`: the
  pointwise Jordan characterizations.
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

universe u v

/-- The object property asserting that every algebraic-closure-valued point acts unipotently in
every finite-dimensional representation.

This geometric-point criterion is kept separate from smoothness, as required by the roadmap. It
is not by itself a definition of unipotence for nonreduced group schemes, whose infinitesimal
structure is invisible to algebraic-closure-valued points. -/
def geometricallyUnipotentPointsCommHopfAlgProperty (k : Type u) [Field k] :
    ObjectProperty (CommHopfAlgCat.{v} k) :=
  fun H ↦ ∀ g : WithConv (H →ₐ[k] AlgebraicClosure k),
    HopfAlgebra.IsUnipotentPoint g

/-- Membership in the geometric-point unipotence property means that every
algebraic-closure-valued point acts unipotently in every finite-dimensional representation. -/
@[simp]
theorem geometricallyUnipotentPointsCommHopfAlgProperty_iff (k : Type u) [Field k]
    (H : CommHopfAlgCat.{v} k) :
    geometricallyUnipotentPointsCommHopfAlgProperty k H ↔
      ∀ g : WithConv (H →ₐ[k] AlgebraicClosure k),
        HopfAlgebra.IsUnipotentPoint g :=
  Iff.rfl

/-- The geometric-point unipotence property is invariant under isomorphisms of commutative Hopf
algebras. -/
instance (k : Type u) [Field k] :
    (geometricallyUnipotentPointsCommHopfAlgProperty k :
      ObjectProperty (CommHopfAlgCat.{v} k)).IsClosedUnderIsomorphisms where
  of_iso {H K} e hH g := by
    let e' : H ≃ₐc[k] K := CommHopfAlgCat.ofIso e
    apply (HopfAlgebra.isUnipotentPoint_mapDomain_iff e' g).mp
    exact hH _

/-- Every geometric point is unipotent exactly when every such point acts with nilpotent
difference from the identity in every finite-dimensional comodule. -/
theorem geometricallyUnipotentPointsCommHopfAlgProperty_iff_forall_isNilpotent_endOfPoint_sub_one
    (k : Type u) [Field k] (H : CommHopfAlgCat.{v} k) :
    geometricallyUnipotentPointsCommHopfAlgProperty k H ↔
      ∀ (g : WithConv (H →ₐ[k] AlgebraicClosure k))
        (M : FGComoduleCat.{u, v, u} k H),
          _root_.IsNilpotent (Comodule.endOfPoint M g.ofConv - 1) := by
  rw [geometricallyUnipotentPointsCommHopfAlgProperty_iff]
  apply forall_congr'
  exact HopfAlgebra.isUnipotentPoint_iff_forall_isNilpotent_endOfPoint_sub_one

/-- Every geometric point is unipotent exactly when its unipotent part is the point itself. -/
theorem geometricallyUnipotentPointsCommHopfAlgProperty_iff_forall_unipotentPart_eq_self
    (k : Type u) [Field k] (H : CommHopfAlgCat.{u} k) :
    geometricallyUnipotentPointsCommHopfAlgProperty k H ↔
      ∀ g : WithConv (H →ₐ[k] AlgebraicClosure k),
        HopfAlgebra.Point.unipotentPart k H (AlgebraicClosure k) g = g := by
  rw [geometricallyUnipotentPointsCommHopfAlgProperty_iff]
  apply forall_congr'
  exact HopfAlgebra.Point.isUnipotentPoint_iff_unipotentPart_eq_self k H
    (AlgebraicClosure k)

/-- Every geometric point is unipotent exactly when its semisimple part is the identity. -/
theorem geometricallyUnipotentPointsCommHopfAlgProperty_iff_forall_semisimplePart_eq_one
    (k : Type u) [Field k] (H : CommHopfAlgCat.{u} k) :
    geometricallyUnipotentPointsCommHopfAlgProperty k H ↔
      ∀ g : WithConv (H →ₐ[k] AlgebraicClosure k),
        HopfAlgebra.Point.semisimplePart k H (AlgebraicClosure k) g = 1 := by
  rw [geometricallyUnipotentPointsCommHopfAlgProperty_iff]
  apply forall_congr'
  exact HopfAlgebra.Point.isUnipotentPoint_iff_semisimplePart_eq_one k H
    (AlgebraicClosure k)

/-- The object property selecting smooth finite-type affine groups whose every geometric point is
unipotent.

The point predicate tests the action on every finitely generated comodule, which over a field is
the finite-dimensional representation-theoretic definition. The smoothness condition excludes the
infinitesimal nonreduced obstruction that algebraic-closure-valued points cannot detect. -/
def smoothUnipotentCommHopfAlgProperty (k : Type u) [Field k] :
    ObjectProperty (FiniteTypeCommHopfAlgCat.{u, v} k) :=
  ((smoothCommHopfAlgProperty k) ⊓ geometricallyUnipotentPointsCommHopfAlgProperty k).inverseImage
    (forget₂ (FiniteTypeCommHopfAlgCat.{u, v} k) (CommHopfAlgCat.{v} k))

/-- Membership in the smooth unipotent property means smoothness together with every
algebraic-closure-valued point acting unipotently in every finite-dimensional representation. -/
@[simp]
theorem smoothUnipotentCommHopfAlgProperty_iff (k : Type u) [Field k]
    (H : FiniteTypeCommHopfAlgCat.{u, v} k) :
    smoothUnipotentCommHopfAlgProperty k H ↔
      Algebra.Smooth k H ∧
        ∀ g : WithConv (H →ₐ[k] AlgebraicClosure k),
          HopfAlgebra.IsUnipotentPoint g := by
  rw [smoothUnipotentCommHopfAlgProperty, ObjectProperty.prop_inverseImage_iff,
    ObjectProperty.prop_inf_iff,
    FiniteTypeCommHopfAlgCat.forget₂_commHopfAlgCat_obj,
    smoothCommHopfAlgProperty_iff, geometricallyUnipotentPointsCommHopfAlgProperty_iff]

/-- Smooth geometric-point unipotence is invariant under isomorphisms of finite-type commutative
Hopf algebras. -/
instance (k : Type u) [Field k] :
    (smoothUnipotentCommHopfAlgProperty k :
      ObjectProperty (FiniteTypeCommHopfAlgCat.{u, v} k)).IsClosedUnderIsomorphisms := by
  unfold smoothUnipotentCommHopfAlgProperty
  infer_instance

/-- The category of smooth finite-type unipotent coordinate Hopf algebras over a field. -/
abbrev SmoothUnipotentCommHopfAlgCat (k : Type u) [Field k] :=
  (smoothUnipotentCommHopfAlgProperty k).FullSubcategory

end TauCeti
