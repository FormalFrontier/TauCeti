/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.CommHopfAlgCat
public import Mathlib.CategoryTheory.ObjectProperty.CompleteLattice
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import TauCeti.Algebra.AlgebraicGroup.Representation.JordanDecomposition.Naturality
public import TauCeti.Algebra.AlgebraicGroup.Representation.SemisimplePoint

/-!
# Geometric semisimple points of affine groups

This file packages the condition that every algebraic-closure-valued point of a commutative Hopf
algebra is semisimple. It also uses the generic transport and product results to prove
that this object property is invariant under isomorphisms and closed under tensor products.

## Main declarations

* `TauCeti.geometricallySemisimplePointsCommHopfAlgProperty`: the object property asserting that
  every algebraic-closure-valued point is semisimple.
* `TauCeti.geometricallySemisimplePointsCommHopfAlgProperty_of_surjective`: closed subgroups of a
  group with semisimple geometric points again have semisimple geometric points.
* `TauCeti.geometricallySemisimplePointsCommHopfAlgProperty.tensorProduct`: geometric semisimplicity
  is closed under direct products of affine groups.

## References

* T. A. Springer, *Linear Algebraic Groups*, §2.4.
* J. S. Milne, *Algebraic Groups* (2017), §12.c.

This supplies generic geometric semisimple-point infrastructure used by Layer 4 of the
ReductiveGroups roadmap.
-/

public section

open CategoryTheory WithConv
open scoped TensorProduct

namespace TauCeti

universe u v w x

section ObjectProperty

variable (k : Type u) [Field k]

/-- The object property asserting that every algebraic-closure-valued point of a commutative Hopf
algebra is a semisimple point. -/
def geometricallySemisimplePointsCommHopfAlgProperty :
    ObjectProperty (CommHopfAlgCat.{v} k) :=
  fun H ↦ ∀ g : WithConv (H →ₐ[k] AlgebraicClosure k),
    HopfAlgebra.IsSemisimplePoint g

/-- Membership in `geometricallySemisimplePointsCommHopfAlgProperty` means that every geometric
point is semisimple. -/
@[simp]
theorem geometricallySemisimplePointsCommHopfAlgProperty_iff
    (H : CommHopfAlgCat.{v} k) :
    geometricallySemisimplePointsCommHopfAlgProperty k H ↔
      ∀ g : WithConv (H →ₐ[k] AlgebraicClosure k),
        HopfAlgebra.IsSemisimplePoint g :=
  Iff.rfl

/-- The geometric-point semisimplicity property is invariant under isomorphisms of commutative Hopf
algebras. -/
instance :
    (geometricallySemisimplePointsCommHopfAlgProperty k :
      ObjectProperty (CommHopfAlgCat.{v} k)).IsClosedUnderIsomorphisms where
  of_iso {H K} e hH g := by
    let e' : H ≃ₐc[k] K := CommHopfAlgCat.ofIso e
    apply (HopfAlgebra.isSemisimplePoint_mapDomain_iff e' g).mp
    exact hH _

/-- Geometric-point semisimplicity descends along a surjective morphism of coordinate Hopf
algebras. Contravariantly, closed subgroups of a group with semisimple geometric points again
have semisimple geometric points. -/
theorem geometricallySemisimplePointsCommHopfAlgProperty_of_surjective
    {H K : CommHopfAlgCat.{u} k}
    (f : H ⟶ K) (hf : Function.Surjective f.hom)
    (hH : geometricallySemisimplePointsCommHopfAlgProperty k H) :
    geometricallySemisimplePointsCommHopfAlgProperty k K := by
  rw [geometricallySemisimplePointsCommHopfAlgProperty_iff] at hH ⊢
  intro g
  apply (HopfAlgebra.isSemisimplePoint_mapDomain_iff_of_surjective f.hom hf g).mp
  exact hH _

/-- The tensor product of two coordinate Hopf algebras with semisimple geometric points again has
only semisimple geometric points. Contravariantly, geometric-point semisimplicity is closed under
direct products of affine groups. -/
theorem geometricallySemisimplePointsCommHopfAlgProperty.tensorProduct
    (H K : CommHopfAlgCat.{v} k)
    (hH : geometricallySemisimplePointsCommHopfAlgProperty k H)
    (hK : geometricallySemisimplePointsCommHopfAlgProperty k K) :
    geometricallySemisimplePointsCommHopfAlgProperty k
      (CommHopfAlgCat.of k (H ⊗[k] K)) := by
  rw [geometricallySemisimplePointsCommHopfAlgProperty_iff] at hH hK ⊢
  intro g
  rw [HopfAlgebra.isSemisimplePoint_pointsMulEquiv_iff]
  exact ⟨hH _, hK _⟩

/-- Every geometric point is semisimple exactly when the unipotent part of every geometric point is
the identity. -/
theorem geometricallySemisimplePointsCommHopfAlgProperty_iff_forall_unipotentPart_eq_one
    (H : CommHopfAlgCat.{u} k) :
    geometricallySemisimplePointsCommHopfAlgProperty k H ↔
      ∀ g : WithConv (H →ₐ[k] AlgebraicClosure k),
        HopfAlgebra.Point.unipotentPart k H (AlgebraicClosure k) g = 1 := by
  rw [geometricallySemisimplePointsCommHopfAlgProperty_iff]
  apply forall_congr'
  intro g
  exact HopfAlgebra.isSemisimplePoint_iff_unipotentPart_eq_one g

/-- Every geometric point is semisimple exactly when the semisimple part of every geometric point
is the point itself. -/
theorem geometricallySemisimplePointsCommHopfAlgProperty_iff_forall_semisimplePart_eq_self
    (H : CommHopfAlgCat.{u} k) :
    geometricallySemisimplePointsCommHopfAlgProperty k H ↔
      ∀ g : WithConv (H →ₐ[k] AlgebraicClosure k),
        HopfAlgebra.Point.semisimplePart k H (AlgebraicClosure k) g = g := by
  rw [geometricallySemisimplePointsCommHopfAlgProperty_iff]
  apply forall_congr'
  intro g
  constructor
  · intro hg
    exact HopfAlgebra.Point.semisimplePart_eq_self k H (AlgebraicClosure k)
      (fun M ↦ (HopfAlgebra.isSemisimplePoint_def g).mp hg M)
  · intro hs
    rw [HopfAlgebra.isSemisimplePoint_def]
    intro M
    have hdecomp := HopfAlgebra.Point.jordanDecomposition_spec k H (AlgebraicClosure k) g
    have hsem := hdecomp.1 M
    have h1 : (HopfAlgebra.Point.jordanDecomposition k H (AlgebraicClosure k) g).1 = g := by
      rw [HopfAlgebra.Point.jordanDecomposition_fst, hs]
    rw [h1] at hsem
    exact hsem

end ObjectProperty

end TauCeti
