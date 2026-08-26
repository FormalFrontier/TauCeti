/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.SemidirectProduct
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Normal.Product.Basic
public import TauCeti.Algebra.AlgebraicGroup.Solvable.Basic

/-!
# Solvability of semidirect products of affine groups

An internal action of affine groups equips the product of their underlying affine schemes with a
semidirect-product group law. This file proves that the resulting affine group has solvable
geometric points when both factors do.

On points over an algebraic closure, the internal semidirect product is the ordinary semidirect
product of the two point groups. Its normal-factor inclusion and projection onto the acting factor
form an extension, so Mathlib's extension closure for solvable groups applies. The result is also
stated for the named conjugation semidirect product used to form the scheme-theoretic product of a
normal closed subgroup with another closed subgroup.

## Main declarations

* `TauCeti.geometricallySolvablePointsCommHopfAlgProperty.semidirectProduct`: internal
  semidirect products preserve solvability of geometric points.
* `TauCeti.geometricallySolvablePointsCommHopfAlgProperty.normalSemidirectProduct`: the
  conjugation semidirect-product source attached to two closed subgroups has solvable geometric
  points when both subgroups do.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, I.2.
* T. A. Springer, *Linear Algebraic Groups*, Section 2.4.

This supplies the source-side extension step for the solvable radical in Layer 6 of the
ReductiveGroups roadmap. To prove that the scheme-theoretic multiplication image is again
solvable, it remains to descend solvability from this source to its image.
-/

public section

open CategoryTheory Opposite WithConv
open scoped CategoryTheory.MonObj

namespace TauCeti

universe u

noncomputable section

namespace geometricallySolvablePointsCommHopfAlgProperty

variable (k : Type u) [Field k]

/-- An internal semidirect product of affine groups with solvable geometric point groups again
has a solvable geometric point group. -/
theorem semidirectProduct (H K : _root_.CommHopfAlgCat.{u} k)
    (A : GrpObj.Action (CommHopfAlgCat.grpObj K) (CommHopfAlgCat.grpObj H))
    (hH : geometricallySolvablePointsCommHopfAlgProperty k H)
    (hK : geometricallySolvablePointsCommHopfAlgProperty k K) :
    geometricallySolvablePointsCommHopfAlgProperty k A.coordinateHopfAlgebra := by
  rw [geometricallySolvablePointsCommHopfAlgProperty_iff] at hH hK ⊢
  let L := CommAlgCat.of k (AlgebraicClosure k)
  let X := op L
  let _ := A.semidirectProductGrpObj
  let eH := CommHopfAlgCat.grpObjPointsMulEquiv H X
  let eK := CommHopfAlgCat.grpObjPointsMulEquiv K X
  have hHX : Group.IsSolvable (X ⟶ CommHopfAlgCat.grpObj H) := by
    let _ : Group.IsSolvable (WithConv (H →ₐ[k] AlgebraicClosure k)) := hH
    exact Group.isSolvable_of_isSolvable_injective (f := eH.toMonoidHom) eH.injective
  have hKX : Group.IsSolvable (X ⟶ CommHopfAlgCat.grpObj K) := by
    let _ : Group.IsSolvable (WithConv (K →ₐ[k] AlgebraicClosure k)) := hK
    exact Group.isSolvable_of_isSolvable_injective (f := eK.toMonoidHom) eK.injective
  have hsemi : Group.IsSolvable
      ((X ⟶ CommHopfAlgCat.grpObj H) ⋊[A.toMulAutHom X]
        (X ⟶ CommHopfAlgCat.grpObj K)) := by
    let _ : Group.IsSolvable (X ⟶ CommHopfAlgCat.grpObj H) := hHX
    let _ : Group.IsSolvable (X ⟶ CommHopfAlgCat.grpObj K) := hKX
    exact Group.isSolvable_of_ker_le_range
      (SemidirectProduct.inl :
        (X ⟶ CommHopfAlgCat.grpObj H) →*
          ((X ⟶ CommHopfAlgCat.grpObj H) ⋊[A.toMulAutHom X]
            (X ⟶ CommHopfAlgCat.grpObj K)))
      (SemidirectProduct.rightHom :
        ((X ⟶ CommHopfAlgCat.grpObj H) ⋊[A.toMulAutHom X]
          (X ⟶ CommHopfAlgCat.grpObj K)) →*
            (X ⟶ CommHopfAlgCat.grpObj K))
      SemidirectProduct.range_inl_eq_ker_rightHom.ge
  let e : WithConv (A.coordinateHopfAlgebra →ₐ[k] AlgebraicClosure k) ≃*
      ((X ⟶ CommHopfAlgCat.grpObj H) ⋊[A.toMulAutHom X]
        (X ⟶ CommHopfAlgCat.grpObj K)) :=
    (CommHopfAlgCat.grpObjPointsMulEquiv A.coordinateHopfAlgebra X).symm.trans
      (A.pointMulEquiv X)
  let _ : Group.IsSolvable
      ((X ⟶ CommHopfAlgCat.grpObj H) ⋊[A.toMulAutHom X]
        (X ⟶ CommHopfAlgCat.grpObj K)) := hsemi
  exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective

/-- The conjugation semidirect-product source associated to a normal closed subgroup and another
closed subgroup has solvable geometric points when the two subgroup point groups are solvable. -/
theorem normalSemidirectProduct (H : _root_.CommHopfAlgCat.{u} k)
    (I J : HopfIdeal k H) (hI : I.IsNormal)
    (hIs : geometricallySolvablePointsCommHopfAlgProperty k (CommHopfAlgCat.quotient H I))
    (hJs : geometricallySolvablePointsCommHopfAlgProperty k (CommHopfAlgCat.quotient H J)) :
    geometricallySolvablePointsCommHopfAlgProperty k
      (CommHopfAlgCat.normalSemidirectProduct H I J hI) := by
  let A := CommHopfAlgCat.quotientNormalConjugation H I J hI
  exact (geometricallySolvablePointsCommHopfAlgProperty k).prop_of_iso
    (CommHopfAlgCat.normalSemidirectProductIso H I J hI).symm
    (semidirectProduct k (CommHopfAlgCat.quotient H I)
      (CommHopfAlgCat.quotient H J) A hIs hJs)

end geometricallySolvablePointsCommHopfAlgProperty

end

end TauCeti
