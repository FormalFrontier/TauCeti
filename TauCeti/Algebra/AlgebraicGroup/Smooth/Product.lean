/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.SemidirectProduct
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Normal.Product
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Image.Smooth

/-!
# Smoothness of products of affine groups

The coordinate algebra of a direct or semidirect product of affine groups is the tensor product
of the two coordinate algebras. Smoothness is preserved by base change and composition, so the
product is smooth when both factors are. Smoothness then descends to a scheme-theoretic image in
a finite-type ambient affine group.

## Main declarations

* `TauCeti.smoothCommHopfAlgProperty.semidirectProduct`: a semidirect product of smooth affine
  groups is smooth.
* `TauCeti.smoothCommHopfAlgProperty.productOfNormal`: the multiplication image of a normal
  smooth subgroup and another smooth subgroup is smooth in a finite-type ambient affine group.

This supplies the smoothness part of binary-product closure in Layer 5, "The unipotent radical",
of the ReductiveGroups roadmap.
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti

universe u

noncomputable section

namespace smoothCommHopfAlgProperty

variable {k : Type u} [Field k]

/-- The semidirect product associated to an action of smooth affine groups is smooth. -/
theorem semidirectProduct (H K : CommHopfAlgCat.{u} k)
    (A : GrpObj.Action (CommHopfAlgCat.grpObj K) (CommHopfAlgCat.grpObj H))
    (hH : smoothCommHopfAlgProperty k H)
    (hK : smoothCommHopfAlgProperty k K) :
    smoothCommHopfAlgProperty k A.coordinateHopfAlgebra := by
  rw [smoothCommHopfAlgProperty_iff] at hH hK ⊢
  let _ : Algebra.Smooth k H := hH
  let _ : Algebra.Smooth k K := hK
  let _ : Algebra.Smooth H (H ⊗[k] K) := Algebra.Smooth.baseChange k K H
  let _ : Algebra.Smooth k (H ⊗[k] K) := Algebra.Smooth.comp k H _
  -- Transport the inferred tensor-product smoothness across the coordinate-algebra equivalence.
  exact Algebra.Smooth.of_equiv A.coordinateAlgEquiv.symm

/-- The scheme-theoretic multiplication image of a normal smooth closed affine subgroup and
another smooth closed affine subgroup is smooth when the ambient affine group is finite type. -/
theorem productOfNormal (H : CommHopfAlgCat.{u} k) [Algebra.FiniteType k H]
    (I J : HopfIdeal k H) (hI : I.IsNormal)
    (hIs : smoothCommHopfAlgProperty k (CommHopfAlgCat.quotient H I))
    (hJs : smoothCommHopfAlgProperty k (CommHopfAlgCat.quotient H J)) :
    smoothCommHopfAlgProperty k (CommHopfAlgCat.productOfNormal H I J hI) := by
  let A := CommHopfAlgCat.quotientNormalConjugation H I J hI
  apply image (CommHopfAlgCat.productMapOfNormal H I J hI)
  rw [CommHopfAlgCat.normalSemidirectProduct_eq_coordinateHopfAlgebra]
  exact semidirectProduct (CommHopfAlgCat.quotient H I)
    (CommHopfAlgCat.quotient H J) A hIs hJs

end smoothCommHopfAlgProperty

end

end TauCeti
