/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.SemidirectProduct
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Normal.Product.Basic
public import TauCeti.Algebra.AlgebraicGroup.Smooth.CommHopfAlgCat
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Image.Smooth

/-!
# Smoothness of products of affine groups

The coordinate algebra of a direct or semidirect product of affine groups is the tensor product
of the two coordinate algebras. Smoothness is preserved by base change and composition, so the
product is smooth when both factors are. Smoothness then descends to a scheme-theoretic image in
a finite-type ambient affine group.

## Main declarations

* `TauCeti.smoothCommHopfAlgProperty.semidirectProduct`: a semidirect product of smooth affine
  groups is smooth.
* `TauCeti.smoothCommHopfAlgProperty.normalSemidirectProduct`: the conjugation semidirect-product
  source associated to two smooth closed subgroups is smooth.
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

variable {R : Type u} [CommRing R]

/-- The semidirect product associated to an action of smooth affine groups is smooth. -/
theorem semidirectProduct (H K : CommHopfAlgCat.{u} R)
    (A : GrpObj.Action (CommHopfAlgCat.grpObj K) (CommHopfAlgCat.grpObj H))
    (hH : smoothCommHopfAlgProperty R H)
    (hK : smoothCommHopfAlgProperty R K) :
    smoothCommHopfAlgProperty R A.coordinateHopfAlgebra := by
  rw [smoothCommHopfAlgProperty_iff] at hH hK ⊢
  let _ : Algebra.Smooth R H := hH
  let _ : Algebra.Smooth R K := hK
  let _ : Algebra.Smooth H (H ⊗[R] K) := Algebra.Smooth.baseChange R K H
  let _ : Algebra.Smooth R (H ⊗[R] K) := Algebra.Smooth.comp R H _
  -- Transport the inferred tensor-product smoothness across the coordinate-algebra equivalence.
  exact Algebra.Smooth.of_equiv A.coordinateAlgEquiv.symm

/-- The conjugation semidirect-product source associated to a normal smooth closed subgroup and
another smooth closed subgroup is smooth. -/
theorem normalSemidirectProduct (H : CommHopfAlgCat.{u} R)
    (I J : HopfIdeal R H) (hI : I.IsNormal)
    (hIs : smoothCommHopfAlgProperty R (CommHopfAlgCat.quotient H I))
    (hJs : smoothCommHopfAlgProperty R (CommHopfAlgCat.quotient H J)) :
    smoothCommHopfAlgProperty R
      (CommHopfAlgCat.normalSemidirectProduct H I J hI) := by
  let A := CommHopfAlgCat.quotientNormalConjugation H I J hI
  exact (smoothCommHopfAlgProperty R).prop_of_iso
    (CommHopfAlgCat.normalSemidirectProductIso H I J hI).symm
    (semidirectProduct (CommHopfAlgCat.quotient H I)
      (CommHopfAlgCat.quotient H J) A hIs hJs)

variable {k : Type u} [Field k]

/-- The scheme-theoretic multiplication image of a normal smooth closed affine subgroup and
another smooth closed affine subgroup is smooth when the ambient affine group is finite type. -/
theorem productOfNormal (H : CommHopfAlgCat.{u} k) [Algebra.FiniteType k H]
    (I J : HopfIdeal k H) (hI : I.IsNormal)
    (hIs : smoothCommHopfAlgProperty k (CommHopfAlgCat.quotient H I))
    (hJs : smoothCommHopfAlgProperty k (CommHopfAlgCat.quotient H J)) :
    smoothCommHopfAlgProperty k (CommHopfAlgCat.productOfNormal H I J hI) := by
  apply image (CommHopfAlgCat.productMapOfNormal H I J hI)
  exact normalSemidirectProduct H I J hI hIs hJs

end smoothCommHopfAlgProperty

end

end TauCeti
