/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.Yoneda
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Basic
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Categorical

/-!
# Generalized points of Hopf-ideal quotient inclusions

This file identifies composition with the categorical closed-subgroup inclusion represented by a
Hopf-ideal quotient with the usual precomposition map on algebra-valued points.

## Main declarations

* `TauCeti.CommHopfAlgCat.grpObjPointsMulEquiv_comp_quotientGrpObjInclusion`: the represented
  quotient inclusion acts on generalized points by the quotient-points homomorphism.

## References

This is the generalized-point form of the Layer 3 Hopf-ideal/closed-subgroup dictionary in the
ReductiveGroups roadmap. It combines the represented group-object Yoneda equivalence with the
point-level quotient API.
-/

public section

open CategoryTheory Opposite

namespace TauCeti.CommHopfAlgCat

universe u

variable {R : Type u} [CommRing R]

/-- Under the group-object point equivalences, composition with the categorical quotient
inclusion is the usual quotient-points homomorphism. -/
@[simp]
theorem grpObjPointsMulEquiv_comp_quotientGrpObjInclusion
    (H : _root_.CommHopfAlgCat.{u} R) (I : HopfIdeal R H)
    (X : (CommAlgCat.{u} R)ᵒᵖ) (q : X ⟶ grpObj (quotient H I)) :
    grpObjPointsMulEquiv H X (q ≫ quotientGrpObjInclusion H I) =
      quotientPointsHom H I X.unop (grpObjPointsMulEquiv (quotient H I) X q) := by
  rw [quotientGrpObjInclusion_def]
  exact grpObjPointsMulEquiv_comp_grpObjMap (mkQuotient H I) X q

end TauCeti.CommHopfAlgCat
