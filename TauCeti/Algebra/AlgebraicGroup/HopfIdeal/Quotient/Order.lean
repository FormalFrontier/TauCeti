/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Order

/-!
# Point compatibility for order maps between Hopf-ideal quotients

If `I ≤ J` are Hopf ideals in a commutative Hopf algebra `H`, then the quotient map
`H ⟶ H ⧸ J` kills `I`, so it factors through a coordinate morphism
`H ⧸ I ⟶ H ⧸ J`. Contravariantly, this is the map on closed-subgroup functors induced by
the inclusion of the subgroup cut out by `J` into the subgroup cut out by `I`.

This file records the compatibility of that quotient-to-quotient morphism with the
already-defined point subgroup inclusions. The coordinate-level morphism itself is defined in
`TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Basic`.

## Main declarations

* `CommHopfAlgCat.quotientPointsHom_mapPointsFunctor_quotientMapOfLe_app`: on points,
  precomposition with `quotientMapOfLe` is compatible with the ambient quotient-points
  inclusions.

## References

This is point-level bookkeeping for the ReductiveGroups roadmap, Layer 3,
"Hopf ideals ↔ closed subgroup schemes". It uses the quotient universal property from
`TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Basic` and the cut-out subgroup order API from
`TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Order`.
-/

public section

open CategoryTheory WithConv

namespace TauCeti

universe u v w

namespace CommHopfAlgCat

variable {R : Type u} [CommRing R]

/-- On points, precomposition with `quotientMapOfLe` is compatible with the ambient
quotient-points inclusions.

Starting with a point of `H ⧸ J`, mapping it to a point of `H ⧸ I` and then including into
ambient `H`-points gives the same ambient point as the direct inclusion from `H ⧸ J`. -/
@[simp]
lemma quotientPointsHom_mapPointsFunctor_quotientMapOfLe_app
    (H : _root_.CommHopfAlgCat.{v} R) {I J : HopfIdeal R H} (hIJ : I ≤ J)
    (A : CommAlgCat.{w} R)
    (f : HopfAlgebra.points (R := R) (H := quotient H J) A) :
    quotientPointsHom H I A ((mapPointsFunctor (quotientMapOfLe H hIJ)).app A f) =
      quotientPointsHom H J A f := by
  apply WithConv.ofConv_injective
  ext h
  erw [quotientPointsHom_apply_apply, mapPointsFunctor_app_apply_apply,
    quotientMapOfLe_mk, quotientPointsHom_apply_apply]

/-- The pointwise form of
`CommHopfAlgCat.quotientPointsHom_mapPointsFunctor_quotientMapOfLe_app`. -/
@[simp]
lemma quotientPointsHom_mapPointsFunctor_quotientMapOfLe_app_apply
    (H : _root_.CommHopfAlgCat.{v} R) {I J : HopfIdeal R H} (hIJ : I ≤ J)
    (A : CommAlgCat.{w} R)
    (f : HopfAlgebra.points (R := R) (H := quotient H J) A) (h : H) :
    (quotientPointsHom H I A ((mapPointsFunctor (quotientMapOfLe H hIJ)).app A f)).ofConv h =
      f.ofConv (Ideal.Quotient.mkₐ R J.toIdeal h) := by
  rw [quotientPointsHom_mapPointsFunctor_quotientMapOfLe_app, quotientPointsHom_apply_apply]

/-- Under the quotient-point subgroup isomorphisms, the points map induced by
`quotientMapOfLe` is exactly the subgroup inclusion attached to `I ≤ J`. -/
@[simp]
lemma quotientPointsSubgroupIso_hom_mapPointsFunctor_quotientMapOfLe_app
    (H : _root_.CommHopfAlgCat.{v} R) {I J : HopfIdeal R H} (hIJ : I ≤ J)
    (A : CommAlgCat.{w} R)
    (f : HopfAlgebra.points (R := R) (H := quotient H J) A) :
    (quotientPointsSubgroupIso H I A).hom
        ((mapPointsFunctor (quotientMapOfLe H hIJ)).app A f) =
      Subgroup.inclusion (quotientPointsSubgroup_le_of_le H hIJ A)
        ((quotientPointsSubgroupIso H J A).hom f) := by
  apply Subtype.ext
  exact quotientPointsHom_mapPointsFunctor_quotientMapOfLe_app H hIJ A f

end CommHopfAlgCat

end TauCeti
