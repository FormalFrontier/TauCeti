/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Basic

/-!
# Points of Hopf-ideal quotients

For a Hopf ideal `I` in a commutative Hopf algebra `H`, the quotient coordinate Hopf algebra
`H ⧸ I` represents a closed subgroup of the affine group represented by `H`. On functors of
points this is the injective group homomorphism
`(H ⧸ I →ₐ[R] A) → (H →ₐ[R] A)` obtained by pre-composing with the quotient map
`H → H ⧸ I`.

This file records the point-level part of that dictionary. The image is characterized by the
ordinary algebraic condition that an `A`-point of `H` vanish on the ideal `I`; equivalently,
the point factors uniquely through the quotient algebra.

## Main declarations

* `CommHopfAlgCat.quotientPointsHom`: the group homomorphism from quotient points to
  ambient points.
* `CommHopfAlgCat.liftQuotientPoint`: factor an ambient point through `H ⧸ I` when it
  kills `I`.
* `CommHopfAlgCat.mem_range_quotientPointsHom_iff`: quotient points are exactly ambient
  points killing `I`.
* `CommHopfAlgCat.quotientPointsSubgroup`: the subgroup of ambient points cut out by `I`.

## References

This is a Layer 3 prerequisite for `TauCetiRoadmap/ReductiveGroups/README.md`, "Hopf ideals ↔
closed subgroup schemes". It builds on the quotient Hopf algebra API in
`TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Basic` and Mathlib's algebra quotient universal
property `Ideal.Quotient.liftₐ`.
-/

public section

open CategoryTheory WithConv

namespace TauCeti

universe u v w

namespace CommHopfAlgCat

variable {R : Type u} [CommRing R]

/-- The map on `A`-points induced by the quotient coordinate morphism `H ⟶ H ⧸ I`.

Contravariantly, this is the closed-subgroup inclusion on points: it sends a point of the
quotient Hopf algebra to its composite with the quotient map from `H`. -/
@[expose] noncomputable def quotientPointsHom (H : _root_.CommHopfAlgCat.{v} R)
    (I : HopfIdeal R H) (A : CommAlgCat.{w} R) :
    HopfAlgebra.points (R := R) (H := quotient H I) A ⟶
      HopfAlgebra.points (R := R) (H := H) A :=
  (mapPointsFunctor (mkQuotient H I)).app A

/-- The quotient-points map acts by pre-composition with the quotient morphism. -/
@[simp]
lemma quotientPointsHom_apply (H : _root_.CommHopfAlgCat.{v} R) (I : HopfIdeal R H)
    (A : CommAlgCat.{w} R) (f : HopfAlgebra.points (R := R) (H := quotient H I) A) :
    quotientPointsHom H I A f =
      toConv (f.ofConv.comp ((mkQuotient H I).hom : H →ₐ[R] quotient H I)) :=
  mapPointsFunctor_app_apply (mkQuotient H I) A f

/-- Pointwise form of `CommHopfAlgCat.quotientPointsHom_apply`. -/
@[simp]
lemma quotientPointsHom_apply_apply (H : _root_.CommHopfAlgCat.{v} R)
    (I : HopfIdeal R H) (A : CommAlgCat.{w} R)
    (f : HopfAlgebra.points (R := R) (H := quotient H I) A) (h : H) :
    ((quotientPointsHom H I A f).ofConv) h =
      f.ofConv (Ideal.Quotient.mkₐ R I.toIdeal h) := by
  rw [quotientPointsHom_apply, ofConv_toConv, AlgHom.comp_apply]
  exact congrArg f.ofConv (mkQuotient_apply H I h)

/-- The map from quotient points to ambient points is injective. -/
lemma quotientPointsHom_injective (H : _root_.CommHopfAlgCat.{v} R)
    (I : HopfIdeal R H) (A : CommAlgCat.{w} R) :
    Function.Injective (quotientPointsHom H I A) :=
  mapPointsFunctor_app_injective_of_surjective (mkQuotient H I)
    (Ideal.Quotient.mkₐ_surjective R I.toIdeal) A

/-- An ambient `A`-point factors through `H ⧸ I` when it kills the Hopf ideal `I`. -/
noncomputable def liftQuotientPoint (H : _root_.CommHopfAlgCat.{v} R)
    (I : HopfIdeal R H) (A : CommAlgCat.{w} R)
    (g : HopfAlgebra.points (R := R) (H := H) A)
    (hg : ∀ h : H, h ∈ I → g.ofConv h = 0) :
    HopfAlgebra.points (R := R) (H := quotient H I) A :=
  toConv (Ideal.Quotient.liftₐ I.toIdeal g.ofConv (by
    intro h hh
    exact hg h ((HopfIdeal.mem_toIdeal (I := I)).mp hh)))

/-- The quotient point built from a point killing `I` evaluates on a quotient class by
choosing any representative. -/
@[simp]
lemma liftQuotientPoint_mk (H : _root_.CommHopfAlgCat.{v} R)
    (I : HopfIdeal R H) (A : CommAlgCat.{w} R)
    (g : HopfAlgebra.points (R := R) (H := H) A)
    (hg : ∀ h : H, h ∈ I → g.ofConv h = 0) (h : H) :
    ((liftQuotientPoint H I A g hg).ofConv) (Ideal.Quotient.mkₐ R I.toIdeal h) =
      g.ofConv h := by
  exact AlgHom.congr_fun (Ideal.Quotient.liftₐ_comp I.toIdeal g.ofConv (by
    intro h hh
    exact hg h ((HopfIdeal.mem_toIdeal (I := I)).mp hh))) h

/-- Factoring a point that kills `I` through the quotient and then including it back in the
ambient point group recovers the original point. -/
@[simp]
lemma quotientPointsHom_liftQuotientPoint (H : _root_.CommHopfAlgCat.{v} R)
    (I : HopfIdeal R H) (A : CommAlgCat.{w} R)
    (g : HopfAlgebra.points (R := R) (H := H) A)
    (hg : ∀ h : H, h ∈ I → g.ofConv h = 0) :
    quotientPointsHom H I A (liftQuotientPoint H I A g hg) = g := by
  apply WithConv.ofConv_injective
  apply AlgHom.ext
  intro h
  rw [quotientPointsHom_apply_apply, liftQuotientPoint_mk]

/-- A point of the ambient Hopf algebra lies in the image of quotient points if and only if it
kills the Hopf ideal. -/
lemma mem_range_quotientPointsHom_iff (H : _root_.CommHopfAlgCat.{v} R)
    (I : HopfIdeal R H) (A : CommAlgCat.{w} R)
    (g : HopfAlgebra.points (R := R) (H := H) A) :
    g ∈ Set.range (quotientPointsHom H I A) ↔ ∀ h : H, h ∈ I → g.ofConv h = 0 := by
  constructor
  · rintro ⟨f, rfl⟩ h hh
    rw [quotientPointsHom_apply_apply]
    exact map_zero f.ofConv ▸ congrArg f.ofConv
      (Ideal.Quotient.eq_zero_iff_mem.mpr ((HopfIdeal.mem_toIdeal (I := I)).mpr hh))
  · intro hg
    exact ⟨liftQuotientPoint H I A g hg, quotientPointsHom_liftQuotientPoint H I A g hg⟩

/-- The subgroup of ambient `A`-points cut out by a Hopf ideal `I`.

Its elements are exactly those algebra maps `H →ₐ[R] A` that vanish on `I`; this is the
point-level closed subgroup represented by the quotient coordinate Hopf algebra `H ⧸ I`. -/
@[expose] noncomputable def quotientPointsSubgroup (H : _root_.CommHopfAlgCat.{v} R)
    (I : HopfIdeal R H) (A : CommAlgCat.{w} R) :
    Subgroup (HopfAlgebra.points (R := R) (H := H) A) :=
  (quotientPointsHom H I A).hom.range

/-- Membership in the subgroup of points cut out by a Hopf ideal is vanishing on that ideal. -/
@[simp]
lemma mem_quotientPointsSubgroup_iff (H : _root_.CommHopfAlgCat.{v} R)
    (I : HopfIdeal R H) (A : CommAlgCat.{w} R)
    (g : HopfAlgebra.points (R := R) (H := H) A) :
    g ∈ quotientPointsSubgroup H I A ↔ ∀ h : H, h ∈ I → g.ofConv h = 0 :=
  mem_range_quotientPointsHom_iff H I A g

/-- The included quotient point belongs to the subgroup cut out by the Hopf ideal. -/
lemma quotientPointsHom_mem_quotientPointsSubgroup (H : _root_.CommHopfAlgCat.{v} R)
    (I : HopfIdeal R H) (A : CommAlgCat.{w} R)
    (f : HopfAlgebra.points (R := R) (H := quotient H I) A) :
    quotientPointsHom H I A f ∈ quotientPointsSubgroup H I A :=
  ⟨f, rfl⟩

end CommHopfAlgCat

end TauCeti
