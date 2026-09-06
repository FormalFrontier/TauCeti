/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Center.Basic
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Reduction
public import TauCeti.Algebra.AlgebraicGroup.Smooth.AlgebraicallyClosed
import Mathlib.RingTheory.Noetherian.Nilpotent

/-!
# The reduced center of an affine group

The center of an affine group can be nonreduced, even when the ambient group is smooth. This file
constructs its reduction in Hopf coordinates. First quotient by the center ideal, then quotient
that coordinate algebra by its nilradical. Equivalently, the reduced center is cut out in the
ambient coordinate algebra by the radical of the center ideal.

The only additional input is reducedness of the tensor square of the reduced center coordinate
algebra. This is the exact commutative-algebra condition needed to make the nilradical a Hopf
ideal; it is kept explicit by `TauCeti.HopfIdeal.reduction`. The construction records both the
nested quotient and the single ambient defining ideal, together with their canonical
identification.

This is the reduced-center input for proving that the center of a semisimple affine group is
finite. Semisimplicity trivializes the smooth connected identity component of this reduction;
the finite component-group theorem then makes the reduction finite, after which nilpotence of the
thickening controls the original center.

## Main declarations

* `TauCeti.CommHopfAlgCat.reducedCenterDefiningIdeal`: the ambient ideal cutting out the reduced
  center.
* `TauCeti.CommHopfAlgCat.reducedCenterCoordinateRing`: its coordinate Hopf algebra.
* `TauCeti.CommHopfAlgCat.reducedCenterDefiningIdeal_toIdeal`: the ambient defining ideal is the
  radical of the center ideal.
* `TauCeti.CommHopfAlgCat.quotientReducedCenterIso`: the ambient and iterated quotient models
  agree.
* `TauCeti.CommHopfAlgCat.smooth_reducedCenterCoordinateRing`: over an algebraically closed
  field, a finite-type reduced center is smooth.
* `TauCeti.CommHopfAlgCat.isNilpotent_reducedCenterKernel`: over a Noetherian center coordinate
  ring, the thickening from the reduced center to the full center is nilpotent.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§1.f and 21.10.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §11.4.
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti.CommHopfAlgCat

universe u v

variable {k : Type u} [Field k]

variable (H : _root_.CommHopfAlgCat.{v} k)

variable [IsReduced
  ((((centerCoordinateRing H : _root_.CommHopfAlgCat.{v} k) : Type v) ⧸
      nilradical ((centerCoordinateRing H : _root_.CommHopfAlgCat.{v} k) : Type v)) ⊗[k]
    (((centerCoordinateRing H : _root_.CommHopfAlgCat.{v} k) : Type v) ⧸
      nilradical ((centerCoordinateRing H : _root_.CommHopfAlgCat.{v} k) : Type v)))]

/-- The Hopf ideal in the ambient coordinate algebra cutting out the reduced center.

It is the inverse image of the nilradical Hopf ideal of the center coordinate algebra. -/
noncomputable def reducedCenterDefiningIdeal : HopfIdeal k H :=
  (HopfIdeal.reduction k (centerCoordinateRing H)).comapOfSurjective
    (mkQuotient H (centerDefiningIdeal H)).hom
    (mkQuotient_surjective H (centerDefiningIdeal H))

/-- The center ideal is contained in the reduced-center ideal. Contravariantly, the reduced
center is a closed subgroup of the center. -/
theorem centerDefiningIdeal_le_reducedCenterDefiningIdeal :
    centerDefiningIdeal H ≤ reducedCenterDefiningIdeal H := by
  intro x hx
  rw [reducedCenterDefiningIdeal, HopfIdeal.mem_comapOfSurjective]
  have hzero : (mkQuotient H (centerDefiningIdeal H)).hom x = 0 :=
    (mkQuotient_eq_zero_iff H (centerDefiningIdeal H) x).mpr hx
  rw [hzero]
  exact HopfIdeal.mem_toIdeal.mp
    (HopfIdeal.reduction k (centerCoordinateRing H)).toIdeal.zero_mem

/-- The ideal defining the reduced center is central. -/
theorem isCentral_reducedCenterDefiningIdeal :
    (reducedCenterDefiningIdeal H).IsCentral :=
  (centerDefiningIdeal_le_iff H (reducedCenterDefiningIdeal H)).mp
    (centerDefiningIdeal_le_reducedCenterDefiningIdeal H)

/-- The coordinate Hopf algebra of the reduced center, formed by quotienting the center by its
nilradical. -/
noncomputable abbrev reducedCenterCoordinateRing : _root_.CommHopfAlgCat.{v} k :=
  quotient (centerCoordinateRing H) (HopfIdeal.reduction k (centerCoordinateRing H))

/-- The reduced-center coordinate algebra is reduced. -/
theorem isReduced_reducedCenterCoordinateRing :
    IsReduced (reducedCenterCoordinateRing H) :=
  HopfIdeal.isReduced_quotient_reduction k (centerCoordinateRing H)

/-- The ambient ideal defining the reduced center is the radical of the center ideal. -/
@[simp]
theorem reducedCenterDefiningIdeal_toIdeal :
    (reducedCenterDefiningIdeal H).toIdeal = (centerDefiningIdeal H).toIdeal.radical := by
  rw [reducedCenterDefiningIdeal, HopfIdeal.comapOfSurjective_toIdeal,
    HopfIdeal.reduction_toIdeal, nilradical, Ideal.comap_radical]
  congr 1
  rw [Ideal.zero_eq_bot, ← RingHom.ker_eq_comap_bot]
  exact mkQuotient_ker H (centerDefiningIdeal H)

/-- An element belongs to the reduced-center ideal exactly when it belongs to the radical of the
center ideal. -/
@[simp]
theorem mem_reducedCenterDefiningIdeal {x : H} :
    x ∈ reducedCenterDefiningIdeal H ↔ x ∈ (centerDefiningIdeal H).toIdeal.radical := by
  rw [← HopfIdeal.mem_toIdeal, reducedCenterDefiningIdeal_toIdeal]

/-- The quotient by the ambient reduced-center ideal is canonically the iterated quotient formed
by taking the center and then killing its nilradical. -/
noncomputable def quotientReducedCenterIso :
    quotient H (reducedCenterDefiningIdeal H) ≅ reducedCenterCoordinateRing H :=
  quotientIsoOfSurjective (mkQuotient H (centerDefiningIdeal H))
    (mkQuotient_surjective H (centerDefiningIdeal H))
      (HopfIdeal.reduction k (centerCoordinateRing H))

/-- The canonical reduced-center isomorphism commutes with the ambient and iterated quotient
morphisms. -/
@[simp]
theorem mkQuotient_comp_quotientReducedCenterIso_hom :
    mkQuotient H (reducedCenterDefiningIdeal H) ≫ (quotientReducedCenterIso H).hom =
      mkQuotient H (centerDefiningIdeal H) ≫
        mkQuotient (centerCoordinateRing H) (HopfIdeal.reduction k (centerCoordinateRing H)) := by
  exact mkQuotient_comp_quotientIsoOfSurjective_hom
    (mkQuotient H (centerDefiningIdeal H))
      (mkQuotient_surjective H (centerDefiningIdeal H))
        (HopfIdeal.reduction k (centerCoordinateRing H))

/-- The ambient quotient model of the reduced center has reduced coordinate ring. -/
theorem isReduced_quotient_reducedCenterDefiningIdeal :
    IsReduced (quotient H (reducedCenterDefiningIdeal H)) := by
  let _ : IsReduced (reducedCenterCoordinateRing H) :=
    isReduced_reducedCenterCoordinateRing H
  exact isReduced_of_injective (quotientReducedCenterIso H).hom.hom.toAlgHom.toRingHom
    (ConcreteCategory.bijective_of_isIso (quotientReducedCenterIso H).hom).1

/-- If the center coordinate ring is Noetherian, the ideal removed from the center to form its
reduction is nilpotent. This records that the reduced center and the full center differ by a
nilpotent thickening. -/
theorem isNilpotent_reducedCenterKernel [IsNoetherianRing (centerCoordinateRing H)] :
    IsNilpotent (HopfIdeal.reduction k (centerCoordinateRing H)).toIdeal := by
  rw [HopfIdeal.reduction_toIdeal]
  exact IsNoetherianRing.isNilpotent_nilradical (centerCoordinateRing H)

section Smooth

variable (G : _root_.CommHopfAlgCat.{u} k)
variable [IsReduced
  ((((centerCoordinateRing G : _root_.CommHopfAlgCat.{u} k) : Type u) ⧸
      nilradical ((centerCoordinateRing G : _root_.CommHopfAlgCat.{u} k) : Type u)) ⊗[k]
    (((centerCoordinateRing G : _root_.CommHopfAlgCat.{u} k) : Type u) ⧸
      nilradical ((centerCoordinateRing G : _root_.CommHopfAlgCat.{u} k) : Type u)))]

/-- Over an algebraically closed field, a finite-type reduced center is smooth. -/
theorem smooth_reducedCenterCoordinateRing [IsAlgClosed k]
    [Algebra.FiniteType k (reducedCenterCoordinateRing G)] :
    Algebra.Smooth k (reducedCenterCoordinateRing G) := by
  let _ : IsReduced (reducedCenterCoordinateRing G) :=
    isReduced_reducedCenterCoordinateRing G
  exact (smoothCommHopfAlgProperty_iff (reducedCenterCoordinateRing G)).mp
    (smoothCommHopfAlgProperty_of_isAlgClosed_of_isReduced k (reducedCenterCoordinateRing G))

end Smooth

end TauCeti.CommHopfAlgCat
