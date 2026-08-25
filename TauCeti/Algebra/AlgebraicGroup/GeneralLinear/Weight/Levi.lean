/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Weight.Parabolic
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Order
import TauCeti.CategoryTheory.Comma.Over

/-!
# Weight-Levi subgroup schemes of the general linear group

An integer weight `w i` on each coordinate of `GL_N` decomposes the standard representation into
its weight spaces. The corresponding Levi subgroup consists of the invertible matrices preserving
every weight space, so its `(i,j)` entry vanishes whenever `w i ≠ w j`.

This file represents that subgroup over an arbitrary commutative base ring. Its defining Hopf
ideal is the join of the weight-parabolic ideals for `w` and `-w`: intersecting the two opposite
block-triangular subgroups leaves precisely the block-diagonal Levi. This construction reuses the
weight-parabolic Hopf-ideal and closed-subgroup API rather than repeating its comultiplication and
antipode calculations.

## Main declarations

* `TauCeti.GeneralLinear.weightLeviDefiningHopfIdeal`: the join of the two opposite
  weight-parabolic ideals.
* `TauCeti.GeneralLinear.weightLeviGroupScheme`: the resulting finite-type closed subgroup
  scheme of `GL_N`.
* `TauCeti.GeneralLinear.mem_weightLeviDefiningPointsSubgroup_iff`: its algebra-valued points are
  exactly the matrices preserving every weight space.

## References

* G. R. Kempf, *Instability in invariant theory*, Annals of Mathematics 108 (1978), §2.
* J. S. Milne, *Algebraic Groups* (2017), Chapter 13.

This advances the dynamic-parabolic route in Layer 7, "Structure theory", of the ReductiveGroups
roadmap by constructing the scheme-level Levi attached to a weight cocharacter.
-/

public section

open AlgebraicGeometry CategoryTheory

namespace TauCeti.GeneralLinear

universe u

variable (R : Type u) [CommRing R] {N : ℕ}

/-- The Hopf ideal cutting out the matrices preserving every weight space. It is the join of the
weight-parabolic ideals for the two opposite filtrations. -/
noncomputable def weightLeviDefiningHopfIdeal (w : Fin N → ℤ) :
    HopfIdeal R (coordinateHopfAlgebra R N) :=
  weightParabolicDefiningHopfIdeal R w ⊔ weightParabolicDefiningHopfIdeal R (-w)

/-- The underlying ideal of the weight Levi is the sum of the two opposite
weight-parabolic ideals. -/
@[simp]
theorem weightLeviDefiningHopfIdeal_toIdeal (w : Fin N → ℤ) :
    (weightLeviDefiningHopfIdeal R w).toIdeal =
      (weightParabolicDefiningHopfIdeal R w).toIdeal ⊔
        (weightParabolicDefiningHopfIdeal R (-w)).toIdeal := by
  rw [weightLeviDefiningHopfIdeal, HopfIdeal.sup_toIdeal]

/-- The coordinate Hopf algebra of the weight Levi attached to `w`. -/
noncomputable abbrev weightLeviCoordinateHopfAlgebra (w : Fin N → ℤ) :
    _root_.CommHopfAlgCat.{u} R :=
  CommHopfAlgCat.quotient (coordinateHopfAlgebra R N)
    (weightLeviDefiningHopfIdeal R w)

/-- The affine group scheme represented by the weight-Levi coordinate Hopf algebra. -/
noncomputable abbrev weightLeviGroupScheme (w : Fin N → ℤ) :=
  CommHopfAlgCat.quotientSpec (coordinateHopfAlgebra R N)
    (weightLeviDefiningHopfIdeal R w)

/-- The closed immersion from the weight Levi into the named general linear group scheme. -/
noncomputable def weightLeviInclusion (w : Fin N → ℤ) :
    weightLeviGroupScheme R w ⟶ groupScheme R N :=
  CommHopfAlgCat.quotientSpecι (coordinateHopfAlgebra R N)
      (weightLeviDefiningHopfIdeal R w) ≫
    (eqToIso (groupScheme_def R N).symm).hom

/-- The weight-Levi inclusion is the quotient-spectrum inclusion followed by the named
identification with `GL_N`. -/
theorem weightLeviInclusion_def (w : Fin N → ℤ) :
    weightLeviInclusion R w =
      CommHopfAlgCat.quotientSpecι (coordinateHopfAlgebra R N)
          (weightLeviDefiningHopfIdeal R w) ≫
        (eqToIso (groupScheme_def R N).symm).hom := by
  rw [weightLeviInclusion]

private theorem weightLeviInclusion_hom_left (w : Fin N → ℤ) :
    (weightLeviInclusion R w).hom.hom.left =
      (CommHopfAlgCat.quotientSpecι (coordinateHopfAlgebra R N)
          (weightLeviDefiningHopfIdeal R w)).hom.hom.left ≫
        ((eqToIso (groupScheme_def R N).symm).hom).hom.hom.left := by
  rw [weightLeviInclusion_def]
  rfl

/-- The weight-Levi inclusion into `GL_N` is a closed immersion. -/
instance isClosedImmersion_weightLeviInclusion (w : Fin N → ℤ) :
    IsClosedImmersion (weightLeviInclusion R w).hom.hom.left := by
  let c := (CommHopfAlgCat.quotientSpecι (coordinateHopfAlgebra R N)
    (weightLeviDefiningHopfIdeal R w)).hom.hom.left
  let e := ((eqToIso (groupScheme_def R N).symm).hom).hom.hom.left
  have hc : IsClosedImmersion c := by infer_instance
  have hce : IsClosedImmersion (c ≫ e) :=
    (MorphismProperty.cancel_right_of_respectsIso _ c e).2 hc
  rw [weightLeviInclusion_hom_left]
  exact hce

/-- The weight-Levi group scheme is locally of finite type over the base. -/
instance locallyOfFiniteType_weightLeviGroupScheme (w : Fin N → ℤ) :
    LocallyOfFiniteType (weightLeviGroupScheme R w).X.hom :=
  FiniteTypeCommHopfAlgCat.locallyOfFiniteType_quotientSpec
    (⟨coordinateHopfAlgebra R N,
      inferInstanceAs (Algebra.FiniteType R (coordinateHopfAlgebra R N))⟩ :
      FiniteTypeCommHopfAlgCat R)
    (weightLeviDefiningHopfIdeal R w)

/-- The subgroup cut out by the weight-Levi ideal consists exactly of matrices preserving every
weight space: entries between distinct weights vanish. -/
@[simp]
theorem mem_weightLeviDefiningPointsSubgroup_iff (w : Fin N → ℤ)
    {A : Type*} [CommRing A] [Algebra R A]
    (g : HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R N)
      (CommAlgCat.of R A)) :
    g ∈ CommHopfAlgCat.quotientPointsSubgroup (coordinateHopfAlgebra R N)
        (weightLeviDefiningHopfIdeal R w) (CommAlgCat.of R A) ↔
      ∀ i j, w i ≠ w j →
        (pointsMulEquiv N g : Matrix (Fin N) (Fin N) A) i j = 0 := by
  rw [weightLeviDefiningHopfIdeal,
    CommHopfAlgCat.quotientPointsSubgroup_sup, Subgroup.mem_inf,
    mem_weightParabolicDefiningPointsSubgroup_iff_blockTriangular,
    mem_weightParabolicDefiningPointsSubgroup_iff_blockTriangular]
  simp only [Matrix.BlockTriangular, Function.comp_apply, OrderDual.toDual_lt_toDual,
    Pi.neg_apply, neg_lt_neg_iff]
  constructor
  · rintro ⟨hupper, hlower⟩ i j hij
    rcases lt_or_gt_of_ne hij with hij | hji
    · exact hupper hij
    · exact hlower hji
  · intro h
    exact ⟨fun i j hij ↦ h i j hij.ne, fun i j hji ↦ h i j hji.ne'⟩

end TauCeti.GeneralLinear
