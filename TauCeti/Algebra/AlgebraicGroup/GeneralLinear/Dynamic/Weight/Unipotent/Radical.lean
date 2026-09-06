/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Dynamic.Weight.Levi.DiagonalTorus
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Dynamic.Weight.Levi.Kernel
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Weight.Unipotent.Geometry
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Dynamic.Weight.Unipotent.Pointwise
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.DiagonalizableQuotient
import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.Isomorphism

/-!
# Unipotent radicals of injective-weight parabolics

For an injective weight `w : Fin N → ℤ`, the dynamic parabolic `P(w)` has diagonal-torus
Levi quotient and weight-unipotent kernel `U(w)`. This file identifies that kernel with the
unipotent radical of `P(w)`.

The normality and kernel calculation come from the represented dynamic Levi decomposition.
The weight-unipotent coordinate algebra is polynomial, hence smooth and geometrically connected,
and its points are unipotent. The general diagonalizable-quotient criterion then gives the
claimed equality of Hopf ideals.

## Main declaration

* `TauCeti.GeneralLinear.
    unipotentRadicalDefiningIdeal_weightParabolicFiniteTypeCoordinateHopfAlgebra`:
  after identifying the finite-type package's object with the weight-parabolic coordinate
  algebra, the unipotent radical is its weight-unipotent kernel.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapters 13 and 17.
* T. A. Springer, *Linear Algebraic Groups*, Sections 6.2--6.3.
-/

public section

open CategoryTheory TauCeti.GeneralLinear.Dynamic TauCeti.FiniteTypeCommHopfAlgCat

namespace TauCeti.GeneralLinear

universe u

noncomputable section

variable {N : ℕ}

/-- **The unipotent radical of an injective-weight parabolic is its weight-unipotent subgroup.**
The pullback along the displayed object equality presents the result in the coordinate algebra
where the canonical weight-unipotent ideal is defined. -/
@[simp] theorem unipotentRadicalDefiningIdeal_weightParabolicFiniteTypeCoordinateHopfAlgebra
    (k : Type u) [Field k] (w : Fin N → ℤ) (hw : Function.Injective w) :
    (FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal
        (weightParabolicFiniteTypeCoordinateHopfAlgebra k w)).comapOfSurjective
      (eqToHom (weightParabolicFiniteTypeCoordinateHopfAlgebra_obj k w).symm).hom
      (ConcreteCategory.bijective_of_isIso
        (eqToHom (weightParabolicFiniteTypeCoordinateHopfAlgebra_obj k w).symm)).2 =
      weightUnipotentInParabolicHopfIdeal k w := by
  let H : FiniteTypeCommHopfAlgCat.{u, u} k :=
    ⟨weightParabolicCoordinateHopfAlgebra k w,
      weightParabolicFiniteTypeCoordinateHopfAlgebra_obj k w ▸
        (weightParabolicFiniteTypeCoordinateHopfAlgebra k w).property⟩
  let I := weightUnipotentInParabolicHopfIdeal k w
  let hUfinite : Algebra.FiniteType k (weightUnipotentCoordinateHopfAlgebra k w) := by
    let _ : Algebra.Smooth k (weightUnipotentCoordinateHopfAlgebra k w) := inferInstance
    infer_instance
  let U : FiniteTypeCommHopfAlgCat.{u, u} k :=
    ⟨weightUnipotentCoordinateHopfAlgebra k w, hUfinite⟩
  let eU : U ≅ FiniteTypeCommHopfAlgCat.quotient H I :=
    ObjectProperty.isoMk _ (weightUnipotentInParabolicCoordinateIso k w)
  have hUconnected : geometricallyConnectedCommHopfAlgProperty k U.obj :=
    geometricallyConnectedCommHopfAlgProperty_weightUnipotentCoordinateHopfAlgebra k w
  have hUsmoothUnipotent : smoothUnipotentCommHopfAlgProperty k U := by
    rw [smoothUnipotentCommHopfAlgProperty_iff]
    refine ⟨inferInstance, ?_⟩
    exact (geometricallyUnipotentPointsCommHopfAlgProperty_iff k U.obj).mp
      (geometricallyUnipotentPointsCommHopfAlgProperty_weightUnipotentCoordinateHopfAlgebra w)
  have hI : HopfIdeal.IsUnipotentRadicalCandidate H I :=
    HopfIdeal.IsUnipotentRadicalCandidate.mk
      (isNormal_weightUnipotentInParabolicHopfIdeal k w)
      ((geometricallyConnectedCommHopfAlgProperty k).prop_of_iso
        ((forget₂ (FiniteTypeCommHopfAlgCat.{u, u} k)
          (_root_.CommHopfAlgCat.{u} k)).mapIso eU) hUconnected)
      ((smoothUnipotentCommHopfAlgProperty k).prop_of_iso eU hUsmoothUnipotent)
  let G := SplitTorus.characterGroup (ULift.{u} (Fin N))
  let eL := weightLeviDiagonalCoordinateIso k w hw
  let fL := weightParabolicLimitCoordinateMap k w
  let f : (DiagonalizableGroup.coordinateRing k G).obj ⟶ H.obj := eL.inv ≫ fL
  have hker : CommHopfAlgCat.kernelHopfIdeal f = I := by
    calc
      CommHopfAlgCat.kernelHopfIdeal f = CommHopfAlgCat.kernelHopfIdeal fL :=
        CommHopfAlgCat.kernelHopfIdeal_comp_of_surjective eL.inv
          (ConcreteCategory.bijective_of_isIso eL.inv).2 fL
      _ = I := kernelHopfIdeal_weightParabolicLimitCoordinateMap k w
  have hRaw : FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal H = I := by
    rw [← hker]
    exact
      unipotentRadicalDefiningIdeal_eq_kernelHopfIdeal_of_geometricallySemisimple
        H (DiagonalizableGroup.coordinateRing k G)
          (DiagonalizableGroup.geometricallySemisimplePointsCommHopfAlgProperty k G)
          f (hker ▸ hI)
  let e : weightParabolicFiniteTypeCoordinateHopfAlgebra k w ≅ H :=
    ObjectProperty.isoMk _
      (eqToIso (weightParabolicFiniteTypeCoordinateHopfAlgebra_obj k w))
  -- The finite-type package is opaque across modules, so align its explicit object isomorphism
  -- with the pullback displayed in the theorem statement.
  change
    (FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal
      (weightParabolicFiniteTypeCoordinateHopfAlgebra k w)).comapOfSurjective
        (FiniteTypeCommHopfAlgCat.toBialgHom e.symm.hom)
        (ConcreteCategory.bijective_of_isIso e.symm.hom).2 = I
  rw [FiniteTypeCommHopfAlgCat.comapOfSurjective_unipotentRadicalDefiningIdeal e.symm]
  exact hRaw

end

end TauCeti.GeneralLinear
