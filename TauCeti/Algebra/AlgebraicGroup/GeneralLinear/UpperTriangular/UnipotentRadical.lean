/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Dynamic.Weight.Unipotent.Radical
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.UpperTriangular.Basic
import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.Isomorphism

/-!
# The unipotent radical of the upper-triangular group

The standard upper-triangular group is the dynamic parabolic for the injective weights
`i ↦ n - 1 - i`. Its weight-unipotent subgroup consists exactly of upper-unitriangular
matrices. Specializing the injective-weight calculation therefore identifies this subgroup with
the unipotent radical of the upper-triangular affine group.

## Main declaration

* `TauCeti.GeneralLinear.UpperTriangular.mem_upperUnitriangularPointsSubgroup_iff`:
  the relative weight-unipotent ideal cuts out exactly the existing upper-unitriangular matrix
  group over every commutative value algebra.
* `TauCeti.GeneralLinear.UpperTriangular.
    unipotentRadicalDefiningIdeal_finiteTypeCoordinateHopfAlgebra`:
  after identifying the finite-type package's object with the upper-triangular coordinate
  algebra, the relative upper-unitriangular Hopf ideal is the unipotent-radical defining ideal.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapters 13 and 17.
* T. A. Springer, *Linear Algebraic Groups*, Sections 6.2--6.3.
-/

public section

open CategoryTheory

namespace TauCeti.GeneralLinear.UpperTriangular

universe u v

noncomputable section

/-- The relative weight-unipotent ideal cuts out exactly the existing upper-unitriangular
matrix group, compatibly with the upper-triangular inclusion into `GL_n`. -/
@[simp]
theorem mem_upperUnitriangularPointsSubgroup_iff
    (R : Type u) [CommRing R] (n : ℕ) {A : Type v} [CommRing A] [Algebra R A]
    (f : HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R n)
      (CommAlgCat.of R A)) :
    f ∈ CommHopfAlgCat.quotientPointsSubgroup (coordinateHopfAlgebra R n)
        (GeneralLinear.Dynamic.weightUnipotentInParabolicHopfIdeal R (weights n))
        (CommAlgCat.of R A) ↔
      (pointsMulEquiv (R := R) (n := n) (A := A) f : GL (Fin n) A) ∈
        upperUnitriangularGroup (Fin n) A := by
  rw [GeneralLinear.Dynamic.mem_weightUnipotentInParabolicPointsSubgroup_iff,
    GeneralLinear.mem_weightUnipotentDefiningPointsSubgroup_iff,
    UpperUnitriangularGroup.mem_iff, Matrix.isUpperUnitriangular_def,
    GeneralLinear.pointsMulEquiv_apply, pointsMulEquiv_coe]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro i j hji
      have hne : i ≠ j := fun h ↦ hji.ne h.symm
      have hw : weights n i ≤ weights n j :=
        (weights_lt_weights_iff n i j).mpr hji |>.le
      simpa [Matrix.one_apply, hne] using h i j hw
    · intro i
      simpa using h i i le_rfl
  · rintro ⟨htri, hdiag⟩ i j hij
    rcases hij.eq_or_lt with hij | hij
    · have : i = j := weights_injective n hij
      subst j
      simpa using hdiag i
    · have hji : j < i := (weights_lt_weights_iff n i j).mp hij
      simpa [Matrix.one_apply, hji.ne'] using htri hji

/-- **The unipotent radical of the standard upper-triangular group is its
upper-unitriangular subgroup.** The relative ideal is identified pointwise by
`mem_upperUnitriangularPointsSubgroup_iff`; the pullback presents the finite-type radical in that
relative coordinate algebra. -/
@[simp]
theorem unipotentRadicalDefiningIdeal_finiteTypeCoordinateHopfAlgebra
    (k : Type u) [Field k] (n : ℕ) :
    (FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal
        (finiteTypeCoordinateHopfAlgebra k n)).comapOfSurjective
      (eqToHom (finiteTypeCoordinateHopfAlgebra_obj k n).symm).hom
      (ConcreteCategory.bijective_of_isIso
        (eqToHom (finiteTypeCoordinateHopfAlgebra_obj k n).symm)).2 =
      GeneralLinear.Dynamic.weightUnipotentInParabolicHopfIdeal k (weights n) := by
  let e : finiteTypeCoordinateHopfAlgebra k n ≅
      GeneralLinear.weightParabolicFiniteTypeCoordinateHopfAlgebra k (weights n) :=
    ObjectProperty.isoMk _ <| eqToIso <|
      finiteTypeCoordinateHopfAlgebra_obj k n |>.trans <|
        (GeneralLinear.weightParabolicFiniteTypeCoordinateHopfAlgebra_obj k (weights n)).symm
  have hRadical :=
    FiniteTypeCommHopfAlgCat.comapOfSurjective_unipotentRadicalDefiningIdeal e
  have hWeight :=
    unipotentRadicalDefiningIdeal_weightParabolicFiniteTypeCoordinateHopfAlgebra
      k (weights n) (weights_injective n)
  ext x
  rw [HopfIdeal.mem_comapOfSurjective, ← hRadical, HopfIdeal.mem_comapOfSurjective]
  have hx := congrArg (fun I ↦ x ∈ I) hWeight
  rw [HopfIdeal.mem_comapOfSurjective] at hx
  have hcomp :
      eqToHom (finiteTypeCoordinateHopfAlgebra_obj k n).symm ≫ e.hom.hom =
        eqToHom
          (GeneralLinear.weightParabolicFiniteTypeCoordinateHopfAlgebra_obj
            k (weights n)).symm := by
    simp only [e, ObjectProperty.isoMk_hom, ObjectProperty.homMk_hom, eqToIso.hom]
    rw [eqToHom_trans]
  have hcomp_apply :
      e.hom.hom ((eqToHom (finiteTypeCoordinateHopfAlgebra_obj k n).symm).hom x) =
        (eqToHom
          (GeneralLinear.weightParabolicFiniteTypeCoordinateHopfAlgebra_obj
            k (weights n)).symm).hom x := by
    rw [← ConcreteCategory.comp_apply, hcomp]
  rw [hcomp_apply]
  exact iff_of_eq hx

end

end TauCeti.GeneralLinear.UpperTriangular
