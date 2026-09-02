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

* `TauCeti.GeneralLinear.UpperTriangular.unipotentRadicalDefiningIdeal`:
  the relative upper-unitriangular Hopf ideal is the unipotent-radical defining ideal.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapters 13 and 17.
* T. A. Springer, *Linear Algebraic Groups*, Sections 6.2--6.3.

This supplies the concrete unipotent radical of the standard Borel candidate required by Layers
5 and 7 of the ReductiveGroups roadmap. Maximal solvability of that candidate remains downstream.
-/

public section

open CategoryTheory

namespace TauCeti.GeneralLinear.UpperTriangular

universe u

noncomputable section

/-- The relative upper-unitriangular Hopf ideal in the finite-type coordinate algebra of the
standard upper-triangular group. -/
noncomputable def upperUnitriangularHopfIdeal (k : Type u) [Field k] (n : ℕ) :
    HopfIdeal k (finiteTypeCoordinateHopfAlgebra k n).obj :=
  let e : finiteTypeCoordinateHopfAlgebra k n ≅
      GeneralLinear.weightParabolicFiniteTypeCoordinateHopfAlgebra k (weights n) :=
    ObjectProperty.isoMk _ <| eqToIso <|
      finiteTypeCoordinateHopfAlgebra_obj k n |>.trans <|
        (GeneralLinear.weightParabolicFiniteTypeCoordinateHopfAlgebra_obj k (weights n)).symm
  (GeneralLinear.weightUnipotentInParabolicFiniteTypeHopfIdeal k (weights n)).comapOfSurjective
    (FiniteTypeCommHopfAlgCat.toBialgHom e.hom)
    (ConcreteCategory.bijective_of_isIso e.hom).2

/-- **The unipotent radical of the standard upper-triangular group is its
upper-unitriangular subgroup.** The latter is expressed as the relative weight-unipotent Hopf
ideal in the upper-triangular coordinate algebra. -/
theorem unipotentRadicalDefiningIdeal (k : Type u) [Field k] (n : ℕ) :
    FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal
        (finiteTypeCoordinateHopfAlgebra k n) =
      upperUnitriangularHopfIdeal k n := by
  let e : finiteTypeCoordinateHopfAlgebra k n ≅
      GeneralLinear.weightParabolicFiniteTypeCoordinateHopfAlgebra k (weights n) :=
    ObjectProperty.isoMk _ <| eqToIso <|
      finiteTypeCoordinateHopfAlgebra_obj k n |>.trans <|
        (GeneralLinear.weightParabolicFiniteTypeCoordinateHopfAlgebra_obj k (weights n)).symm
  rw [← FiniteTypeCommHopfAlgCat.comapOfSurjective_unipotentRadicalDefiningIdeal e,
    unipotentRadicalDefiningIdeal_weightParabolicFiniteTypeCoordinateHopfAlgebra
      k (weights n) (weights_injective n)]
  dsimp [e, upperUnitriangularHopfIdeal]

end

end TauCeti.GeneralLinear.UpperTriangular
