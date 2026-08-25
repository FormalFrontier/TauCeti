/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Smooth.CommHopfAlgCat
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.SmoothConnected
public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Basic
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Lift

/-!
# Smoothness of the special linear group

The coordinate algebra of `SLₙ` is smooth over every commutative ring. The proof uses the
infinitesimal lifting criterion for formal smoothness. Under the algebra-valued-points
equivalence, lifting a coordinate-algebra map through a square-zero quotient is exactly lifting a
special-linear matrix;
`Matrix.SpecialLinearGroup.map_quotient_mk_surjective_of_isNilpotent` supplies that lift. Finite
presentation is inherited from the determinant localization presenting `GLₙ` and the principal
determinant-one quotient presenting `SLₙ`.

The result is valid in every natural rank, including rank zero, over bases with zero divisors and
in every characteristic.

## Main declarations

* `TauCeti.SpecialLinear.instSmoothCoordinateHopfAlgebra`: the coordinate algebra of `SLₙ` is
  smooth.
* `TauCeti.SpecialLinear.smoothCommHopfAlgProperty_finiteTypeCoordinateHopfAlgebra`: the same
  result stated for the finite-type commutative Hopf algebra.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapter 2.
* The Stacks Project, Tag 00TI (formal smoothness), and Tags 00T2 and 00TN (equivalent notions of
  smooth algebras).
-/

public section

open WithConv

namespace TauCeti.SpecialLinear

universe u

noncomputable section

variable (R : Type u) [CommRing R] (n : ℕ)

/-- The special-linear coordinate algebra is formally smooth over its ground ring.

Via the functor-of-points description, this is the assertion that determinant-one matrices lift
through square-zero quotients. -/
private instance instFormallySmoothCoordinateHopfAlgebra :
    Algebra.FormallySmooth R (coordinateHopfAlgebra R n) := by
  apply Algebra.FormallySmooth.of_comp_surjective
  intro B _ _ I hI f
  obtain ⟨t, ht⟩ :=
    Matrix.SpecialLinearGroup.map_quotient_mk_surjective_of_isNilpotent I ⟨2, hI⟩
      ((pointsMulEquiv (R := R) (A := B ⧸ I) n) (toConv f))
  let g : WithConv (coordinateHopfAlgebra R n →ₐ[R] B) :=
    (pointsMulEquiv (R := R) (A := B) n).symm t
  refine ⟨g.ofConv, ?_⟩
  apply toConv_injective
  apply (pointsMulEquiv (R := R) (A := B ⧸ I) n).injective
  rw [← AlgHom.mapValue_apply]
  rw [pointsMulEquiv_mapValue]
  have hg : (pointsMulEquiv (R := R) (A := B) n) g = t := by simp [g]
  rw [hg]
  have hq : (Ideal.Quotient.mkₐ R I).toRingHom = Ideal.Quotient.mk I :=
    Ideal.Quotient.mkₐ_toRingHom (R₁ := R) I
  rw [hq]
  exact ht

/-- The coordinate algebra of `SLₙ` is smooth over every commutative ring. -/
instance instSmoothCoordinateHopfAlgebra :
    Algebra.Smooth R (coordinateHopfAlgebra R n) := by
  have hfg : (definingHopfIdeal R n).toIdeal.FG := by
    rw [definingHopfIdeal_toIdeal]
    exact Submodule.fg_span_singleton _
  let _ : Algebra.FinitePresentation R (coordinateHopfAlgebra R n) :=
    Algebra.FinitePresentation.quotient hfg
  exact ⟨inferInstance, inferInstance⟩

/-- The finite-type commutative Hopf algebra representing `SLₙ` has smooth coordinate ring. -/
theorem smoothCommHopfAlgProperty_finiteTypeCoordinateHopfAlgebra :
    smoothCommHopfAlgProperty R (finiteTypeCoordinateHopfAlgebra R n).obj := by
  rw [smoothCommHopfAlgProperty_iff, finiteTypeCoordinateHopfAlgebra_obj]
  infer_instance

end

end TauCeti.SpecialLinear
