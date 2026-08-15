/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.Faithful
public import TauCeti.Algebra.AlgebraicGroup.Representation.JordanDecomposition.Basic

/-!
# Detecting unipotent points in a faithful representation

The definition of a unipotent point of an affine group quantifies over every finite-dimensional
representation. This file proves the usable faithful-representation criterion over a perfect
value field: if one finite-dimensional comodule defines a closed immersion into a general linear
group, then a point is unipotent exactly when it acts unipotently on that comodule.

The substantive direction uses the Jordan decomposition of the point. If its action in the
faithful comodule is unipotent, its semisimple part acts trivially there. The same is true on the
inverse point, so the semisimple part agrees with the identity both on the matrix coefficients and
on their antipode images. Faithfulness says that these two coefficient algebras generate the whole
coordinate Hopf algebra; hence the semisimple part is the identity, which characterizes a
unipotent point.

This is the bridge needed by Layer 5, "Unipotent groups", of the ReductiveGroups roadmap: a closed
immersion into an upper-unitriangular group can now be tested in its defining faithful
representation instead of separately in every representation.

## Main declaration

* `TauCeti.HopfAlgebra.isUnipotentPoint_iff_isUnipotent_pointsAction_of_isFaithful`: a faithful
  finite-dimensional representation detects unipotence of points over a perfect value field.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, I.2.
* T. A. Springer, *Linear Algebraic Groups*, §2.4.
-/

public section

open WithConv

namespace TauCeti.HopfAlgebra

universe u

variable {k H K : Type u} [Field k] [CommRing H] [_root_.HopfAlgebra k H]
  [Field K] [Algebra k K] [PerfectField K]

noncomputable section

/-- **Over a perfect value field, a faithful finite-dimensional representation detects unipotent
points.**

The forward implication is the defining universal property of a unipotent point. For the
converse, faithfulness ensures that the comodule's matrix coefficients and their antipode images
generate the coordinate Hopf algebra, so triviality of the semisimple part on this one comodule
forces triviality of the semisimple part as a point. -/
theorem isUnipotentPoint_iff_isUnipotent_pointsAction_of_isFaithful
    (M : FGComoduleCat.{u, u, u} k H)
    (hM : Comodule.IsFaithful (k := k) (H := H) (V := M))
    (g : WithConv (H →ₐ[k] K)) :
    IsUnipotentPoint g ↔
      GeneralLinearGroup.IsUnipotent
        (LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction M g)) := by
  constructor
  · intro hg
    exact (isUnipotentPoint_def g).mp hg M
  · intro hg
    rw [Point.isUnipotentPoint_iff_semisimplePart_eq_one]
    let s := Point.semisimplePart k H K g
    have hsemisimpleAction :
        GeneralLinearGroup.semisimplePart
            (LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction M g)) = 1 :=
      GeneralLinearGroup.semisimplePart_eq_one_of_isUnipotent hg
    have hsEnd :
        Comodule.endOfPoint M s.ofConv =
          Comodule.endOfPoint M (1 : WithConv (H →ₐ[k] K)).ofConv := by
      calc
        Comodule.endOfPoint M s.ofConv =
            (GeneralLinearGroup.semisimplePart
              (LinearMap.GeneralLinearGroup.ofLinearEquiv
                (Comodule.pointsAction M g)) : Module.End K _) :=
          Point.endOfPoint_semisimplePart k H K g M
        _ = (1 : Module.End K _) := congrArg Units.val hsemisimpleAction
        _ = Comodule.endOfPoint M (1 : WithConv (H →ₐ[k] K)).ofConv := by
          exact (Comodule.endOfPoint_convOne M).symm
    have hsAction :
        Comodule.pointsAction M s =
          Comodule.pointsAction M (1 : WithConv (H →ₐ[k] K)) := by
      apply LinearEquiv.toLinearMap_injective
      simpa only [Comodule.pointsAction_toLinearMap] using hsEnd
    have hsInvAction :
        Comodule.pointsAction M s⁻¹ =
          Comodule.pointsAction M (1 : WithConv (H →ₐ[k] K))⁻¹ := by
      simpa only [map_inv] using congrArg Inv.inv hsAction
    have hsInvEnd :
        Comodule.endOfPoint M (s⁻¹).ofConv =
          Comodule.endOfPoint M ((1 : WithConv (H →ₐ[k] K))⁻¹).ofConv := by
      simpa only [Comodule.pointsAction_toLinearMap] using
        congrArg LinearEquiv.toLinearMap hsInvAction
    have hsCoefficients :
        Set.EqOn s.ofConv (1 : WithConv (H →ₐ[k] K)).ofConv
          (Comodule.matrixCoefficientSubalgebra (R := k) (C := H) (M := M)) :=
      Comodule.eqOn_matrixCoefficientSubalgebra_of_endOfPoint_eq _ _ hsEnd
    have hsInvCoefficients :
        Set.EqOn (s⁻¹).ofConv ((1 : WithConv (H →ₐ[k] K))⁻¹).ofConv
          (Comodule.matrixCoefficientSubalgebra (R := k) (C := H) (M := M)) :=
      Comodule.eqOn_matrixCoefficientSubalgebra_of_endOfPoint_eq _ _ hsInvEnd
    have hsAntipodeCoefficients :
        Set.EqOn s.ofConv (1 : WithConv (H →ₐ[k] K)).ofConv
          ((Comodule.matrixCoefficientSubalgebra (R := k) (C := H) (M := M)).map
            (_root_.HopfAlgebra.antipodeAlgHom k H)) := by
      rintro y ⟨x, hx, rfl⟩
      -- The subalgebra map leaves the algebra-hom coercion opaque to rewriting; expose its
      -- underlying antipode value so the pointwise inverse formula applies.
      change s.ofConv (_root_.HopfAlgebraStruct.antipode k x) =
        (1 : WithConv (H →ₐ[k] K)).ofConv (_root_.HopfAlgebraStruct.antipode k x)
      simpa only [← AlgHom.convInv_apply] using hsInvCoefficients hx
    let b := Module.finBasis k M
    have hgenerate :
        Comodule.matrixCoefficientSubalgebra (R := k) (C := H) (M := M) ⊔
            (Comodule.matrixCoefficientSubalgebra (R := k) (C := H) (M := M)).map
              (_root_.HopfAlgebra.antipodeAlgHom k H) = ⊤ :=
      (Comodule.isFaithful_iff_matrixCoefficientSubalgebra_sup_antipode_eq_top b).mp hM
    have hsTop := AlgHom.eqOn_sup hsCoefficients hsAntipodeCoefficients
    rw [hgenerate] at hsTop
    -- Fold the local name back into the Jordan characterization which is the current goal.
    change s = 1
    apply WithConv.ofConv_injective
    apply AlgHom.ext
    intro x
    exact hsTop (by simp)

end

end TauCeti.HopfAlgebra
