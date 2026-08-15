/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.Faithful
public import TauCeti.Algebra.AlgebraicGroup.Representation.UnipotentPoint.Basic
public import Mathlib.FieldTheory.Perfect
import TauCeti.Algebra.AlgebraicGroup.Representation.JordanDecomposition.Basic

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

This is the bridge needed by Layer 5, "Unipotent groups", of the ReductiveGroups roadmap: a point
of a group given with a faithful representation can now be tested for unipotence in that one
representation instead of in every representation. The upper-unitriangular embedding
characterization is still to come.

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
    apply Comodule.pointsAction_injective_of_isFaithful hM
    have hGL :
        LinearMap.GeneralLinearGroup.ofLinearEquiv
            (Comodule.pointsAction M (Point.semisimplePart k H K g)) =
          LinearMap.GeneralLinearGroup.ofLinearEquiv
            (Comodule.pointsAction M (1 : WithConv (H →ₐ[k] K))) := by
      rw [Point.ofLinearEquiv_pointsAction_semisimplePart,
        GeneralLinearGroup.semisimplePart_eq_one_of_isUnipotent hg, map_one]
      exact ((LinearMap.GeneralLinearGroup.generalLinearEquiv K _).symm.map_one).symm
    exact (LinearMap.GeneralLinearGroup.generalLinearEquiv K _).symm.injective hGL

end

end TauCeti.HopfAlgebra
