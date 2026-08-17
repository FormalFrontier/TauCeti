/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.FunctorOfPoints
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Basic

/-!
# Matrix points of general-linear quotient group schemes

A Hopf ideal in the coordinate algebra of `GLₙ` cuts out a subgroup of its functor of points.
This file transports that subgroup through `GeneralLinear.pointsMulEquiv`, viewing it directly as
a subgroup of invertible matrices over the value algebra.

## Main declarations

* `TauCeti.GeneralLinear.quotientMatrixPointsSubgroup`: the matrix-valued points cut out by a Hopf
  ideal in the coordinate algebra of `GLₙ`.
* `TauCeti.GeneralLinear.mem_quotientMatrixPointsSubgroup_iff`: membership is vanishing of the
  corresponding convolution point on the Hopf ideal.
-/

public section

namespace TauCeti.GeneralLinear

universe u w

variable {R : Type u} [CommRing R]

/-- The matrix-valued points of the closed subgroup of `GLₙ` cut out by the Hopf ideal `I`. -/
noncomputable def quotientMatrixPointsSubgroup (n : ℕ)
    (I : HopfIdeal R (coordinateHopfAlgebra R n))
    (A : Type w) [CommRing A] [Algebra R A] :
    Subgroup (Matrix.GeneralLinearGroup (Fin n) A) :=
  (CommHopfAlgCat.quotientPointsSubgroup
      (coordinateHopfAlgebra R n) I (CommAlgCat.of R A)).map
    (pointsMulEquiv n).toMonoidHom

/-- A matrix belongs to the closed subgroup cut out by `I` exactly when its corresponding
convolution point vanishes on `I`. -/
@[simp]
theorem mem_quotientMatrixPointsSubgroup_iff (n : ℕ)
    (I : HopfIdeal R (coordinateHopfAlgebra R n))
    (A : Type w) [CommRing A] [Algebra R A]
    (g : Matrix.GeneralLinearGroup (Fin n) A) :
    g ∈ quotientMatrixPointsSubgroup n I A ↔
      ∀ x ∈ I, ((pointsMulEquiv (R := R) n).symm g).ofConv x = 0 := by
  unfold quotientMatrixPointsSubgroup
  rw [Subgroup.mem_map_equiv, CommHopfAlgCat.mem_quotientPointsSubgroup_iff]

end TauCeti.GeneralLinear
