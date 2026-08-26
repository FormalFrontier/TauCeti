/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.RealForm
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.DoubleCover
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.SpinorNorm
import Mathlib.Analysis.Real.Sqrt

/-!
# Compact real Spin groups

For a positive-definite real quadratic form, every nonzero norm is a square. The spinor norm on
the orthogonal group therefore agrees with the determinant modulo squares. Its restriction to the
special orthogonal group is trivial, so the Spin action is surjective.

This file applies that argument to the positive-definite signature form `realCliffordForm n 0` and
packages its Spin double cover. Topology, connectedness, and the universal-cover theorem remain
separate.

## Main definitions and results

* `CliffordAlgebra.orthogonalSpinorNorm_eq_detSquareClass_of_posDef` identifies the orthogonal
  spinor norm with the determinant square-class map for a positive-definite real form.
* `CliffordAlgebra.spinToSpecialOrthogonal_surjective_of_posDef` proves surjectivity for any
  finite-dimensional positive-definite real form.
* `CliffordAlgebra.realCliffordSpinGroup` names the real Spin groups by signature.
* `CliffordAlgebra.realCliffordSpinGroupZero` names the compact real Spin group.
* `CliffordAlgebra.realCliffordSpinDoubleCoverZero` packages its double cover in positive dimension.

## References

This advances the real Spin-group part of Layer 7 in
`TauCetiRoadmap/RepresentationTheory/SpinRepresentations/README.md`. See H. B. Lawson and
M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I §2.
-/

public section

open QuadraticMap

namespace CliffordAlgebra

open TauCeti

universe u

variable {V : Type u} [AddCommGroup V] [Module ℝ V]

variable [FiniteDimensional ℝ V]

/-- On a finite-dimensional positive-definite real quadratic space, the orthogonal spinor norm is
the square class of the determinant. -/
theorem orthogonalSpinorNorm_eq_detSquareClass_of_posDef
    (Q : QuadraticForm ℝ V) (hQ : Q.PosDef) :
    orthogonalSpinorNorm Q hQ.anisotropic.nondegenerate =
      QuadraticMap.orthogonalDetSquareClass Q := by
  exact orthogonalSpinorNorm_eq_detSquareClass_of_isSquare_apply Q hQ.anisotropic.nondegenerate
    fun v => Real.isSquare_iff.2 (hQ.nonneg v)

/-- The Spin action of a finite-dimensional positive-definite real quadratic space is onto its
special orthogonal group. -/
theorem spinToSpecialOrthogonal_surjective_of_posDef
    (Q : QuadraticForm ℝ V) (hQ : Q.PosDef) :
    Function.Surjective (spinToSpecialOrthogonal Q) := by
  exact spinToSpecialOrthogonal_surjective_of_isSquare_apply Q hQ.anisotropic.nondegenerate
    fun v => Real.isSquare_iff.2 (hQ.nonneg v)

/-- The real Spin group of signature `(p, q)`. -/
abbrev realCliffordSpinGroup (p q : ℕ) := spinGroup (realCliffordForm p q)

/-- The compact real Spin group `Spin(n)`. -/
abbrev realCliffordSpinGroupZero (n : ℕ) := realCliffordSpinGroup n 0

/-- The algebraic double cover from `Spin(n)` to the special orthogonal group in positive
dimension. -/
noncomputable def realCliffordSpinDoubleCoverZero (n : ℕ) [NeZero n] :
    GroupExtension (Multiplicative (ZMod 2)) (realCliffordSpinGroupZero n)
      (QuadraticMap.specialOrthogonalGroup (realCliffordForm n 0)) :=
  spinDoubleCoverOfSurjective (realCliffordForm n 0)
    (nondegenerate_realCliffordForm n 0)
    (spinToSpecialOrthogonal_surjective_of_posDef _ (posDef_realCliffordForm_zero n))

/-- The inclusion in the compact real Spin double cover sends the generator to the distinguished
element `-1` of the Spin group. -/
@[simp]
theorem realCliffordSpinDoubleCoverZero_inl_ofAdd_one (n : ℕ) [NeZero n] :
    (realCliffordSpinDoubleCoverZero n).inl (Multiplicative.ofAdd 1) =
      spinGroup.negOne (realCliffordForm n 0) (nondegenerate_realCliffordForm n 0).ne_zero := by
  rw [realCliffordSpinDoubleCoverZero, spinDoubleCoverOfSurjective_inl_ofAdd_one]

/-- The projection in the compact real Spin double cover is the Spin action. -/
@[simp]
theorem realCliffordSpinDoubleCoverZero_rightHom (n : ℕ) [NeZero n] :
    (realCliffordSpinDoubleCoverZero n).rightHom =
      spinToSpecialOrthogonal (realCliffordForm n 0) := by
  rw [realCliffordSpinDoubleCoverZero, spinDoubleCoverOfSurjective_rightHom]

end CliffordAlgebra
