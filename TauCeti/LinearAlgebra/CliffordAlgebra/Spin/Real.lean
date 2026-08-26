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
* `CliffordAlgebra.spinPQ` and `CliffordAlgebra.spinN` name the real and compact Spin groups.
* `CliffordAlgebra.spinNDoubleCover` packages the compact real Spin double cover in positive
  dimension.

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

private theorem posDef_unit_isSquare (Q : QuadraticForm ℝ V) (hQ : Q.PosDef) (v : V)
    [Invertible (Q v)] : IsSquare (unitOfInvertible (Q v)) := by
  have hvQ : Q v ≠ 0 := Invertible.ne_zero _
  have hv : v ≠ 0 := by
    intro hv
    subst v
    simp at hvQ
  rw [← isSquare_units_val_iff, val_unitOfInvertible, Real.isSquare_iff]
  exact (hQ v hv).le

variable [FiniteDimensional ℝ V]

/-- On a finite-dimensional positive-definite real quadratic space, the orthogonal spinor norm is
the square class of the determinant. -/
theorem orthogonalSpinorNorm_eq_detSquareClass_of_posDef
    (Q : QuadraticForm ℝ V) (hQ : Q.PosDef) :
    orthogonalSpinorNorm Q hQ.anisotropic.nondegenerate = orthogonalDetSquareClass Q := by
  exact orthogonalSpinorNorm_eq_detSquareClass_of_isSquare Q hQ.anisotropic.nondegenerate
    (posDef_unit_isSquare Q hQ)

/-- The Spin action of a finite-dimensional positive-definite real quadratic space is onto its
special orthogonal group. -/
theorem spinToSpecialOrthogonal_surjective_of_posDef
    (Q : QuadraticForm ℝ V) (hQ : Q.PosDef) :
    Function.Surjective (spinToSpecialOrthogonal Q) := by
  exact spinToSpecialOrthogonal_surjective_of_unit_isSquare Q hQ.anisotropic.nondegenerate
    (posDef_unit_isSquare Q hQ)

/-- The real Spin group of signature `(p, q)`. -/
abbrev spinPQ (p q : ℕ) := spinGroup (realCliffordForm p q)

/-- The compact real Spin group `Spin(n)`. -/
abbrev spinN (n : ℕ) := spinPQ n 0

/-- The algebraic double cover from `Spin(n)` to the special orthogonal group in positive
dimension. -/
noncomputable def spinNDoubleCover (n : ℕ) (hn : 0 < n) :
    GroupExtension (Multiplicative (ZMod 2)) (spinN n)
      (QuadraticMap.specialOrthogonalGroup (realCliffordForm n 0)) := by
  let : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  exact spinDoubleCoverOfSurjective (realCliffordForm n 0)
    (nondegenerate_realCliffordForm n 0)
    (spinToSpecialOrthogonal_surjective_of_posDef _ (posDef_realCliffordForm_zero n))

/-- The inclusion in the compact real Spin double cover sends the generator to the distinguished
element `-1` of the Spin group. -/
@[simp]
theorem spinNDoubleCover_inl_ofAdd_one (n : ℕ) (hn : 0 < n) :
    let _ : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
    (spinNDoubleCover n hn).inl (Multiplicative.ofAdd 1) =
      spinGroup.negOne (realCliffordForm n 0) (nondegenerate_realCliffordForm n 0).ne_zero := by
  let : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  rw [spinNDoubleCover, spinDoubleCoverOfSurjective_inl_ofAdd_one]

/-- The projection in the compact real Spin double cover is the Spin action. -/
@[simp]
theorem spinNDoubleCover_rightHom (n : ℕ) (hn : 0 < n) :
    (spinNDoubleCover n hn).rightHom =
      spinToSpecialOrthogonal (realCliffordForm n 0) := by
  let : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  rw [spinNDoubleCover, spinDoubleCoverOfSurjective_rightHom]

end CliffordAlgebra
