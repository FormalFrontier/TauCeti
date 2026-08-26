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

* `CliffordAlgebra.orthogonalSpinorNorm_eq_detSquareClass_of_posDef` identifies it with the
  orthogonal spinor norm for a positive-definite real form.
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
  have hpos := hQ v hv
  let u : ℝˣ := Units.mk0 (Real.sqrt (Q v)) (Real.sqrt_ne_zero'.2 hpos)
  refine ⟨u, ?_⟩
  apply Units.ext
  dsimp only [u]
  simpa only [val_unitOfInvertible, Units.val_mul, Units.val_mk0, pow_two] using
    (Real.sq_sqrt hpos.le).symm

variable [FiniteDimensional ℝ V]

/-- On a finite-dimensional positive-definite real quadratic space, the orthogonal spinor norm is
the square class of the determinant. -/
theorem orthogonalSpinorNorm_eq_detSquareClass_of_posDef
    (Q : QuadraticForm ℝ V) (hQ : Q.PosDef) :
    orthogonalSpinorNorm Q hQ.nondegenerate = orthogonalDetSquareClass Q := by
  let f : QuadraticMap.orthogonalGroup Q →* Multiplicative (SquareClassGroup ℝ) :=
    orthogonalSpinorNorm Q hQ.nondegenerate
  let g : QuadraticMap.orthogonalGroup Q →* Multiplicative (SquareClassGroup ℝ) :=
    orthogonalDetSquareClass Q
  let H : Subgroup (QuadraticMap.orthogonalGroup Q) :=
    @MonoidHom.eqLocus (QuadraticMap.orthogonalGroup Q) _
      (Multiplicative (SquareClassGroup ℝ)) _ f g
  have hH : H = ⊤ := QuadraticMap.subgroup_eq_top_of_reflection_mem
    Q hQ.nondegenerate H fun v _ => by
      change orthogonalSpinorNorm Q hQ.nondegenerate
          (QuadraticMap.reflectionOrthogonal Q v) =
        orthogonalDetSquareClass Q (QuadraticMap.reflectionOrthogonal Q v)
      rw [orthogonalSpinorNorm_reflectionOrthogonal, orthogonalDetSquareClass_apply]
      rw [QuadraticMap.coe_reflectionOrthogonal, QuadraticMap.det_reflection]
      have hsquare : squareClassHom (unitOfInvertible (Q v)) = 1 := by
        rw [squareClassHom_apply]
        simpa only [ofAdd_zero] using congrArg Multiplicative.ofAdd
          ((squareClass_eq_zero_iff _).2 (posDef_unit_isSquare Q hQ v))
      rw [show -(unitOfInvertible (Q v)) = (-1 : ℝˣ) * unitOfInvertible (Q v) by
          apply Units.ext
          simp]
      rw [map_mul, hsquare]
      exact mul_one (squareClassHom (-1 : ℝˣ))
  apply MonoidHom.ext
  intro x
  have hx : x ∈ H := by rw [hH]; trivial
  exact hx

/-- The Spin action of a finite-dimensional positive-definite real quadratic space is onto its
special orthogonal group. -/
theorem spinToSpecialOrthogonal_surjective_of_posDef
    (Q : QuadraticForm ℝ V) (hQ : Q.PosDef) :
    Function.Surjective (spinToSpecialOrthogonal Q) := by
  rw [← MonoidHom.range_eq_top]
  rw [range_spinToSpecialOrthogonal_eq_ker_spinorNorm Q hQ.nondegenerate]
  rw [Subgroup.eq_top_iff']
  intro g
  rw [MonoidHom.mem_ker, spinorNorm_apply,
    orthogonalSpinorNorm_eq_detSquareClass_of_posDef Q hQ]
  rw [orthogonalDetSquareClass_apply]
  have hgdet := (QuadraticMap.mem_specialOrthogonalGroup_iff.mp g.2).2
  have hgdet' : LinearEquiv.det
      ((Subgroup.inclusion (QuadraticMap.specialOrthogonalGroup_le_orthogonalGroup Q) g :
        QuadraticMap.orthogonalGroup Q) : V ≃ₗ[ℝ] V) = 1 := by
    rw [show ((Subgroup.inclusion
      (QuadraticMap.specialOrthogonalGroup_le_orthogonalGroup Q) g :
        QuadraticMap.orthogonalGroup Q) : V ≃ₗ[ℝ] V) = (g : V ≃ₗ[ℝ] V) by
      apply LinearEquiv.ext
      intro v
      rfl]
    exact hgdet
  rw [hgdet', map_one]

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

/-- The inclusion in the compact real Spin double cover sends the generator to the Clifford
scalar `-1`. -/
@[simp]
theorem spinNDoubleCover_inl_ofAdd_one (n : ℕ) (hn : 0 < n) :
    (((spinNDoubleCover n hn).inl (Multiplicative.ofAdd 1) : spinN n) :
      CliffordAlgebra (realCliffordForm n 0)) = -1 := by
  let : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  rw [spinNDoubleCover, spinDoubleCoverOfSurjective_inl_ofAdd_one,
    spinGroup.coe_negOne]

/-- The projection in the compact real Spin double cover is the Spin action. -/
@[simp]
theorem spinNDoubleCover_rightHom (n : ℕ) (hn : 0 < n) :
    (spinNDoubleCover n hn).rightHom =
      spinToSpecialOrthogonal (realCliffordForm n 0) := by
  let : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  rw [spinNDoubleCover, spinDoubleCoverOfSurjective_rightHom]

end CliffordAlgebra
