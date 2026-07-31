/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Complex.UnitDisc.Basic
public import Mathlib.Topology.Algebra.ConstMulAction

/-!
# Basic API for the complex unit disc

This file collects small API lemmas for Mathlib's `Complex.UnitDisc`.
-/

public section

namespace TauCeti

open Complex

namespace Complex.UnitDisc

/-- Rotating the disc origin by a circle element fixes it. This is the `smul_zero`
normalization for Mathlib's `Circle` action on `Complex.UnitDisc`, which is a bare
`MulAction` and so does not get the generic `smul_zero` simp lemma. -/
@[simp]
lemma circle_smul_zero (u : Circle) : u • (0 : _root_.Complex.UnitDisc) = 0 := by
  ext
  simp

/-- A circle rotation of a disc point vanishes exactly when the point does. This is the
`smul_eq_zero` normalization for Mathlib's `Circle` action on `Complex.UnitDisc`. -/
@[simp]
lemma circle_smul_eq_zero_iff (u : Circle) {z : _root_.Complex.UnitDisc} :
    u • z = 0 ↔ z = 0 := by
  rw [← _root_.Complex.UnitDisc.coe_eq_zero, _root_.Complex.UnitDisc.coe_circle_smul, mul_eq_zero]
  simp

/-- The set of unit-disc points of Euclidean norm at most `ρ < 1` is compact: it is carried by
the embedding into `ℂ` onto the closed Euclidean ball of radius `ρ`, which the hypothesis
`ρ < 1` places inside the open disc. -/
lemma isCompact_setOf_norm_le {ρ : ℝ} (hρ : ρ < 1) :
    IsCompact {z : _root_.Complex.UnitDisc | ‖(z : ℂ)‖ ≤ ρ} := by
  rw [_root_.Complex.UnitDisc.isEmbedding_coe.isCompact_iff]
  have himg : ((↑) : _root_.Complex.UnitDisc → ℂ) ''
      {z : _root_.Complex.UnitDisc | ‖(z : ℂ)‖ ≤ ρ} = Metric.closedBall (0 : ℂ) ρ := by
    ext w
    simp only [Set.mem_image, Set.mem_setOf_eq, Metric.mem_closedBall, dist_zero_right]
    exact ⟨fun ⟨z, hz, hzw⟩ => hzw ▸ hz, fun hw =>
      ⟨_root_.Complex.UnitDisc.mk w (lt_of_le_of_lt hw hρ), by simpa using hw, by simp⟩⟩
  rw [himg]
  exact isCompact_closedBall _ _

end Complex.UnitDisc

/-- A fixed circle rotation is continuous on the bundled open disc. -/
lemma continuous_circle_smul_unitDisc (u : Circle) :
    Continuous fun z : Complex.UnitDisc => u • z := by
  rw [Complex.UnitDisc.isEmbedding_coe.continuous_iff]
  exact ((continuous_const (y := (u : ℂ))).mul Complex.UnitDisc.continuous_coe).congr fun z => by
    simp only [Function.comp_def, Complex.UnitDisc.coe_circle_smul, Pi.mul_apply]

/-- Circle rotations act continuously on the bundled open unit disc. -/
instance instContinuousConstSMulCircleUnitDisc :
    ContinuousConstSMul Circle Complex.UnitDisc where
  continuous_const_smul := continuous_circle_smul_unitDisc

end TauCeti
