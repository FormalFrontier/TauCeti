/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Complex.UnitDisc.Basic
public import Mathlib.Topology.Algebra.ConstMulAction

/-!
# Basic API for the complex unit disc

This file collects small API lemmas for Mathlib's `Complex.UnitDisc`. It covers the transport
between a self-map of the bundled disc and a scalar representative `ℂ → ℂ` of it — such a
representative maps `Metric.ball 0 1` into itself, and bijectively onto itself when the bundled
map is an equivalence — together with the basic properties of the `Circle` action on the disc: the
disc is nontrivial, a rotation is determined by its value at any one nonzero point, and hence the
circle acts faithfully.
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
    simp only [Set.mem_image, Set.mem_ofPred_eq, Metric.mem_closedBall, dist_zero_right]
    exact ⟨fun ⟨z, hz, hzw⟩ => hzw ▸ hz, fun hw =>
      ⟨_root_.Complex.UnitDisc.mk w (lt_of_le_of_lt hw hρ), by simpa using hw, by simp⟩⟩
  rw [himg]
  exact isCompact_closedBall _ _

end Complex.UnitDisc

open Metric Set in
/-- A scalar representative of a self-map of the disc maps the open unit ball into itself. -/
lemma mapsTo_ball_of_forall_unitDisc_coe_eq {e : Complex.UnitDisc → Complex.UnitDisc} {f : ℂ → ℂ}
    (hf : ∀ z : Complex.UnitDisc, (e z : ℂ) = f z) :
    MapsTo f (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) := by
  intro w hw
  have hw' : ‖w‖ < 1 := by simpa [mem_ball_zero_iff] using hw
  have := (e (Complex.UnitDisc.mk w hw')).norm_lt_one
  rw [hf (Complex.UnitDisc.mk w hw')] at this
  simpa [mem_ball_zero_iff] using this

open Metric Set in
/-- A self-equivalence of `Complex.UnitDisc`, read through a scalar representative, is a bijection
of `Metric.ball 0 1` onto itself. -/
lemma bijOn_ball_of_unitDiscEquiv (E : Complex.UnitDisc ≃ Complex.UnitDisc) {φ : ℂ → ℂ}
    (hφ : ∀ z : Complex.UnitDisc, (E z : ℂ) = φ z) :
    BijOn φ (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) := by
  have mem : ∀ z : Complex.UnitDisc, (z : ℂ) ∈ ball (0 : ℂ) 1 := fun z => by
    simpa [mem_ball_zero_iff] using z.norm_lt_one
  have exists_coe : ∀ w ∈ ball (0 : ℂ) 1, ∃ z : Complex.UnitDisc, (z : ℂ) = w := fun w hw =>
    ⟨Complex.UnitDisc.mk w (by simpa [mem_ball_zero_iff] using hw), Complex.UnitDisc.coe_mk _ _⟩
  refine ⟨mapsTo_ball_of_forall_unitDisc_coe_eq hφ, fun w₁ h₁ w₂ h₂ h => ?_, fun v hv => ?_⟩
  · obtain ⟨z₁, rfl⟩ := exists_coe w₁ h₁
    obtain ⟨z₂, rfl⟩ := exists_coe w₂ h₂
    rw [← hφ z₁, ← hφ z₂] at h
    exact congrArg _ (E.injective (Complex.UnitDisc.coe_injective h))
  · obtain ⟨v', rfl⟩ := exists_coe v hv
    exact ⟨(E.symm v' : ℂ), mem _, by rw [← hφ (E.symm v'), Equiv.apply_symm_apply]⟩

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

/-- The open unit disc has more than one point: `0` and `1 / 2` are both in it. -/
instance instNontrivialUnitDisc : Nontrivial Complex.UnitDisc := by
  have h : ‖(2⁻¹ : ℂ)‖ < 1 := by
    rw [norm_inv, Complex.norm_ofNat]
    norm_num
  exact ⟨⟨Complex.UnitDisc.mk (2⁻¹ : ℂ) h, 0, by simp⟩⟩

/-- **A rotation is determined by its value at a single nonzero point of the disc.** Multiplication
by a nonzero complex number is injective, and the disc inherits that from `ℂ`. -/
theorem circle_smul_left_injective {z : Complex.UnitDisc} (hz : z ≠ 0) :
    Function.Injective fun u : Circle => u • z := by
  intro u v h
  have hz' : (z : ℂ) ≠ 0 := fun hc => hz (Complex.UnitDisc.coe_eq_zero.1 hc)
  have h' : (u : ℂ) * (z : ℂ) = (v : ℂ) * (z : ℂ) := by
    simpa only [Complex.UnitDisc.coe_circle_smul] using
      congrArg (fun w : Complex.UnitDisc => (w : ℂ)) h
  exact Circle.ext (mul_right_cancel₀ hz' h')

/-- **The circle acts faithfully on the unit disc.** Only the trivial rotation fixes the whole
disc, because the disc contains a nonzero point. -/
instance instFaithfulSMulCircleUnitDisc : FaithfulSMul Circle Complex.UnitDisc where
  eq_of_smul_eq_smul h := by
    obtain ⟨z, hz⟩ := exists_ne (0 : Complex.UnitDisc)
    exact circle_smul_left_injective hz (h z)

end TauCeti
