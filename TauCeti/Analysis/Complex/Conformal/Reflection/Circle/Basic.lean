/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Geometry.Euclidean.Inversion.Basic

/-!
# Reflection in a circle

This file connects Mathlib's Euclidean inversion to the conjugate-reciprocal formula for
reflection in a circle in `ℂ`. It also packages the restriction to the punctured plane as a
homeomorphism and records the inside/outside behavior needed for Schwarz reflection.
-/

public section

namespace TauCeti

open Complex EuclideanGeometry Metric Set
open scoped ComplexConjugate

/-- Euclidean inversion in `ℂ` is given by the standard conjugate-reciprocal formula for
reflection in a circle. -/
theorem inversion_eq_conj_reciprocal (c : ℂ) (r : ℝ) (z : ℂ) :
    inversion c r z = c + (r : ℂ) ^ 2 / (starRingEnd ℂ) (z - c) := by
  by_cases hz : z = c
  · subst z
    simp
  rw [inversion, vsub_eq_sub, vadd_eq_add, Complex.dist_eq, Complex.real_smul]
  push_cast
  rw [div_pow]
  have hnorm : (‖z - c‖ : ℂ) ^ 2 =
      (starRingEnd ℂ) (z - c) * (z - c) := by
    rw [← ofReal_pow, ← Complex.normSq_eq_norm_sq,
      Complex.normSq_eq_conj_mul_self, starRingEnd_apply, Complex.star_def]
  rw [hnorm]
  rw [starRingEnd_apply, Complex.star_def]
  field_simp
  ring

/-- Euclidean inversion restricts to a self-homeomorphism of the punctured complex plane. -/
noncomputable def circleReflectionHomeomorph (c : ℂ) (r : ℝ) (hr : r ≠ 0) :
    ({c}ᶜ : Set ℂ) ≃ₜ ({c}ᶜ : Set ℂ) where
  toFun z := ⟨inversion c r z, by simpa using (inversion_eq_center hr).not.mpr z.2⟩
  invFun z := ⟨inversion c r z, by simpa using (inversion_eq_center hr).not.mpr z.2⟩
  left_inv z := Subtype.ext (inversion_inversion c hr z)
  right_inv z := Subtype.ext (inversion_inversion c hr z)
  continuous_toFun :=
    ((continuousOn_const.inversion continuousOn_const continuousOn_id fun z hz ↦
      Set.mem_compl_singleton_iff.mp hz).restrict.subtype_mk _)
  continuous_invFun :=
    ((continuousOn_const.inversion continuousOn_const continuousOn_id fun z hz ↦
      Set.mem_compl_singleton_iff.mp hz).restrict.subtype_mk _)

/-- The punctured-plane circle-reflection homeomorphism acts by Euclidean inversion. -/
@[simp]
theorem coe_circleReflectionHomeomorph_apply (c : ℂ) (r : ℝ) (hr : r ≠ 0)
    (z : ({c}ᶜ : Set ℂ)) :
    (circleReflectionHomeomorph c r hr z : ℂ) = inversion c r z := by
  rfl

/-- The punctured-plane circle-reflection homeomorphism is its own inverse. -/
@[simp]
theorem circleReflectionHomeomorph_symm (c : ℂ) (r : ℝ) (hr : r ≠ 0) :
    (circleReflectionHomeomorph c r hr).symm = circleReflectionHomeomorph c r hr := by
  apply Homeomorph.ext
  intro z
  apply (circleReflectionHomeomorph c r hr).injective
  rw [(circleReflectionHomeomorph c r hr).apply_symm_apply]
  exact Subtype.ext (inversion_inversion c hr z).symm

/-- Inversion in a positive-radius circle sends a point into its open ball exactly when the
original point is in the exterior of its closed ball. -/
@[simp]
theorem dist_inversion_center_lt_iff {c z : ℂ} {r : ℝ} (hr : 0 < r) (hz : z ≠ c) :
    dist (inversion c r z) c < r ↔ r < dist z c := by
  rw [dist_inversion_center, div_lt_iff₀ (dist_pos.mpr hz)]
  constructor <;> intro h
  · nlinarith [mul_pos hr (dist_pos.mpr hz)]
  · nlinarith [mul_pos hr (dist_pos.mpr hz)]

/-- Inversion in a positive-radius circle sends a point outside its closed ball exactly when the
original point is in its open ball. -/
@[simp]
theorem lt_dist_inversion_center_iff {c z : ℂ} {r : ℝ} (hr : 0 < r) (hz : z ≠ c) :
    r < dist (inversion c r z) c ↔ dist z c < r := by
  rw [dist_inversion_center, lt_div_iff₀ (dist_pos.mpr hz)]
  constructor <;> intro h
  · nlinarith [mul_pos hr (dist_pos.mpr hz)]
  · nlinarith [mul_pos hr (dist_pos.mpr hz)]

end TauCeti
