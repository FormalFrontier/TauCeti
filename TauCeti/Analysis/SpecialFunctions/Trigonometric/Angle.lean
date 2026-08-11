/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle

/-!
# Normalising a real angle into `[0, 2π)`

`Real.Angle` is `ℝ` modulo `2π`, and `toIcoMod Real.two_pi_pos 0` is the section of the quotient
map picking the representative in `[0, 2π)`. Mathlib records one direction of the relationship
between the two, as `Real.Angle.coe_toIcoMod`: normalising and then projecting to `Real.Angle`
changes nothing.

This file records that the section is *injective on angles* — the normalisations of two reals
agree exactly when the reals agree in `Real.Angle`. That is the transport step behind any
computation of a normalised angle: the identity is proved in `Real.Angle`, where `2π` is
invisible, and then read back as an equality of representatives.

## Main results

* `Real.Angle.toIcoMod_eq_toIcoMod_iff_coe_eq`: two reals have the same `[0, 2π)` representative
  exactly when they are equal in `Real.Angle`.
-/

public section

namespace TauCeti

/-- **Equal angles are exactly equal normalisations.** Two reals agree in `Real.Angle` — that is,
differ by an integer multiple of `2π` — exactly when their representatives in `[0, 2π)` agree,
since the normalisation discards precisely such a multiple.

The forward direction is Mathlib's `Real.Angle.coe_toIcoMod` applied on both sides; the reverse
shifts one argument by the multiple and uses `toIcoMod_add_zsmul`. -/
theorem _root_.Real.Angle.toIcoMod_eq_toIcoMod_iff_coe_eq {x y : ℝ} :
    toIcoMod Real.two_pi_pos 0 x = toIcoMod Real.two_pi_pos 0 y ↔
      (x : Real.Angle) = (y : Real.Angle) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← Real.Angle.coe_toIcoMod x 0, ← Real.Angle.coe_toIcoMod y 0, h]
  · obtain ⟨k, hk⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp h
    have hshift : x = y + k • (2 * Real.pi) := by rw [zsmul_eq_mul]; linarith
    rw [hshift, toIcoMod_add_zsmul]

end TauCeti
