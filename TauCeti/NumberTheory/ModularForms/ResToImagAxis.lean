/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.NumberTheory.ModularForms.Identities
public import TauCeti.Analysis.Complex.UpperHalfPlane.ResToImagAxis

/-!
# The slash action on the imaginary axis

The restriction `UpperHalfPlane.resToImagAxis` of a function on `ℍ` to the positive imaginary
axis intertwines the weight-`k` slash action of `S = ![![0, -1], ![1, 0]]` with the involution
`t ↦ 1 / t` of the axis. This is the reflection underlying the functional equation of the
L-function of a modular form.

## Main results

* `UpperHalfPlane.resToImagAxis_slash_S`: the restriction of `F ∣[k] S` at `t` is
  `i ^ (-k) t ^ (-k)` times the restriction of `F` at `1 / t`.

Ported from the AINTLIB `LeanModularForms` project
(`LeanModularForms/Modularforms/ResToImagAxis.lean`, Chris Birkbeck,
<https://github.com/CBirkbeck/AINTLIB/tree/main/projects/LeanModularForms>); the generic
material about the restriction is in
`TauCeti/Analysis/Complex/UpperHalfPlane/ResToImagAxis.lean`.
-/

public section

open Complex ModularGroup

open scoped ModularForm MatrixGroups

namespace UpperHalfPlane

/-- **The `S`-involution on the imaginary axis**: slashing by `S` turns `t` into `1 / t`,
`(F ∣[k] S) (i t) = i ^ (-k) t ^ (-k) F (i / t)`. This is the reflection underlying the
functional equation of the L-function. -/
theorem resToImagAxis_slash_S (F : ℍ → ℂ) (k : ℤ) {t : ℝ} (ht : 0 < t) :
    resToImagAxis (F ∣[k] S) t =
      Complex.I ^ (-k) * (t : ℂ) ^ (-k) * resToImagAxis F (1 / t) := by
  have ht' : (0 : ℝ) < 1 / t := by positivity
  have h : mk _ (⟨Complex.I * t, by simpa using ht⟩ : ℍ).im_inv_neg_coe_pos =
      (⟨Complex.I * (1 / t : ℝ), by simpa using ht'⟩ : ℍ) :=
    UpperHalfPlane.ext (by
      -- `(-(i t))⁻¹ = i / t`, since `i * i = -1`
      have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
      have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
      push_cast
      field_simp
      linear_combination -hI)
  rw [resToImagAxis_of_pos _ ht, SlashInvariantForm.slash_S_apply, h,
    resToImagAxis_of_pos F ht']
  simp only [mul_zpow]
  ring

end UpperHalfPlane
