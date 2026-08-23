/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic

/-!
# Ratios of points in a common half-plane lie in the slit plane

The quotient `z₂ / z₁` of two points of an open half-plane through the origin is never a
nonpositive real, so it lies in `Complex.slitPlane`. The half-plane is encoded by a normal
direction `a`: its members are the `z` with `0 < (conj a * z).re`. Specializations to the
four axis-aligned half-planes cover the common cases.

These criteria feed logarithm evaluations of index integrals: a curve piece confined to a
half-plane about the winding point has slit-compatible chord ratios, so its index integral
is a principal logarithm.

## Main declarations

* `TauCeti.div_mem_slitPlane_of_re_conj_mul_pos`
* `TauCeti.div_mem_slitPlane_of_re_pos`, `…_of_re_neg`, `…_of_im_pos`, `…_of_im_neg`
-/

public section

open Complex

namespace TauCeti

/-- The ratio of two members of an open half-plane through the origin lies in the slit
plane. The half-plane with normal direction `a` is `{z | 0 < (conj a * z).re}`; degenerate
`a` admits no members, so no nonvanishing hypothesis is needed. -/
theorem div_mem_slitPlane_of_re_conj_mul_pos {a z₁ z₂ : ℂ}
    (h₁ : 0 < ((starRingEnd ℂ) a * z₁).re) (h₂ : 0 < ((starRingEnd ℂ) a * z₂).re) :
    z₂ / z₁ ∈ slitPlane := by
  have hz₁ : z₁ ≠ 0 := by rintro rfl; simp at h₁
  by_contra hmem
  rw [mem_slitPlane_iff, not_or, not_lt, not_ne_iff] at hmem
  obtain ⟨hre, him⟩ := hmem
  have heq : z₂ / z₁ = (((z₂ / z₁).re : ℝ) : ℂ) := Complex.ext (by simp) (by simpa using him)
  have hz₂ : z₂ = (((z₂ / z₁).re : ℝ) : ℂ) * z₁ := by
    rw [← heq, div_mul_cancel₀ _ hz₁]
  have hkey : ((starRingEnd ℂ) a) * ((((z₂ / z₁).re : ℝ) : ℂ) * z₁) =
      (((z₂ / z₁).re : ℝ) : ℂ) * ((starRingEnd ℂ) a * z₁) := by ring
  rw [hz₂, hkey, Complex.re_ofReal_mul] at h₂
  nlinarith

/-- Two points in the right half-plane have their ratio in the slit plane. -/
theorem div_mem_slitPlane_of_re_pos {z₁ z₂ : ℂ} (h₁ : 0 < z₁.re) (h₂ : 0 < z₂.re) :
    z₂ / z₁ ∈ slitPlane :=
  div_mem_slitPlane_of_re_conj_mul_pos (a := 1) (by simpa) (by simpa)

/-- Two points in the left half-plane have their ratio in the slit plane. -/
theorem div_mem_slitPlane_of_re_neg {z₁ z₂ : ℂ} (h₁ : z₁.re < 0) (h₂ : z₂.re < 0) :
    z₂ / z₁ ∈ slitPlane :=
  div_mem_slitPlane_of_re_conj_mul_pos (a := -1)
    (by simpa using neg_pos.mpr h₁) (by simpa using neg_pos.mpr h₂)

/-- Two points in the upper half-plane have their ratio in the slit plane. -/
theorem div_mem_slitPlane_of_im_pos {z₁ z₂ : ℂ} (h₁ : 0 < z₁.im) (h₂ : 0 < z₂.im) :
    z₂ / z₁ ∈ slitPlane :=
  div_mem_slitPlane_of_re_conj_mul_pos (a := Complex.I)
    (by simpa [Complex.mul_re]) (by simpa [Complex.mul_re])

/-- Two points in the lower half-plane have their ratio in the slit plane. -/
theorem div_mem_slitPlane_of_im_neg {z₁ z₂ : ℂ} (h₁ : z₁.im < 0) (h₂ : z₂.im < 0) :
    z₂ / z₁ ∈ slitPlane :=
  div_mem_slitPlane_of_re_conj_mul_pos (a := -Complex.I)
    (by simpa [Complex.mul_re] using neg_pos.mpr h₁)
    (by simpa [Complex.mul_re] using neg_pos.mpr h₂)

end TauCeti

end
