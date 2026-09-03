/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Elementary real charts for one-dimensional changes of variables

This file records reusable calculus facts about elementary real charts that recur in density and
special-function computations.

## Main results

* `TauCeti.div_one_sub_strictMonoOn`, `TauCeti.injOn_div_one_sub_Ioo`,
  `TauCeti.image_div_one_sub_Ioo`, and `TauCeti.hasDerivAt_div_one_sub` describe the chart
  `u ↦ u / (1 - u)` on intervals below `1`;
* `TauCeti.image_sq_div_const_Ioi`, `TauCeti.injOn_sq_div_const_Ioi`, and
  `TauCeti.hasDerivAt_sq_div_const` describe the square chart `z ↦ z ^ 2 / ν` on positive
  half-lines.
-/

public section

namespace TauCeti

open Set

variable {ν : ℝ}

/-! ### The chart `u ↦ u / (1 - u)` -/

/-- The chart `u ↦ u / (1 - u)` is strictly increasing on `(-∞, 1)`. -/
lemma div_one_sub_strictMonoOn : StrictMonoOn (fun u : ℝ => u / (1 - u)) (Set.Iio 1) := by
  intro u hui v hvi huv
  have hu1 : u < 1 := hui
  have hv1 : v < 1 := hvi
  have h1 : 0 < 1 - u := by linarith
  have h2 : 0 < 1 - v := by linarith
  have h3 : u * (1 - v) < v * (1 - u) := by nlinarith
  have hden : 0 < (1 - u) * (1 - v) := by positivity
  calc u / (1 - u)
       = (u * (1 - v)) / ((1 - u) * (1 - v)) := by field_simp [h1.ne', h2.ne']
    _ < (v * (1 - u)) / ((1 - u) * (1 - v)) := by
      exact div_lt_div_of_pos_right h3 hden
    _ = v / (1 - v) := by field_simp [h1.ne', h2.ne']

/-- The chart `u ↦ u / (1 - u)` is injective on `(u₀, 1)`. -/
lemma injOn_div_one_sub_Ioo {u0 : ℝ} :
    InjOn (fun u : ℝ => u / (1 - u)) (Ioo u0 1) :=
  div_one_sub_strictMonoOn.injOn.mono fun _ hx => (Set.mem_Ioo.mp hx).2

/-- The chart `u ↦ u / (1 - u)` carries `(u₀, 1)` onto `(u₀ / (1 - u₀), ∞)` for `u₀ < 1`. -/
lemma image_div_one_sub_Ioo {u0 : ℝ} (hu1 : u0 < 1) :
    (fun u : ℝ => u / (1 - u)) '' Ioo u0 1 = Ioi (u0 / (1 - u0)) := by
  ext w
  simp only [mem_image, mem_Ioo, mem_Ioi]
  constructor
  · rintro ⟨u, ⟨huu0, hu1'⟩, rfl⟩
    have h_a : u0 ∈ Set.Iio 1 := Set.mem_Iio.mpr hu1
    have h_b : u ∈ Set.Iio 1 := Set.mem_Iio.mpr hu1'
    exact div_one_sub_strictMonoOn h_a h_b huu0
  · intro hw
    have hlow : -1 < u0 / (1 - u0) := by
      rw [lt_div_iff₀ (by linarith : 0 < 1 - u0)]
      linarith
    have h1 : 0 < 1 + w := by linarith
    let u : ℝ := w / (1 + w)
    have hden : 1 - u = (1 + w)⁻¹ := by
      simp only [u]; field_simp [h1.ne']; ring
    have hu_eq : u / (1 - u) = w := by
      rw [hden]; simp only [u]; field_simp [h1.ne']
    have hu_lt_one : u < 1 := by
      simp only [u]; rw [div_lt_one h1]; linarith
    have hu0_lt : u0 < u := by
      have h_a : u0 ∈ Set.Iio 1 := Set.mem_Iio.mpr hu1
      have h_b : u ∈ Set.Iio 1 := Set.mem_Iio.mpr hu_lt_one
      have h : u0 / (1 - u0) < u / (1 - u) := by rw [hu_eq]; exact hw
      exact (div_one_sub_strictMonoOn.lt_iff_lt h_a h_b).mp h
    exact ⟨u, ⟨hu0_lt, hu_lt_one⟩, hu_eq⟩

/-- The derivative of the chart `u ↦ u / (1 - u)` is `(1 - u) ^ (-2)`. -/
lemma hasDerivAt_div_one_sub {u : ℝ} (hu : u ≠ 1) :
    HasDerivAt (fun t : ℝ => t / (1 - t)) ((1 - u) ^ 2)⁻¹ u := by
  have h : (1 : ℝ) - u ≠ 0 := sub_ne_zero_of_ne (Ne.symm hu)
  have hd : HasDerivAt (fun t : ℝ => 1 - t) (-1) u := by
    simpa using (hasDerivAt_id u).const_sub (1 : ℝ)
  refine ((hasDerivAt_id' (x := u)).div hd h).congr_deriv ?_
  have hnum : (1 : ℝ) * (1 - u) - u * -1 = 1 := by ring
  rw [hnum, one_div]

/-! ### The square chart on the positive half-line -/

/-- The square chart `z ↦ z ^ 2 / ν` carries `(y, ∞)` onto `(y ^ 2 / ν, ∞)` for
`0 ≤ y` and `0 < ν`. -/
lemma image_sq_div_const_Ioi (hν : 0 < ν) {y : ℝ} (hy : 0 ≤ y) :
    (fun z : ℝ => z ^ 2 / ν) '' Ioi y = Ioi (y ^ 2 / ν) := by
  ext w
  simp only [mem_image, mem_Ioi]
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hz0 : 0 < z := hy.trans_lt hz
    have hsq : y ^ 2 < z ^ 2 := by gcongr
    exact div_lt_div_of_pos_right hsq hν
  · intro hw
    have h0 : 0 ≤ y ^ 2 / ν := by positivity
    have hw0 : 0 < w := h0.trans_lt hw
    have hνw : 0 < ν * w := mul_pos hν hw0
    have hsqrt_y : y < Real.sqrt (ν * w) := by
      have h : y ^ 2 < ν * w := by
        have h' : y ^ 2 / ν < w := hw
        calc y ^ 2 = ν * (y ^ 2 / ν) := by field_simp [hν.ne']
             _ < ν * w := mul_lt_mul_of_pos_left h' hν
      have h2 : y ^ 2 < (Real.sqrt (ν * w)) ^ 2 := by
        rw [Real.sq_sqrt (by linarith)]; exact h
      nlinarith [Real.sqrt_nonneg (ν * w)]
    refine ⟨Real.sqrt (ν * w), hsqrt_y, ?_⟩
    rw [Real.sq_sqrt (by linarith)]; field_simp [hν.ne']

/-- The chart `z ↦ z ^ 2 / ν` is injective on the positive half-line for nonzero `ν`. -/
lemma injOn_sq_div_const_Ioi (hν : ν ≠ 0) :
    InjOn (fun z : ℝ => z ^ 2 / ν) (Ioi (0 : ℝ)) := by
  intro z hz w hw h
  have hz0 : 0 < z := hz
  have hw0 : 0 < w := hw
  have : z ^ 2 = w ^ 2 := by
    field_simp [hν] at h
    linarith
  nlinarith

/-- The derivative of the chart `z ↦ z ^ 2 / ν`. -/
lemma hasDerivAt_sq_div_const (ν z : ℝ) :
    HasDerivAt (fun x : ℝ => x ^ 2 / ν) (2 * z / ν) z := by
  simpa using ((hasDerivAt_id z).pow 2).div_const ν

end TauCeti
