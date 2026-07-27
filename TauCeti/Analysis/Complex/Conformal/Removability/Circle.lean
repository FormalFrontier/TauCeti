/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Complex.Conformal.Removability.Basic

/-!
# Painlevé removability across a circle

A circle is a removable set for continuous holomorphic functions: if `F` is continuous on an open
set `Ω ⊆ ℂ` and holomorphic on `Ω` off a positive-radius circle, then `F` is holomorphic on all of
`Ω`.

The proof reduces to Painlevé removability of the real axis from
`Conformal/Removability/Basic.lean`. Two fractional-linear charts cover the circle, with each
chart carrying the real axis to the circle and omitting one point.
-/

public section

namespace TauCeti

open Complex Metric Set

/-- A fractional-linear parametrisation of the circle centred at `c` through `c + a`.
It maps the real axis to that circle and omits `c + a`. -/
private noncomputable def circleLineMap (c a w : ℂ) : ℂ :=
  c + a * ((w - I) / (w + I))

/-- The inverse coordinate to `circleLineMap`, away from its omitted point `c + a`. -/
private noncomputable def circleLineMapInv (c a z : ℂ) : ℂ :=
  I * ((a + (z - c)) / (a - (z - c)))

private lemma differentiableOn_circleLineMap {c a : ℂ} {S : Set ℂ}
    (hI : -I ∉ S) :
    DifferentiableOn ℂ (circleLineMap c a) S := by
  intro w hw
  apply DifferentiableAt.differentiableWithinAt
  apply DifferentiableAt.add
  · fun_prop
  apply DifferentiableAt.mul
  · fun_prop
  apply DifferentiableAt.div
  · fun_prop
  · fun_prop
  · intro h
    apply hI
    have : w = -I := by linear_combination h
    exact this ▸ hw

private lemma differentiableOn_circleLineMapInv {c a : ℂ} {S : Set ℂ}
    (ha : c + a ∉ S) :
    DifferentiableOn ℂ (circleLineMapInv c a) S := by
  intro z hz
  apply DifferentiableAt.differentiableWithinAt
  apply DifferentiableAt.mul
  · fun_prop
  apply DifferentiableAt.div
  · fun_prop
  · fun_prop
  · intro h
    apply ha
    have h' : a = z - c := sub_eq_zero.mp h
    have : z = c + a := by
      rw [h']
      ring
    exact this ▸ hz

private lemma circleLineMap_circleLineMapInv {c a z : ℂ}
    (ha : a ≠ 0) (hz : z ≠ c + a) :
    circleLineMap c a (circleLineMapInv c a z) = z := by
  have hden : a - (z - c) ≠ 0 := by
    rw [sub_ne_zero]
    intro h
    apply hz
    rw [h]
    ring
  have hsum : I * ((a + (z - c)) / (a - (z - c))) + I ≠ 0 := by
    intro h
    have hzero : (2 * I) * a = 0 := by
      field_simp [hden] at h
      linear_combination h
    exact ha ((mul_eq_zero.mp hzero).resolve_left (mul_ne_zero (by norm_num) I_ne_zero))
  rw [circleLineMap, circleLineMapInv]
  field_simp [hden, hsum]
  field_simp [ha]
  ring

private lemma circleLineMap_ne_neg_I {c a z : ℂ} (ha : a ≠ 0)
    (hz : z ≠ c + a) :
    circleLineMapInv c a z ≠ -I := by
  have hden : a - (z - c) ≠ 0 := by
    rw [sub_ne_zero]
    intro h
    apply hz
    rw [h]
    ring
  intro h
  have hzero : 2 * a = 0 := by
    rw [circleLineMapInv] at h
    field_simp [hden] at h
    linear_combination h
  exact ha ((mul_eq_zero.mp hzero).resolve_left (by norm_num))

private lemma circleLineMap_mem_sphere_iff {c a w : ℂ}
    (ha : a ≠ 0) (hw : w ≠ -I) :
    circleLineMap c a w ∈ sphere c ‖a‖ ↔ w.im = 0 := by
  rw [mem_sphere, circleLineMap, dist_eq, add_sub_cancel_left, norm_mul,
    norm_div]
  have hden : ‖w + I‖ ≠ 0 := norm_ne_zero_iff.mpr (by
    intro h
    apply hw
    linear_combination h)
  have hnorm : ‖w - I‖ = ‖w + I‖ ↔ w.im = 0 := by
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), ← Complex.normSq_eq_norm_sq,
      ← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply, sub_re, I_re, sub_zero, sub_im, I_im, add_re,
      add_zero, add_im]
    constructor
    · intro h
      nlinarith
    · intro h
      rw [h]
      ring
  constructor
  · intro h
    have hquot : ‖w - I‖ / ‖w + I‖ = 1 :=
      mul_left_cancel₀ (norm_ne_zero_iff.mpr ha) (by simpa using h)
    exact hnorm.mp (div_eq_one_iff_eq hden |>.mp hquot)
  · intro h
    have hquot : ‖w - I‖ / ‖w + I‖ = 1 :=
      div_eq_one_iff_eq hden |>.mpr (hnorm.mpr h)
    rw [hquot, mul_one]

private theorem differentiableOn_of_continuousOn_of_differentiableOn_diff_sphere_omit
    {Ω : Set ℂ} {F : ℂ → ℂ} {c a : ℂ} (ha : a ≠ 0)
    (hΩ : IsOpen Ω) (hcont : ContinuousOn F Ω)
    (hdiff : DifferentiableOn ℂ F (Ω \ sphere c ‖a‖)) :
    DifferentiableOn ℂ F (Ω \ {c + a}) := by
  let φ := circleLineMap c a
  let ψ := circleLineMapInv c a
  let U := {-I}ᶜ ∩ φ ⁻¹' Ω
  have hV : IsOpen ({-I}ᶜ : Set ℂ) := isClosed_singleton.isOpen_compl
  have hφV : DifferentiableOn ℂ φ ({-I}ᶜ : Set ℂ) :=
    differentiableOn_circleLineMap fun h => h (by simp)
  have hφ : DifferentiableOn ℂ φ U := hφV.mono inter_subset_left
  have hU : IsOpen U :=
    hφV.continuousOn.isOpen_inter_preimage hV hΩ
  have hG : DifferentiableOn ℂ (F ∘ φ) U := by
    refine differentiableOn_of_continuousOn_of_differentiableOn_im_ne_zero hU
      (hcont.comp hφ.continuousOn fun w hw => hw.2) ?_
    refine hdiff.comp (hφ.mono inter_subset_left) fun w hw => ⟨hw.1.2, ?_⟩
    rw [circleLineMap_mem_sphere_iff ha (fun h => by
      rw [h] at hw
      exact hw.1.1 (by simp))]
    exact hw.2
  have hψ : DifferentiableOn ℂ ψ (Ω \ {c + a}) :=
    differentiableOn_circleLineMapInv fun h => h.2 (by simp)
  refine (hG.comp hψ fun z hz => ?_).congr fun z hz => ?_
  · refine ⟨?_, ?_⟩
    · simpa using circleLineMap_ne_neg_I ha (by simpa using hz.2)
    · -- Expose the two local chart abbreviations so the inverse law rewrites the goal.
      change φ (ψ z) ∈ Ω
      dsimp only [φ, ψ]
      rw [circleLineMap_circleLineMapInv ha (by simpa using hz.2)]
      exact hz.1
  · -- The same chart abbreviations hide the pointwise equality used by `DifferentiableOn.congr`.
    change F z = F (φ (ψ z))
    dsimp only [φ, ψ]
    rw [circleLineMap_circleLineMapInv ha (by simpa using hz.2)]

/-- **Painlevé removability across a circle.** A function continuous on an open set `Ω ⊆ ℂ`
and holomorphic off a positive-radius circle is holomorphic throughout `Ω`. -/
theorem differentiableOn_of_continuousOn_of_differentiableOn_diff_sphere
    {Ω : Set ℂ} {F : ℂ → ℂ} {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hΩ : IsOpen Ω) (hcont : ContinuousOn F Ω)
    (hdiff : DifferentiableOn ℂ F (Ω \ sphere c r)) :
    DifferentiableOn ℂ F Ω := by
  have hr0 : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr.ne'
  have hpos :=
    differentiableOn_of_continuousOn_of_differentiableOn_diff_sphere_omit
      (c := c) (a := (r : ℂ)) hr0 hΩ hcont
        (by simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr] using hdiff)
  have hneg :=
    differentiableOn_of_continuousOn_of_differentiableOn_diff_sphere_omit
      (c := c) (a := -(r : ℂ)) (neg_ne_zero.mpr hr0) hΩ hcont
        (by simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr] using hdiff)
  have hopenPos : IsOpen (Ω \ {c + (r : ℂ)}) := hΩ.sdiff isClosed_singleton
  have hopenNeg : IsOpen (Ω \ {c + -(r : ℂ)}) := hΩ.sdiff isClosed_singleton
  intro z hz
  by_cases hzr : z = c + (r : ℂ)
  · have hzneg : z ∈ Ω \ {c + -(r : ℂ)} := by
      refine ⟨hz, ?_⟩
      simp only [mem_singleton_iff]
      rw [hzr]
      intro h
      apply hr0
      have hzero : (2 : ℂ) * (r : ℂ) = 0 := by linear_combination h
      exact (mul_eq_zero.mp hzero).resolve_left (by norm_num)
    exact (hneg z hzneg).differentiableAt (hopenNeg.mem_nhds hzneg) |>.differentiableWithinAt
  · have hzpos : z ∈ Ω \ {c + (r : ℂ)} := ⟨hz, by simpa using hzr⟩
    exact (hpos z hzpos).differentiableAt (hopenPos.mem_nhds hzpos) |>.differentiableWithinAt

end TauCeti
