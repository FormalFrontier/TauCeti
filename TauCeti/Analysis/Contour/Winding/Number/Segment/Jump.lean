/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Winding.Number.Segment.Formula
public import TauCeti.Analysis.Contour.PiecewiseC1On
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import TauCeti.Analysis.Contour.Winding.Continuity
import TauCeti.Analysis.Contour.Winding.Integer
import TauCeti.Analysis.Contour.Winding.LocallyConstant
import TauCeti.Analysis.Contour.Winding.Number.Concat

/-!
# The winding number differs by one across a straight segment

Letting the reference point `v · (s ± h·i) + z₀` approach an interior point `v · s + z₀`
of the segment from the two sides as `h → 0⁺`, the two limits of the index integral differ
by exactly `1`.

For a *closed* piecewise-`C¹` curve one of whose pieces is a straight segment, if the rest of the
curve avoids an interior point `p` of that piece (hypothesis `hp`), the non-segment contribution is
continuous at `p`, so the winding number of the whole curve differs by exactly `1` between the two
sides of the segment near `p`: it is one larger on the side to the left of the direction of travel.

## Main results

* `TauCeti.Contour.tendsto_windingNumber_segment_add_mul_I` and
  `TauCeti.Contour.tendsto_windingNumber_segment_sub_mul_I` — one-sided limits of the winding
  number at an interior point, from the left and from the right.
* `TauCeti.Contour.tendsto_windingNumber_segment_sub` — the difference of
  the winding numbers tends to `1`.
* `TauCeti.Contour.exists_forall_windingNumber_eq_add_one_of_eqOn_segment` — **a closed curve
  differs by one across a straight piece**.

## References

* L. Ahlfors, *Complex Analysis*, Chapter 4, §2.1.
-/

public section

open Complex Filter MeasureTheory Metric Set

open scoped Topology

namespace TauCeti.Contour

variable {v z₀ : ℂ} {a b c s : ℝ}

private theorem norm_ofReal_sub_eq (hs : s ∈ Ioo a b) :
    ‖(a : ℂ) - (s : ℂ)‖ = s - a := by
  rw [← ofReal_sub, norm_real, Real.norm_eq_abs, abs_sub_comm,
    abs_of_pos (by linarith [hs.1])]

private theorem tendsto_ofReal_sub_add_mul_I (r s : ℝ) (σ : ℝ) :
    Tendsto (fun h : ℝ => (r : ℂ) - (s + (σ * h : ℝ) * I)) (𝓝[>] 0) (𝓝 ((r : ℂ) - s)) := by
  have : Tendsto (fun h : ℝ => (r : ℂ) - (s + (σ * h : ℝ) * I)) (𝓝 0)
      (𝓝 ((r : ℂ) - (s + (σ * (0 : ℝ) : ℝ) * I))) := by
    apply Continuous.tendsto
    fun_prop
  simpa using this.mono_left nhdsWithin_le_nhds

private theorem tendsto_log_ofReal_sub_add_mul_I (hs : s < b) (σ : ℝ) :
    Tendsto (fun h : ℝ => log ((b : ℂ) - (s + (σ * h : ℝ) * I))) (𝓝[>] 0)
      (𝓝 (log ((b : ℂ) - s))) := by
  have hmem : (b : ℂ) - s ∈ slitPlane :=
    mem_slitPlane_iff.mpr (Or.inl (by simp only [sub_re, ofReal_re]; linarith))
  exact (continuousAt_clog hmem).tendsto.comp (tendsto_ofReal_sub_add_mul_I b s σ)

/-- **The winding number of a segment about a point approaching it from the left.** For
`s ∈ (a, b)` and `h → 0⁺`, the winding number about `v (s + h i) + z₀` — the side to the left of
the direction of travel — tends to `(2πi)⁻¹ (log (b - s) - (Real.log (s - a) - πi))`. -/
theorem tendsto_windingNumber_segment_add_mul_I (hv : v ≠ 0) (hs : s ∈ Ioo a b) :
    Tendsto (fun h : ℝ =>
        windingNumber (fun t : ℝ => v * (t : ℂ) + z₀) a b (v * (s + h * I) + z₀))
      (𝓝[>] 0)
      (𝓝 ((2 * (Real.pi : ℂ) * I)⁻¹ *
        (log ((b : ℂ) - s) - (Real.log (s - a) - Real.pi * I)))) := by
  have h_eq : ∀ᶠ h : ℝ in 𝓝[>] 0,
      (2 * (Real.pi : ℂ) * I)⁻¹ *
          (log ((b : ℂ) - (s + ((1 : ℝ) * h : ℝ) * I)) -
            log ((a : ℂ) - (s + ((1 : ℝ) * h : ℝ) * I)))
        = windingNumber (fun t : ℝ => v * (t : ℂ) + z₀) a b (v * (s + h * I) + z₀) := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    have him : ((s : ℂ) + h * I).im ≠ 0 := by simpa using hh.ne'
    rw [windingNumber_segment_of_im_ne_zero hv him]
    simp only [one_mul]
  refine Tendsto.congr' h_eq
    (Tendsto.const_mul _ (Tendsto.sub (tendsto_log_ofReal_sub_add_mul_I hs.2 1) ?_))
  have h1 : Tendsto (fun h : ℝ => (a : ℂ) - (s + ((1 : ℝ) * h : ℝ) * I)) (𝓝[>] 0)
      (𝓝[{z : ℂ | z.im < 0}] ((a : ℂ) - s)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨tendsto_ofReal_sub_add_mul_I a s 1, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with h hh
    simpa using hh
  have h2 := (tendsto_log_nhdsWithin_im_neg_of_re_neg_of_im_zero (z := (a : ℂ) - s)
    (by simp only [sub_re, ofReal_re]; linarith [hs.1]) (by simp)).comp h1
  simpa [Function.comp_def, norm_ofReal_sub_eq hs] using h2

/-- **The winding number of a segment about a point approaching it from the right.** For
`s ∈ (a, b)` and `h → 0⁺`, the winding number about `v (s - h i) + z₀` — the side to the right of
the direction of travel — tends to `(2πi)⁻¹ (log (b - s) - (Real.log (s - a) + πi))`. -/
theorem tendsto_windingNumber_segment_sub_mul_I (hv : v ≠ 0) (hs : s ∈ Ioo a b) :
    Tendsto (fun h : ℝ =>
        windingNumber (fun t : ℝ => v * (t : ℂ) + z₀) a b (v * (s - h * I) + z₀))
      (𝓝[>] 0)
      (𝓝 ((2 * (Real.pi : ℂ) * I)⁻¹ *
        (log ((b : ℂ) - s) - (Real.log (s - a) + Real.pi * I)))) := by
  have h_eq : ∀ᶠ h : ℝ in 𝓝[>] 0,
      (2 * (Real.pi : ℂ) * I)⁻¹ *
          (log ((b : ℂ) - (s + ((-1 : ℝ) * h : ℝ) * I)) -
            log ((a : ℂ) - (s + ((-1 : ℝ) * h : ℝ) * I)))
        = windingNumber (fun t : ℝ => v * (t : ℂ) + z₀) a b (v * (s - h * I) + z₀) := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    have him : ((s : ℂ) - h * I).im ≠ 0 := by simpa using hh.ne'
    rw [windingNumber_segment_of_im_ne_zero hv him]
    simp only [neg_mul, one_mul, sub_eq_add_neg, ofReal_neg]
  refine Tendsto.congr' h_eq
    (Tendsto.const_mul _ (Tendsto.sub (tendsto_log_ofReal_sub_add_mul_I hs.2 (-1)) ?_))
  have h1 : Tendsto (fun h : ℝ => (a : ℂ) - (s + ((-1 : ℝ) * h : ℝ) * I)) (𝓝[>] 0)
      (𝓝[{z : ℂ | 0 ≤ z.im}] ((a : ℂ) - s)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨tendsto_ofReal_sub_add_mul_I a s (-1), ?_⟩
    filter_upwards [self_mem_nhdsWithin] with h hh
    simpa using hh.le
  have h2 := (tendsto_log_nhdsWithin_im_nonneg_of_re_neg_of_im_zero (z := (a : ℂ) - s)
    (by simp only [sub_re, ofReal_re]; linarith [hs.1]) (by simp)).comp h1
  simpa [Function.comp_def, norm_ofReal_sub_eq hs] using h2

/-- **The jump of the winding number across a straight segment is `1`.** As `h → 0⁺`, the winding
numbers about the two points `v (s ± h i) + z₀` on either side of the interior point `v s + z₀`
differ by a quantity tending to `1`: the left side minus the right side. -/
theorem tendsto_windingNumber_segment_sub (hv : v ≠ 0) (hs : s ∈ Ioo a b) :
    Tendsto (fun h : ℝ =>
        windingNumber (fun t : ℝ => v * (t : ℂ) + z₀) a b (v * (s + h * I) + z₀) -
          windingNumber (fun t : ℝ => v * (t : ℂ) + z₀) a b (v * (s - h * I) + z₀))
      (𝓝[>] 0) (𝓝 1) := by
  have h := (tendsto_windingNumber_segment_add_mul_I (z₀ := z₀) hv hs).sub
    (tendsto_windingNumber_segment_sub_mul_I (z₀ := z₀) hv hs)
  convert h using 2
  have hπ : (2 * (Real.pi : ℂ) * I) ≠ 0 := by
    simp [Real.pi_ne_zero, I_ne_zero]
  field_simp
  ring

/-! ## The jump of a closed curve across a straight piece -/

private theorem convex_ball_inter_halfSpace_gt (p v : ℂ) (r σ : ℝ) :
    Convex ℝ (ball p r ∩ {w : ℂ | 0 < σ * ((w - p) / v).im}) := by
  have hlin : IsLinearMap ℝ fun w : ℂ => σ * (w / v).im :=
    { map_add := by intro x y; simp only [add_div, Complex.add_im]; ring
      map_smul := by intro s x; simp [Complex.real_smul, Complex.mul_im, mul_div_assoc]; ring }
  have heq : {w : ℂ | 0 < σ * ((w - p) / v).im}
      = (fun x => -p + x) ⁻¹' {w | 0 < σ * (w / v).im} := by
    ext w; simp only [mem_ofPred_eq, neg_add_eq_sub, mem_preimage]
  rw [heq]
  exact (convex_ball p r).inter ((convex_halfSpace_gt hlin _).translate_preimage_right _)

/-- **A closed curve jumps by one across a straight piece.** Let `Γ` be a closed piecewise-`C¹`
curve on `[a, c]` which on `[a, b]` is the straight segment `t ↦ v · t + z₀`, and let
`p = v · s + z₀` with `s ∈ (a, b)` be a point of that segment not visited by the rest of the curve.
Then on a small disc about `p` the winding number takes one value on the side to the left of the
direction of travel and the value one less on the side to the right. -/
theorem exists_forall_windingNumber_eq_add_one_of_eqOn_segment {Γ : ℝ → ℂ}
    (hΓ : IsPiecewiseC1On Γ a c) (hclosed : Γ a = Γ c) (hbc : b ≤ c)
    (hseg : EqOn Γ (fun t : ℝ => v * (t : ℂ) + z₀) (Icc a b)) (hv : v ≠ 0) (hs : s ∈ Ioo a b)
    (hp : v * s + z₀ ∉ Γ '' Icc b c) :
    ∃ r > 0, ∀ w₁ ∈ ball (v * s + z₀) r, ∀ w₂ ∈ ball (v * s + z₀) r,
      0 < ((w₁ - (v * s + z₀)) / v).im → ((w₂ - (v * s + z₀)) / v).im < 0 →
        windingNumber Γ a c w₁ = windingNumber Γ a c w₂ + 1 := by
  set p : ℂ := v * s + z₀ with hp_def
  have hab : a < b := hs.1.trans hs.2
  have hac : a ≤ c := hab.le.trans hbc
  -- Stage 1: half-disc constancy — winding number is constant on each side near p
  have hΓcont : ContinuousOn Γ (uIcc a c) := hΓ.continuousOn
  have hIcc_ab : Icc a b ⊆ uIcc a c := by
    rw [uIcc_of_le hac]; exact Icc_subset_Icc le_rfl hbc
  have hIcc_bc : Icc b c ⊆ uIcc a c := by
    rw [uIcc_of_le hac]; exact Icc_subset_Icc hab.le le_rfl
  have hK : IsCompact (Γ '' Icc b c) := isCompact_Icc.image_of_continuousOn (hΓcont.mono hIcc_bc)
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hK.isClosed.isOpen_compl p hp
  refine ⟨r, hr, ?_⟩
  have h_curve : Γ '' uIcc a c ⊆ (fun t : ℝ => v * (t : ℂ) + z₀) '' Icc a b ∪ Γ '' Icc b c := by
    rw [uIcc_of_le hac]
    rintro _ ⟨t, ht, rfl⟩
    rcases le_or_gt t b with htb | htb
    · exact Or.inl ⟨t, ⟨ht.1, htb⟩, (hseg ⟨ht.1, htb⟩).symm⟩
    · exact Or.inr ⟨t, ⟨htb.le, ht.2⟩, rfl⟩
  have h_off : ∀ w ∈ ball p r, ((w - p) / v).im ≠ 0 → w ∉ Γ '' uIcc a c := by
    intro w hw him hmem
    rcases h_curve hmem with ⟨t, _, rfl⟩ | hmem'
    · apply him
      have : (v * (t : ℂ) + z₀ - p) / v = ((t : ℂ) - s) := by
        rw [hp_def]; field_simp; ring
      rw [this]; simp only [sub_im, ofReal_im, sub_self]
    · exact hball hw hmem'
  have h_const : ∀ σ : ℝ, ∀ w₁ ∈ ball p r, ∀ w₂ ∈ ball p r,
      0 < σ * ((w₁ - p) / v).im → 0 < σ * ((w₂ - p) / v).im →
        windingNumber Γ a c w₁ = windingNumber Γ a c w₂ := by
    intro σ w₁ hw₁ w₂ hw₂ h₁ h₂
    have hDsub : ball p r ∩ {w : ℂ | 0 < σ * ((w - p) / v).im} ⊆ (Γ '' uIcc a c)ᶜ := by
      intro w hw
      have hw2 : 0 < σ * ((w - p) / v).im := hw.2
      refine h_off w hw.1 fun h0 => ?_
      rw [h0, mul_zero] at hw2
      exact lt_irrefl _ hw2
    exact hΓ.windingNumber_eq_of_mem_connectedComponentIn hclosed
      ((convex_ball_inter_halfSpace_gt p v r σ).isPreconnected.subset_connectedComponentIn
        ⟨hw₂, h₂⟩ hDsub ⟨hw₁, h₁⟩)
  -- Stage 2: coordinate identities for test points v·(s ± h·i) + z₀
  have h_im_add : ∀ h : ℝ, ((v * (s + h * I) + z₀ - p) / v).im = h := by
    intro h
    have : (v * (s + h * I) + z₀ - p) / v = h * I := by
      rw [hp_def]; field_simp; ring
    rw [this]; simp only [mul_im, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one, add_zero]
  have h_im_sub : ∀ h : ℝ, ((v * (s - h * I) + z₀ - p) / v).im = -h := by
    intro h
    have key : (v * (s - h * I) + z₀ - p) / v = -(h * I) := by
      rw [hp_def]; field_simp; ring
    simp only [key, neg_im, mul_im, ofReal_re, I_re, mul_zero,
      ofReal_im, I_im, mul_one, add_zero]
  have h_dist_add : ∀ h : ℝ, dist (v * (s + h * I) + z₀) p = ‖v‖ * |h| := by
    intro h
    rw [dist_eq_norm, hp_def]
    have : v * (s + h * I) + z₀ - (v * s + z₀) = v * (h * I) := by ring
    rw [this, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs]
  have h_dist_sub : ∀ h : ℝ, dist (v * (s - h * I) + z₀) p = ‖v‖ * |h| := by
    intro h
    rw [dist_eq_norm, hp_def]
    have : v * (s - h * I) + z₀ - (v * s + z₀) = -(v * (h * I)) := by ring
    rw [this, norm_neg, norm_mul, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs]
  have h_small : ∀ᶠ h : ℝ in 𝓝[>] 0, 0 < h ∧ ‖v‖ * |h| < r := by
    have hlt : ∀ᶠ h : ℝ in 𝓝 (0 : ℝ), ‖v‖ * |h| < r := by
      have : Continuous fun h : ℝ => ‖v‖ * |h| := by fun_prop
      exact this.continuousAt.eventually_lt continuousAt_const (by simpa using hr)
    exact (eventually_mem_nhdsWithin.and (hlt.filter_mono nhdsWithin_le_nhds)).mono fun h hh =>
      ⟨hh.1, hh.2⟩
  -- Stage 3: decompose Γ = segment [a,b] ∪ rest [b,c]; rest is continuous at p
  have h_avoid_bc : ∀ t ∈ uIcc b c, Γ t ≠ p := by
    intro t ht heq
    exact hp ⟨t, by rwa [uIcc_of_le hbc] at ht, heq⟩
  have hΓbc : IsPiecewiseC1On Γ b c := hΓ.mono (by rw [uIcc_of_le hbc]; exact hIcc_bc)
  have hΓab : IsPiecewiseC1On Γ a b := hΓ.mono (by rw [uIcc_of_le hab.le]; exact hIcc_ab)
  have h_contAt : ContinuousAt (fun w => windingNumber Γ b c w) p :=
    continuousAt_windingNumber_of_avoidance hΓbc.continuousOn h_avoid_bc
      (intervalIntegrable_inv_sub_mul_deriv hΓbc.continuousOn h_avoid_bc
        hΓbc.intervalIntegrable_deriv)
  have h_decomp : ∀ w ∉ Γ '' uIcc a c,
      windingNumber Γ a c w
        = windingNumber (fun t : ℝ => v * (t : ℂ) + z₀) a b w + windingNumber Γ b c w := by
    intro w hw
    have h_avoid_ab : ∀ t ∈ uIcc a b, Γ t ≠ w := fun t ht heq =>
      hw ⟨t, by rw [uIcc_of_le hab.le] at ht; exact hIcc_ab ht, heq⟩
    have h_avoid_bc' : ∀ t ∈ uIcc b c, Γ t ≠ w := fun t ht heq =>
      hw ⟨t, by rw [uIcc_of_le hbc] at ht; exact hIcc_bc ht, heq⟩
    rw [windingNumber_concat
      (cauchyPVExistsAt_of_avoidance hΓab.continuousOn h_avoid_ab
        (intervalIntegrable_inv_sub_mul_deriv hΓab.continuousOn h_avoid_ab
          hΓab.intervalIntegrable_deriv))
      (cauchyPVExistsAt_of_avoidance hΓbc.continuousOn h_avoid_bc'
        (intervalIntegrable_inv_sub_mul_deriv hΓbc.continuousOn h_avoid_bc'
          hΓbc.intervalIntegrable_deriv))]
    congr 1
    refine windingNumber_congr_curve fun t ht => hseg ?_
    rw [uIoo_of_le hab.le] at ht
    exact Ioo_subset_Icc_self ht
  have h_tend_add : Tendsto (fun h : ℝ => v * (s + h * I) + z₀) (𝓝[>] 0) (𝓝 p) := by
    have : Tendsto (fun h : ℝ => v * (s + h * I) + z₀) (𝓝 0) (𝓝 (v * (s + (0 : ℝ) * I) + z₀)) := by
      apply Continuous.tendsto; fun_prop
    simpa [hp_def] using this.mono_left nhdsWithin_le_nhds
  have h_tend_sub : Tendsto (fun h : ℝ => v * (s - h * I) + z₀) (𝓝[>] 0) (𝓝 p) := by
    have : Tendsto (fun h : ℝ => v * (s - h * I) + z₀) (𝓝 0) (𝓝 (v * (s - (0 : ℝ) * I) + z₀)) := by
      apply Continuous.tendsto; fun_prop
    simpa [hp_def] using this.mono_left nhdsWithin_le_nhds
  have h_rest : Tendsto (fun h : ℝ =>
      windingNumber Γ b c (v * (s + h * I) + z₀) - windingNumber Γ b c (v * (s - h * I) + z₀))
      (𝓝[>] 0) (𝓝 0) := by
    have := (h_contAt.tendsto.comp h_tend_add).sub (h_contAt.tendsto.comp h_tend_sub)
    simpa [Function.comp_def] using this
  have h_off_add : ∀ h : ℝ, 0 < h → ‖v‖ * |h| < r → v * (s + h * I) + z₀ ∉ Γ '' uIcc a c := by
    intro h hh hlt
    refine h_off _ (by rw [Metric.mem_ball, h_dist_add]; exact hlt) ?_
    rw [h_im_add]; exact hh.ne'
  have h_off_sub : ∀ h : ℝ, 0 < h → ‖v‖ * |h| < r → v * (s - h * I) + z₀ ∉ Γ '' uIcc a c := by
    intro h hh hlt
    refine h_off _ (by rw [Metric.mem_ball, h_dist_sub]; exact hlt) ?_
    rw [h_im_sub]; exact (neg_lt_zero.mpr hh).ne
  -- Stage 4: the segment part tends to 1, the rest tends to 0, so the total tends to 1
  have h_tend : Tendsto (fun h : ℝ =>
      windingNumber Γ a c (v * (s + h * I) + z₀) - windingNumber Γ a c (v * (s - h * I) + z₀))
      (𝓝[>] 0) (𝓝 1) := by
    have h_eq : (fun h : ℝ =>
        (windingNumber (fun t : ℝ => v * (t : ℂ) + z₀) a b (v * (s + h * I) + z₀) -
          windingNumber (fun t : ℝ => v * (t : ℂ) + z₀) a b (v * (s - h * I) + z₀)) +
        (windingNumber Γ b c (v * (s + h * I) + z₀) - windingNumber Γ b c (v * (s - h * I) + z₀)))
        =ᶠ[𝓝[>] 0] fun h : ℝ =>
          windingNumber Γ a c (v * (s + h * I) + z₀) -
            windingNumber Γ a c (v * (s - h * I) + z₀) := by
      filter_upwards [h_small] with h hh
      rw [h_decomp _ (h_off_add h hh.1 hh.2), h_decomp _ (h_off_sub h hh.1 hh.2)]
      ring
    refine Tendsto.congr' h_eq ?_
    simpa using
      (tendsto_windingNumber_segment_sub (z₀ := z₀) hv hs).add h_rest
  -- Stage 5: integrality forces the limit to be exactly 1, propagate to the half-discs
  have h_near : ∀ᶠ h : ℝ in 𝓝[>] 0,
      dist (windingNumber Γ a c (v * (s + h * I) + z₀) - windingNumber Γ a c (v * (s - h * I) + z₀))
        (1 : ℂ) < 1 / 2 :=
    h_tend (Metric.ball_mem_nhds (1 : ℂ) one_half_pos)
  obtain ⟨h, hh_near, hh_pos, hh_lt⟩ := (h_near.and h_small).exists
  have hmem_add : v * (s + h * I) + z₀ ∈ ball p r := by
    rw [Metric.mem_ball, h_dist_add]; exact hh_lt
  have hmem_sub : v * (s - h * I) + z₀ ∈ ball p r := by
    rw [Metric.mem_ball, h_dist_sub]; exact hh_lt
  obtain ⟨m, hm⟩ := hΓ.exists_int_windingNumber hclosed fun t ht heq =>
    h_off_add h hh_pos hh_lt ⟨t, ht, heq⟩
  obtain ⟨n, hn⟩ := hΓ.exists_int_windingNumber hclosed fun t ht heq =>
    h_off_sub h hh_pos hh_lt ⟨t, ht, heq⟩
  have hcast : ((n + 1 : ℤ) : ℂ) = (n : ℂ) + 1 := by push_cast; ring
  have hmn : m = n + 1 :=
    eq_of_dist_intCast_lt_one (n := n + 1) (by
      rw [hm, hn] at hh_near
      rw [hcast]
      have : dist ((m : ℂ) - (n : ℂ)) 1 = dist (m : ℂ) ((n : ℂ) + 1) := by
        simp only [dist_eq_norm]; ring_nf
      linarith)
  have h_jump : windingNumber Γ a c (v * (s + h * I) + z₀)
      = windingNumber Γ a c (v * (s - h * I) + z₀) + 1 := by
    rw [hm, hn, hmn]; push_cast; ring
  intro w₁ hw₁ w₂ hw₂ h₁ h₂
  have e₁ : windingNumber Γ a c w₁ = windingNumber Γ a c (v * (s + h * I) + z₀) :=
    h_const 1 w₁ hw₁ _ hmem_add (by simpa using h₁) (by rw [h_im_add]; simpa using hh_pos)
  have e₂ : windingNumber Γ a c w₂ = windingNumber Γ a c (v * (s - h * I) + z₀) :=
    h_const (-1) w₂ hw₂ _ hmem_sub (by simpa using h₂) (by rw [h_im_sub]; simpa using hh_pos)
  rw [e₁, e₂, h_jump]

end TauCeti.Contour
