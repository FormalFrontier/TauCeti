/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Contour.Winding.Integrand
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Boundedness of the real winding integrand at `C^{1,1}` crossings

`Winding/BoundedIntegrand.lean` proves the real winding integrand stays bounded near a crossing
where the curve is `C²`. This file weakens that regularity to merely `C^{1,1}`: `deriv γ`
Lipschitz on a neighborhood of the crossing, with no second derivative -- pointwise or almost
everywhere -- assumed to exist anywhere. This is a genuinely different proof technique, not a
weakening of the existing one: the `C²` proof reads the bounded limit off an explicit curvature
value at the crossing (which needs a second derivative there); this file instead bounds the
integrand directly from the quadratic remainder a Lipschitz derivative forces on the curve
itself, via the mean value inequality applied to the affine remainder on the segment from the
crossing to each nearby parameter.

## Main result

* `TauCeti.Contour.exists_isBounded_image_realWindingIntegrand_of_lipschitzOnWith_deriv` -- the
  real winding integrand is bounded on a small enough window around a crossing where `deriv γ`
  is Lipschitz and non-zero.

## References

* N. Hungerbühler and M. Wasem, *Non-integer valued winding numbers and a generalized Residue
  Theorem*, arXiv:1808.00997 (2018), Proposition 2.3.
-/

public section

noncomputable section

namespace TauCeti.Contour

open Complex Filter Set Topology

open scoped NNReal

/-- **The quadratic remainder of a Lipschitz derivative.** If `deriv γ` is `K`-Lipschitz on
`[t₀ - ε, t₀ + ε]` and `γ` is differentiable there, the affine approximation at `t₀` is off by at
most `K * (t - t₀) ^ 2`. -/
private theorem norm_sub_sub_smul_deriv_le_of_lipschitzOnWith {γ : ℝ → ℂ} {t₀ ε : ℝ} {K : ℝ≥0}
    (hε_pos : 0 < ε) (hderiv : ∀ t ∈ Icc (t₀ - ε) (t₀ + ε), HasDerivAt γ (deriv γ t) t)
    (hlip : LipschitzOnWith K (deriv γ) (Icc (t₀ - ε) (t₀ + ε)))
    {t : ℝ} (ht : t ∈ Icc (t₀ - ε) (t₀ + ε)) :
    ‖γ t - γ t₀ - (t - t₀) • deriv γ t₀‖ ≤ K * (t - t₀) ^ 2 := by
  set g : ℝ → ℂ := fun u => γ u - γ t₀ - (u - t₀) • deriv γ t₀ with hg_def
  have hg_deriv : ∀ u ∈ Icc (t₀ - ε) (t₀ + ε), HasDerivWithinAt g (deriv γ u - deriv γ t₀)
      (Icc (t₀ - ε) (t₀ + ε)) u := fun u hu => by
    have h1 : HasDerivAt (fun u => γ u - γ t₀) (deriv γ u) u := (hderiv u hu).sub_const _
    have h2 : HasDerivAt (fun u => (u - t₀) • deriv γ t₀) (deriv γ t₀) u := by
      simpa using ((hasDerivAt_id u).sub_const t₀).smul_const (deriv γ t₀)
    exact (h1.sub h2).hasDerivWithinAt
  have ht₀_mem : t₀ ∈ Icc (t₀ - ε) (t₀ + ε) := ⟨by linarith, by linarith⟩
  have hK_nonneg : (0 : ℝ) ≤ (K : ℝ) := K.coe_nonneg
  rcases le_total t₀ t with hle | hle
  · have hIcc : Icc t₀ t ⊆ Icc (t₀ - ε) (t₀ + ε) := Icc_subset_Icc (by linarith [ht.1]) ht.2
    have hbound : ∀ u ∈ Ico t₀ t, ‖deriv γ u - deriv γ t₀‖ ≤ K * (t - t₀) := fun u hu => by
      have h1 : dist (deriv γ u) (deriv γ t₀) ≤ K * dist u t₀ :=
        lipschitzOnWith_iff_dist_le_mul.mp hlip u (hIcc ⟨hu.1, hu.2.le⟩) t₀ ht₀_mem
      rw [dist_eq_norm, Real.dist_eq] at h1
      have h2 : |u - t₀| ≤ t - t₀ := by rw [abs_of_nonneg (by linarith [hu.1])]; linarith [hu.2.le]
      calc ‖deriv γ u - deriv γ t₀‖ ≤ K * |u - t₀| := h1
        _ ≤ K * (t - t₀) := by nlinarith
    have := norm_image_sub_le_of_norm_deriv_le_segment'
      (f := g) (a := t₀) (b := t) (f' := fun u => deriv γ u - deriv γ t₀)
      (fun u hu => (hg_deriv u (hIcc hu)).mono hIcc) hbound t (right_mem_Icc.mpr hle)
    have heq : g t - g t₀ = g t := by simp [hg_def]
    rw [heq] at this
    calc ‖g t‖ ≤ K * (t - t₀) * (t - t₀) := this
      _ = K * (t - t₀) ^ 2 := by ring
  · have hIcc : Icc t t₀ ⊆ Icc (t₀ - ε) (t₀ + ε) := Icc_subset_Icc ht.1 (by linarith [ht.2])
    have hbound : ∀ u ∈ Ico t t₀, ‖deriv γ u - deriv γ t₀‖ ≤ K * (t₀ - t) := fun u hu => by
      have h1 : dist (deriv γ u) (deriv γ t₀) ≤ K * dist u t₀ :=
        lipschitzOnWith_iff_dist_le_mul.mp hlip u (hIcc ⟨hu.1, hu.2.le⟩) t₀ ht₀_mem
      rw [dist_eq_norm, Real.dist_eq] at h1
      have h2 : |u - t₀| ≤ t₀ - t := by
        rw [abs_of_nonpos (by linarith [hu.2.le])]; linarith [hu.1]
      calc ‖deriv γ u - deriv γ t₀‖ ≤ K * |u - t₀| := h1
        _ ≤ K * (t₀ - t) := by nlinarith
    have := norm_image_sub_le_of_norm_deriv_le_segment'
      (f := g) (a := t) (b := t₀) (f' := fun u => deriv γ u - deriv γ t₀)
      (fun u hu => (hg_deriv u (hIcc hu)).mono hIcc) hbound t₀ (right_mem_Icc.mpr hle)
    have heq : g t₀ - g t = -g t := by simp [hg_def]
    rw [heq, norm_neg] at this
    calc ‖g t‖ ≤ K * (t₀ - t) * (t₀ - t) := this
      _ = K * (t - t₀) ^ 2 := by ring

/-- **Pointwise bound on the real winding integrand near a `C^{1,1}` crossing.** For `t` close
enough to `t₀` that `|t - t₀| * (4 * (K + 1)) ≤ ‖deriv γ t₀‖`, the real winding integrand at
`γ t - w` is bounded independent of `t`. -/
private theorem abs_realWindingIntegrand_le_of_lipschitzOnWith {γ : ℝ → ℂ} {w : ℂ} {t₀ ε : ℝ}
    {K : ℝ≥0} (hε_pos : 0 < ε) (hderiv : ∀ t ∈ Icc (t₀ - ε) (t₀ + ε), HasDerivAt γ (deriv γ t) t)
    (hlip : LipschitzOnWith K (deriv γ) (Icc (t₀ - ε) (t₀ + ε)))
    (h_eq : γ t₀ = w) (hvel : deriv γ t₀ ≠ 0) {t : ℝ} (ht : t ∈ Icc (t₀ - ε) (t₀ + ε))
    (hρ : |t - t₀| * (4 * ((K : ℝ) + 1)) ≤ ‖deriv γ t₀‖) :
    |realWindingIntegrand (γ t - w) (deriv γ t)| ≤
      4 * (2 * ‖deriv γ t₀‖ * K + K ^ 2 * ε) / ‖deriv γ t₀‖ ^ 2 := by
  set v₀ := deriv γ t₀ with hv₀_def
  have hv₀_pos : 0 < ‖v₀‖ := norm_pos_iff.mpr hvel
  have hK_nonneg : (0 : ℝ) ≤ (K : ℝ) := K.coe_nonneg
  rcases eq_or_ne t t₀ with rfl | htne
  · have hz0 : γ t - w = 0 := by rw [h_eq, sub_self]
    rw [hz0, realWindingIntegrand_def]
    simp only [inv_zero, zero_mul, Complex.zero_im, abs_zero]
    positivity
  have habs_le : |t - t₀| ≤ ε := by rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
  have habs_sq : |t - t₀| ^ 2 = (t - t₀) ^ 2 := sq_abs _
  set z : ℂ := γ t - w with hz_def
  set R : ℂ := z - ((t - t₀ : ℝ) : ℂ) * v₀ with hR_def
  have hR_bound : ‖R‖ ≤ K * (t - t₀) ^ 2 := by
    have hthis := norm_sub_sub_smul_deriv_le_of_lipschitzOnWith hε_pos hderiv hlip ht
    rw [Complex.real_smul, h_eq] at hthis
    rw [hR_def, hz_def]
    exact hthis
  set e : ℂ := deriv γ t - v₀ with he_def
  have he_bound : ‖e‖ ≤ K * |t - t₀| := by
    have h1 : dist (deriv γ t) v₀ ≤ K * dist t t₀ :=
      lipschitzOnWith_iff_dist_le_mul.mp hlip t ht t₀ ⟨by linarith, by linarith⟩
    rwa [dist_eq_norm, Real.dist_eq] at h1
  have hz_eq : z = ((t - t₀ : ℝ) : ℂ) * v₀ + R := by rw [hR_def]; ring
  have hv_eq : deriv γ t = v₀ + e := by rw [he_def]; ring
  -- The linear part dominates: `‖z‖ ≥ |t - t₀| * ‖v₀‖ / 2`.
  have hz_lower : |t - t₀| * ‖v₀‖ / 2 ≤ ‖z‖ := by
    have h1 : ‖((t - t₀ : ℝ) : ℂ) * v₀‖ - ‖R‖ ≤ ‖z‖ := by
      have := norm_sub_norm_le (((t - t₀ : ℝ) : ℂ) * v₀) (-R)
      rw [sub_neg_eq_add, ← hz_eq, norm_neg] at this
      linarith
    have h2 : ‖((t - t₀ : ℝ) : ℂ) * v₀‖ = |t - t₀| * ‖v₀‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have h3 : K * (t - t₀) ^ 2 ≤ |t - t₀| * ‖v₀‖ / 4 := by
      rw [← habs_sq]
      have h5 : 0 ≤ |t - t₀| := abs_nonneg _
      nlinarith [mul_le_mul_of_nonneg_left hρ h5]
    nlinarith [h1, h2, hR_bound, h3]
  have hz_pos : 0 < ‖z‖ := lt_of_lt_of_le (by
    have : 0 < |t - t₀| := abs_pos.mpr (sub_ne_zero.mpr htne)
    positivity) hz_lower
  -- The numerator is `O((t - t₀) ^ 2)`.
  have hnum_bound : |z.re * (deriv γ t).im - z.im * (deriv γ t).re| ≤
      (2 * ‖v₀‖ * K + K ^ 2 * ε) * (t - t₀) ^ 2 := by
    have hnum_eq : z.re * (deriv γ t).im - z.im * (deriv γ t).re
        = (deriv γ t * (starRingEnd ℂ) z).im := by
      rw [Complex.mul_im, Complex.conj_re, Complex.conj_im]; ring
    rw [hnum_eq]
    have hexpand : deriv γ t * (starRingEnd ℂ) z
        = v₀ * (starRingEnd ℂ) (((t - t₀ : ℝ) : ℂ) * v₀)
          + v₀ * (starRingEnd ℂ) R + e * (starRingEnd ℂ) (((t - t₀ : ℝ) : ℂ) * v₀)
          + e * (starRingEnd ℂ) R := by
      rw [hz_eq, hv_eq, map_add]; ring
    rw [hexpand]
    have h1 : (v₀ * (starRingEnd ℂ) (((t - t₀ : ℝ) : ℂ) * v₀)).im = 0 := by
      have heq : v₀ * (starRingEnd ℂ) (((t - t₀ : ℝ) : ℂ) * v₀)
          = ((t - t₀ : ℝ) : ℂ) * (Complex.normSq v₀ : ℝ) := by
        rw [map_mul, Complex.conj_ofReal, ← mul_assoc, mul_comm v₀, mul_assoc,
          Complex.mul_conj]
      rw [heq]
      simp
    rw [Complex.add_im, Complex.add_im, Complex.add_im, h1, zero_add]
    have hb1 : |(v₀ * (starRingEnd ℂ) R).im| ≤ ‖v₀‖ * (K * (t - t₀) ^ 2) := by
      calc |(v₀ * (starRingEnd ℂ) R).im| ≤ ‖v₀ * (starRingEnd ℂ) R‖ := by
            rw [← RCLike.im_eq_complex_im]; exact RCLike.abs_im_le_norm _
        _ = ‖v₀‖ * ‖R‖ := by rw [norm_mul, RCLike.norm_conj]
        _ ≤ ‖v₀‖ * (K * (t - t₀) ^ 2) := mul_le_mul_of_nonneg_left hR_bound (norm_nonneg _)
    have hb2 : |(e * (starRingEnd ℂ) (((t - t₀ : ℝ) : ℂ) * v₀)).im|
        ≤ (K * |t - t₀|) * (|t - t₀| * ‖v₀‖) := by
      calc |(e * (starRingEnd ℂ) (((t - t₀ : ℝ) : ℂ) * v₀)).im|
            ≤ ‖e * (starRingEnd ℂ) (((t - t₀ : ℝ) : ℂ) * v₀)‖ := by
              rw [← RCLike.im_eq_complex_im]; exact RCLike.abs_im_le_norm _
        _ = ‖e‖ * ‖((t - t₀ : ℝ) : ℂ) * v₀‖ := by rw [norm_mul, RCLike.norm_conj]
        _ = ‖e‖ * (|t - t₀| * ‖v₀‖) := by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        _ ≤ (K * |t - t₀|) * (|t - t₀| * ‖v₀‖) :=
            mul_le_mul_of_nonneg_right he_bound (by positivity)
    have hb3 : |(e * (starRingEnd ℂ) R).im| ≤ (K * |t - t₀|) * (K * (t - t₀) ^ 2) := by
      calc |(e * (starRingEnd ℂ) R).im| ≤ ‖e * (starRingEnd ℂ) R‖ := by
            rw [← RCLike.im_eq_complex_im]; exact RCLike.abs_im_le_norm _
        _ = ‖e‖ * ‖R‖ := by rw [norm_mul, RCLike.norm_conj]
        _ ≤ (K * |t - t₀|) * (K * (t - t₀) ^ 2) := mul_le_mul he_bound hR_bound
          (norm_nonneg _) (by positivity)
    calc |(v₀ * (starRingEnd ℂ) R).im + (e * (starRingEnd ℂ) (((t - t₀ : ℝ) : ℂ) * v₀)).im
          + (e * (starRingEnd ℂ) R).im|
        ≤ |(v₀ * (starRingEnd ℂ) R).im| + |(e * (starRingEnd ℂ) (((t - t₀ : ℝ) : ℂ) * v₀)).im|
          + |(e * (starRingEnd ℂ) R).im| := by
          have e1 := abs_add_le ((v₀ * (starRingEnd ℂ) R).im
            + (e * (starRingEnd ℂ) (((t - t₀ : ℝ) : ℂ) * v₀)).im) (e * (starRingEnd ℂ) R).im
          have e2 := abs_add_le (v₀ * (starRingEnd ℂ) R).im
            (e * (starRingEnd ℂ) (((t - t₀ : ℝ) : ℂ) * v₀)).im
          linarith
      _ ≤ ‖v₀‖ * (K * (t - t₀) ^ 2) + (K * |t - t₀|) * (|t - t₀| * ‖v₀‖)
          + (K * |t - t₀|) * (K * (t - t₀) ^ 2) := add_le_add (add_le_add hb1 hb2) hb3
      _ = (2 * ‖v₀‖ * K) * (t - t₀) ^ 2 + K ^ 2 * |t - t₀| * (t - t₀) ^ 2 := by
          rw [← habs_sq]; ring
      _ ≤ (2 * ‖v₀‖ * K) * (t - t₀) ^ 2 + K ^ 2 * ε * (t - t₀) ^ 2 := by
          have hsq_nonneg : (0 : ℝ) ≤ (t - t₀) ^ 2 := sq_nonneg _
          nlinarith [mul_le_mul_of_nonneg_right habs_le hsq_nonneg,
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right habs_le hsq_nonneg)
              (sq_nonneg (K : ℝ))]
      _ = (2 * ‖v₀‖ * K + K ^ 2 * ε) * (t - t₀) ^ 2 := by ring
  rw [realWindingIntegrand_eq_div, abs_div, Complex.normSq_eq_norm_sq,
    abs_of_pos (by positivity : (0 : ℝ) < ‖z‖ ^ 2)]
  have hD_pos : 0 < (|t - t₀| * ‖v₀‖ / 2) ^ 2 := by positivity
  have step1 : |z.re * (deriv γ t).im - z.im * (deriv γ t).re| / ‖z‖ ^ 2
      ≤ ((2 * ‖v₀‖ * K + K ^ 2 * ε) * (t - t₀) ^ 2) / (|t - t₀| * ‖v₀‖ / 2) ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) hD_pos]
    have hD_le : (|t - t₀| * ‖v₀‖ / 2) ^ 2 ≤ ‖z‖ ^ 2 := pow_le_pow_left₀ (by positivity) hz_lower 2
    have hnum_nonneg : (0 : ℝ) ≤ (2 * ‖v₀‖ * K + K ^ 2 * ε) * (t - t₀) ^ 2 := by positivity
    calc |z.re * (deriv γ t).im - z.im * (deriv γ t).re| * (|t - t₀| * ‖v₀‖ / 2) ^ 2
        ≤ ((2 * ‖v₀‖ * K + K ^ 2 * ε) * (t - t₀) ^ 2) * (|t - t₀| * ‖v₀‖ / 2) ^ 2 :=
          mul_le_mul_of_nonneg_right hnum_bound (by positivity)
      _ ≤ ((2 * ‖v₀‖ * K + K ^ 2 * ε) * (t - t₀) ^ 2) * ‖z‖ ^ 2 :=
          mul_le_mul_of_nonneg_left hD_le hnum_nonneg
  calc |z.re * (deriv γ t).im - z.im * (deriv γ t).re| / ‖z‖ ^ 2
      ≤ ((2 * ‖v₀‖ * K + K ^ 2 * ε) * (t - t₀) ^ 2) / (|t - t₀| * ‖v₀‖ / 2) ^ 2 := step1
    _ = 4 * (2 * ‖v₀‖ * K + K ^ 2 * ε) / ‖v₀‖ ^ 2 := by
        rw [← habs_sq]; field_simp; ring

/-- **Boundedness of the real winding integrand at a `C^{1,1}` crossing.** If `deriv γ` is
`K`-Lipschitz on a neighborhood of a crossing `t₀` where `γ t₀ = w`, and `deriv γ t₀ ≠ 0`, the real
winding integrand is bounded on a small enough symmetric window around `t₀` -- unlike
`isBounded_image_realWindingIntegrand`, no second derivative, pointwise or almost everywhere, is
assumed to exist anywhere. -/
theorem exists_isBounded_image_realWindingIntegrand_of_lipschitzOnWith_deriv
    {γ : ℝ → ℂ} {w : ℂ} {t₀ ε : ℝ} {K : ℝ≥0} (hε_pos : 0 < ε)
    (hderiv : ∀ t ∈ Icc (t₀ - ε) (t₀ + ε), HasDerivAt γ (deriv γ t) t)
    (hlip : LipschitzOnWith K (deriv γ) (Icc (t₀ - ε) (t₀ + ε)))
    (h_eq : γ t₀ = w) (hvel : deriv γ t₀ ≠ 0) :
    ∃ ρ > 0, ρ ≤ ε ∧ Bornology.IsBounded
      ((fun t => realWindingIntegrand (γ t - w) (deriv γ t)) '' Icc (t₀ - ρ) (t₀ + ρ)) := by
  have hv₀_pos : 0 < ‖deriv γ t₀‖ := norm_pos_iff.mpr hvel
  set ρ : ℝ := min ε (‖deriv γ t₀‖ / (8 * ((K : ℝ) + 1))) with hρ_def
  have hρ_pos : 0 < ρ := lt_min hε_pos (by positivity)
  refine ⟨ρ, hρ_pos, min_le_left _ _, Bornology.IsBounded.subset
    (Metric.isBounded_closedBall (x := (0:ℝ))
      (r := 4 * (2 * ‖deriv γ t₀‖ * K + K ^ 2 * ε) / ‖deriv γ t₀‖ ^ 2)) ?_⟩
  rintro x ⟨t, ht, rfl⟩
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]
  have ht' : t ∈ Icc (t₀ - ε) (t₀ + ε) :=
    Icc_subset_Icc (by linarith [min_le_left ε (‖deriv γ t₀‖ / (8 * ((K : ℝ) + 1)))])
      (by linarith [min_le_left ε (‖deriv γ t₀‖ / (8 * ((K : ℝ) + 1)))]) ht
  refine abs_realWindingIntegrand_le_of_lipschitzOnWith hε_pos hderiv hlip h_eq hvel ht' ?_
  have hρ_le : |t - t₀| ≤ ρ := by rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
  have hρ_le' : ρ ≤ ‖deriv γ t₀‖ / (8 * ((K : ℝ) + 1)) := min_le_right _ _
  have hK1_pos : (0 : ℝ) < 4 * ((K : ℝ) + 1) := by positivity
  calc |t - t₀| * (4 * ((K : ℝ) + 1))
      ≤ (‖deriv γ t₀‖ / (8 * ((K : ℝ) + 1))) * (4 * ((K : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_right (hρ_le.trans hρ_le') hK1_pos.le
    _ = ‖deriv γ t₀‖ / 2 := by field_simp; ring
    _ ≤ ‖deriv γ t₀‖ := by linarith

end TauCeti.Contour

end
