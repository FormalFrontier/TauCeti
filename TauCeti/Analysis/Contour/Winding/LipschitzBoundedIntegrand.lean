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

/-- **The cross product of two nearly parallel vectors is small.** The imaginary part of
`u * conj z` is the two-dimensional cross product of `z` and `u`, so it vanishes when both are
real multiples of one vector `v`. This bounds it by the two deviations from that configuration:
`u` from `v`, and `z` from the real multiple `a • v`. -/
private theorem abs_im_mul_conj_le_norm_sub_mul_add_mul_norm_sub_smul (u z v : ℂ) (a : ℝ) :
    |(u * (starRingEnd ℂ) z).im| ≤ ‖u - v‖ * ‖z‖ + ‖v‖ * ‖z - a • v‖ := by
  have habs : ∀ x y : ℂ, |(x * (starRingEnd ℂ) y).im| ≤ ‖x‖ * ‖y‖ := fun x y => by
    simpa [norm_mul, Complex.norm_conj] using Complex.abs_im_le_norm (x * (starRingEnd ℂ) y)
  -- The cross product of `v` with the real multiple `a • v` is zero.
  have hreal : (v * (starRingEnd ℂ) (a • v)).im = 0 := by
    rw [Complex.real_smul, map_mul, Complex.conj_ofReal, ← mul_assoc, mul_comm v, mul_assoc,
      Complex.mul_conj]
    simp
  have hsplit : u * (starRingEnd ℂ) z = (u - v) * (starRingEnd ℂ) z
      + (v * (starRingEnd ℂ) (a • v) + v * (starRingEnd ℂ) (z - a • v)) := by
    rw [map_sub]; ring
  rw [hsplit, Complex.add_im, Complex.add_im, hreal, zero_add]
  exact (abs_add_le _ _).trans (add_le_add (habs _ _) (habs _ _))

/-- **A quadratic error cannot swallow the linear term.** If `z` lies within `K * a ^ 2` of the
real multiple `a • v`, and `a` is small enough that `|a| * (2 * K) ≤ ‖v‖`, then `z` still inherits
half of the length `|a| * ‖v‖` of that multiple. -/
private theorem mul_norm_le_two_mul_norm_of_norm_sub_smul_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {z v : E} {a K : ℝ} (hR : ‖z - a • v‖ ≤ K * a ^ 2)
    (ha : |a| * (2 * K) ≤ ‖v‖) :
    |a| * ‖v‖ ≤ 2 * ‖z‖ := by
  have h1 : ‖a • v‖ - ‖z - a • v‖ ≤ ‖z‖ := by
    simpa [norm_sub_rev z (a • v)] using norm_sub_norm_le (a • v) (a • v - z)
  rw [norm_smul, Real.norm_eq_abs] at h1
  rw [← sq_abs a] at hR
  nlinarith [mul_le_mul_of_nonneg_left ha (abs_nonneg a),
    mul_nonneg (abs_nonneg a) (norm_nonneg v)]

/-- **A quadratically small numerator over a linearly large denominator.** If `|x|` is at most
`N * a ^ 2` while the denominator `d` is at least half of `|a| * b`, the quotient `|x| / d ^ 2`
loses all dependence on `a` and is bounded by `4 * N / b ^ 2`. -/
private theorem abs_div_sq_le_of_abs_le_mul_sq {x a b d N : ℝ} (hN : 0 ≤ N) (hb : 0 < b)
    (hd : |a| * b ≤ 2 * d) (hx : |x| ≤ N * a ^ 2) :
    |x| / d ^ 2 ≤ 4 * N / b ^ 2 := by
  rcases eq_or_ne a 0 with rfl | ha
  · have hx0 : |x| = 0 := le_antisymm (by simpa using hx) (abs_nonneg x)
    rw [hx0, zero_div]
    positivity
  · have hapos : 0 < |a| := abs_pos.mpr ha
    have hdpos : 0 < d := by nlinarith [mul_pos hapos hb]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hsq : a ^ 2 * b ^ 2 ≤ 4 * d ^ 2 := by nlinarith [mul_pos hapos hb, sq_abs a]
    nlinarith [mul_le_mul_of_nonneg_right hx (sq_nonneg b), mul_le_mul_of_nonneg_left hsq hN]

/-- **Pointwise bound on the real winding integrand near a `C^{1,1}` crossing.** For `t` close
enough to `t₀` that `|t - t₀| * (2 * K) ≤ ‖deriv γ t₀‖`, the real winding integrand at
`γ t - w` is bounded independent of `t`. -/
private theorem abs_realWindingIntegrand_le_of_lipschitzOnWith {γ : ℝ → ℂ} {w : ℂ} {t₀ ε : ℝ}
    {K : ℝ≥0} (hε_pos : 0 < ε) (hderiv : ∀ t ∈ Icc (t₀ - ε) (t₀ + ε), HasDerivAt γ (deriv γ t) t)
    (hlip : LipschitzOnWith K (deriv γ) (Icc (t₀ - ε) (t₀ + ε)))
    (h_eq : γ t₀ = w) (hvel : deriv γ t₀ ≠ 0) {t : ℝ} (ht : t ∈ Icc (t₀ - ε) (t₀ + ε))
    (hρ : |t - t₀| * (2 * (K : ℝ)) ≤ ‖deriv γ t₀‖) :
    |realWindingIntegrand (γ t - w) (deriv γ t)| ≤
      4 * (2 * ‖deriv γ t₀‖ * K + K ^ 2 * ε) / ‖deriv γ t₀‖ ^ 2 := by
  have habs_le : |t - t₀| ≤ ε := by rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
  -- A Lipschitz derivative forces a quadratic remainder on `γ` and a linear one on `deriv γ`.
  have hR : ‖γ t - w - (t - t₀) • deriv γ t₀‖ ≤ K * (t - t₀) ^ 2 := by
    have h := norm_sub_sub_smul_deriv_le_of_lipschitzOnWith hε_pos hderiv hlip ht
    rwa [h_eq] at h
  have he : ‖deriv γ t - deriv γ t₀‖ ≤ K * |t - t₀| := by
    have h : dist (deriv γ t) (deriv γ t₀) ≤ K * dist t t₀ :=
      lipschitzOnWith_iff_dist_le_mul.mp hlip t ht t₀ ⟨by linarith, by linarith⟩
    rwa [dist_eq_norm, Real.dist_eq] at h
  -- The linear part `(t - t₀) • deriv γ t₀` controls `γ t - w` from both sides.
  have hlower : |t - t₀| * ‖deriv γ t₀‖ ≤ 2 * ‖γ t - w‖ :=
    mul_norm_le_two_mul_norm_of_norm_sub_smul_le hR hρ
  have hupper : ‖γ t - w‖ ≤ |t - t₀| * ‖deriv γ t₀‖ + K * (t - t₀) ^ 2 := by
    have h := norm_add_le ((t - t₀) • deriv γ t₀) (γ t - w - (t - t₀) • deriv γ t₀)
    rw [norm_smul, Real.norm_eq_abs] at h
    simp only [add_sub_cancel] at h
    linarith
  -- Both deviations from parallelism are `O(t - t₀)`, so the cross product is `O((t - t₀) ^ 2)`.
  have hnum : |(deriv γ t * (starRingEnd ℂ) (γ t - w)).im|
      ≤ (2 * ‖deriv γ t₀‖ * K + K ^ 2 * ε) * (t - t₀) ^ 2 := by
    have hcross := abs_im_mul_conj_le_norm_sub_mul_add_mul_norm_sub_smul
      (deriv γ t) (γ t - w) (deriv γ t₀) (t - t₀)
    have h1 : ‖deriv γ t - deriv γ t₀‖ * ‖γ t - w‖
        ≤ K * ((t - t₀) ^ 2 * ‖deriv γ t₀‖) + K ^ 2 * (|t - t₀| * (t - t₀) ^ 2) :=
      calc ‖deriv γ t - deriv γ t₀‖ * ‖γ t - w‖
          ≤ K * |t - t₀| * (|t - t₀| * ‖deriv γ t₀‖ + K * (t - t₀) ^ 2) :=
            mul_le_mul he hupper (norm_nonneg _) (by positivity)
        _ = K * ((t - t₀) ^ 2 * ‖deriv γ t₀‖) + K ^ 2 * (|t - t₀| * (t - t₀) ^ 2) := by
            rw [← sq_abs (t - t₀)]; ring
    have h2 : ‖deriv γ t₀‖ * ‖γ t - w - (t - t₀) • deriv γ t₀‖
        ≤ ‖deriv γ t₀‖ * (K * (t - t₀) ^ 2) := mul_le_mul_of_nonneg_left hR (norm_nonneg _)
    nlinarith [mul_nonneg (mul_nonneg (sq_nonneg (K : ℝ))
      (sub_nonneg.mpr habs_le)) (sq_nonneg (t - t₀))]
  have hnum_eq : (γ t - w).re * (deriv γ t).im - (γ t - w).im * (deriv γ t).re
      = (deriv γ t * (starRingEnd ℂ) (γ t - w)).im := by
    rw [Complex.mul_im, Complex.conj_re, Complex.conj_im]; ring
  rw [realWindingIntegrand_eq_div, abs_div, Complex.normSq_eq_norm_sq,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖γ t - w‖ ^ 2), hnum_eq]
  exact abs_div_sq_le_of_abs_le_mul_sq (by positivity) (norm_pos_iff.mpr hvel) hlower hnum

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
  -- The radius keeps the `K + 1` denominator, which is positive even when `K = 0`; the pointwise
  -- bound only needs the weaker smallness with `K`.
  have hwide : |t - t₀| * (4 * ((K : ℝ) + 1)) ≤ ‖deriv γ t₀‖ :=
    calc |t - t₀| * (4 * ((K : ℝ) + 1))
        ≤ (‖deriv γ t₀‖ / (8 * ((K : ℝ) + 1))) * (4 * ((K : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_right (hρ_le.trans hρ_le') hK1_pos.le
      _ = ‖deriv γ t₀‖ / 2 := by field_simp; ring
      _ ≤ ‖deriv γ t₀‖ := by linarith
  nlinarith [abs_nonneg (t - t₀), K.coe_nonneg]

end TauCeti.Contour

end
