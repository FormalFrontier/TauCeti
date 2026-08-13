/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Contour.Winding.Integrand
public import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# Boundedness of the real winding integrand at `C^{1,1}` crossings

`Winding/BoundedIntegrand.lean` proves the real winding integrand stays bounded near a crossing
where the curve is `C²`. This file weakens that regularity to merely `C^{1,1}` on each side of the
crossing: `derivWithin γ (Icc c d)` Lipschitz on a one-sided closed piece `[c, d]` ending or
starting at the crossing, with no second derivative -- pointwise or almost everywhere -- assumed
to exist anywhere, and no assumption that the two sides agree. This covers a crossing that
coincides with a breakpoint of a piecewise-`C¹` immersion (a corner, where the two one-sided
tangents may differ), not just a crossing where `γ` is genuinely differentiable on a full
two-sided neighborhood. This is a genuinely different proof technique from the `C²` case, not a
weakening of it: the `C²` proof reads the bounded limit off an explicit curvature value at the
crossing (which needs a second derivative there); this file instead bounds the integrand directly
from the quadratic remainder a Lipschitz derivative forces on the curve itself, via the mean value
inequality applied to the affine remainder on the segment from the crossing to each nearby
parameter -- entirely on one side at a time, so the two sides never need to interact. Only plain
differentiability of `γ` is assumed (not continuity of its derivative): Lipschitz-ness of
`derivWithin γ (Icc c d)` already gives that for free.

## Main results

* `TauCeti.Contour.exists_isBounded_image_realWindingIntegrand_of_lipschitzOnWith_derivWithin_right`
  and `..._left` -- the real winding integrand is bounded on a small enough one-sided window,
  starting (resp. ending) at a crossing where `derivWithin γ` is Lipschitz and non-zero there, on
  the one-sided piece the window lies in.
* `..._corner` -- the two one-sided windows above combined into one full neighborhood of the
  crossing, allowing the two sides to disagree.

## References

* N. Hungerbühler and M. Wasem, *Non-integer valued winding numbers and a generalized Residue
  Theorem*, arXiv:1808.00997 (2018), Proposition 2.3 and its proof (which handles a crossing at a
  corner via exactly this one-sided splitting, p. 9).
-/

public section

noncomputable section

namespace TauCeti.Contour

open Complex Filter Set Topology

open scoped NNReal Pointwise

/-- **The quadratic remainder of a Lipschitz one-sided derivative.** If `γ` is differentiable on
`[c, d]` and `derivWithin γ (Icc c d)` is `K`-Lipschitz there, the affine approximation at any
`t₀ ∈ [c, d]` is off by at most `K * (t - t₀) ^ 2`, for any `t ∈ [c, d]`. -/
private theorem norm_sub_sub_smul_derivWithin_le_of_lipschitzOnWith {γ : ℝ → ℂ} {c d : ℝ}
    {K : ℝ≥0} (hdiff : DifferentiableOn ℝ γ (Icc c d))
    (hlip : LipschitzOnWith K (derivWithin γ (Icc c d)) (Icc c d))
    {t₀ t : ℝ} (ht₀ : t₀ ∈ Icc c d) (ht : t ∈ Icc c d) :
    ‖γ t - γ t₀ - (t - t₀) • derivWithin γ (Icc c d) t₀‖ ≤ K * (t - t₀) ^ 2 := by
  set D : ℝ → ℂ := derivWithin γ (Icc c d)
  set g : ℝ → ℂ := fun u => γ u - γ t₀ - (u - t₀) • D t₀ with hg_def
  have hsub : uIcc t₀ t ⊆ Icc c d := Icc_subset_Icc (le_min ht₀.1 ht.1) (max_le ht₀.2 ht.2)
  have hg_deriv : ∀ u ∈ uIcc t₀ t, HasDerivWithinAt g (D u - D t₀) (uIcc t₀ t) u := fun u hu => by
    have h1 : HasDerivWithinAt (fun u => γ u - γ t₀) (D u) (uIcc t₀ t) u :=
      ((hdiff u (hsub hu)).hasDerivWithinAt.mono hsub).sub_const _
    have h2 : HasDerivWithinAt (fun u => (u - t₀) • D t₀) (D t₀) (uIcc t₀ t) u := by
      simpa using (((hasDerivAt_id u).sub_const t₀).smul_const (D t₀)).hasDerivWithinAt
    exact h1.sub h2
  have hbound : ∀ u ∈ uIcc t₀ t, ‖D u - D t₀‖ ≤ K * |t - t₀| := fun u hu => by
    have h1 : dist (D u) (D t₀) ≤ K * dist u t₀ :=
      lipschitzOnWith_iff_dist_le_mul.mp hlip u (hsub hu) t₀ ht₀
    rw [dist_eq_norm, Real.dist_eq] at h1
    have h2 : |u - t₀| ≤ |t - t₀| := abs_sub_left_of_mem_uIcc hu
    calc ‖D u - D t₀‖ ≤ K * |u - t₀| := h1
      _ ≤ K * |t - t₀| := by gcongr
  have hthis := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hg_deriv hbound
    (convex_uIcc t₀ t) left_mem_uIcc right_mem_uIcc
  have heq : g t - g t₀ = g t := by simp [hg_def]
  rw [heq] at hthis
  calc ‖g t‖ ≤ K * |t - t₀| * ‖t - t₀‖ := hthis
    _ = K * (t - t₀) ^ 2 := by rw [Real.norm_eq_abs, ← sq_abs]; ring

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

/-- **Pointwise bound on the real winding integrand near a one-sided `C^{1,1}` crossing.** For
`t ∈ [c, d]` close enough to `t₀ ∈ [c, d]` that `|t - t₀| * (2 * K) ≤
‖derivWithin γ (Icc c d) t₀‖`, the real winding integrand at `γ t - w` (using the within-piece
derivative at `t`) is bounded independent of `t`. -/
private theorem abs_realWindingIntegrand_le_of_lipschitzOnWith_derivWithin {γ : ℝ → ℂ} {w : ℂ}
    {c d : ℝ} {K : ℝ≥0} (hdiff : DifferentiableOn ℝ γ (Icc c d))
    (hlip : LipschitzOnWith K (derivWithin γ (Icc c d)) (Icc c d))
    {t₀ : ℝ} (ht₀ : t₀ ∈ Icc c d) (h_eq : γ t₀ = w)
    (hvel : derivWithin γ (Icc c d) t₀ ≠ 0) {t : ℝ} (ht : t ∈ Icc c d)
    (hρ : |t - t₀| * (2 * (K : ℝ)) ≤ ‖derivWithin γ (Icc c d) t₀‖) :
    |realWindingIntegrand (γ t - w) (derivWithin γ (Icc c d) t)| ≤
      4 * (2 * ‖derivWithin γ (Icc c d) t₀‖ * K + K ^ 2 * (d - c)) /
        ‖derivWithin γ (Icc c d) t₀‖ ^ 2 := by
  set D : ℝ → ℂ := derivWithin γ (Icc c d)
  have hcd : c ≤ d := ht₀.1.trans ht₀.2
  have habs_le : |t - t₀| ≤ d - c := by
    rw [abs_le]; exact ⟨by linarith [ht.1, ht₀.2], by linarith [ht.2, ht₀.1]⟩
  have hR : ‖γ t - w - (t - t₀) • D t₀‖ ≤ K * (t - t₀) ^ 2 := by
    have h := norm_sub_sub_smul_derivWithin_le_of_lipschitzOnWith hdiff hlip ht₀ ht
    rwa [h_eq] at h
  have he : ‖D t - D t₀‖ ≤ K * |t - t₀| := by
    have h : dist (D t) (D t₀) ≤ K * dist t t₀ :=
      lipschitzOnWith_iff_dist_le_mul.mp hlip t ht t₀ ht₀
    rwa [dist_eq_norm, Real.dist_eq] at h
  have hlower : |t - t₀| * ‖D t₀‖ ≤ 2 * ‖γ t - w‖ :=
    mul_norm_le_two_mul_norm_of_norm_sub_smul_le hR hρ
  have hupper : ‖γ t - w‖ ≤ |t - t₀| * ‖D t₀‖ + K * (t - t₀) ^ 2 := by
    have h := norm_add_le ((t - t₀) • D t₀) (γ t - w - (t - t₀) • D t₀)
    rw [norm_smul, Real.norm_eq_abs] at h
    simp only [add_sub_cancel] at h
    linarith
  have hnum : |(D t * (starRingEnd ℂ) (γ t - w)).im|
      ≤ (2 * ‖D t₀‖ * K + K ^ 2 * (d - c)) * (t - t₀) ^ 2 := by
    have hcross := abs_im_mul_conj_le_norm_sub_mul_add_mul_norm_sub_smul
      (D t) (γ t - w) (D t₀) (t - t₀)
    have h1 : ‖D t - D t₀‖ * ‖γ t - w‖
        ≤ K * ((t - t₀) ^ 2 * ‖D t₀‖) + K ^ 2 * (|t - t₀| * (t - t₀) ^ 2) :=
      calc ‖D t - D t₀‖ * ‖γ t - w‖
          ≤ K * |t - t₀| * (|t - t₀| * ‖D t₀‖ + K * (t - t₀) ^ 2) :=
            mul_le_mul he hupper (norm_nonneg _) (by positivity)
        _ = K * ((t - t₀) ^ 2 * ‖D t₀‖) + K ^ 2 * (|t - t₀| * (t - t₀) ^ 2) := by
            rw [← sq_abs (t - t₀)]; ring
    have h2 : ‖D t₀‖ * ‖γ t - w - (t - t₀) • D t₀‖
        ≤ ‖D t₀‖ * (K * (t - t₀) ^ 2) := mul_le_mul_of_nonneg_left hR (norm_nonneg _)
    nlinarith [mul_nonneg (mul_nonneg (sq_nonneg (K : ℝ))
      (sub_nonneg.mpr habs_le)) (sq_nonneg (t - t₀))]
  have hnum_eq : (γ t - w).re * (D t).im - (γ t - w).im * (D t).re
      = (D t * (starRingEnd ℂ) (γ t - w)).im := by
    rw [Complex.mul_im, Complex.conj_re, Complex.conj_im]; ring
  rw [realWindingIntegrand_eq_div, abs_div, Complex.normSq_eq_norm_sq,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖γ t - w‖ ^ 2), hnum_eq]
  exact abs_div_sq_le_of_abs_le_mul_sq (by positivity) (norm_pos_iff.mpr hvel) hlower hnum

/-- **Boundedness of the real winding integrand at a `C^{1,1}` crossing, from the right.** If `γ`
is differentiable on `[t₀, d]` and `derivWithin γ (Icc t₀ d)` is `K`-Lipschitz there and non-zero
at `t₀`, where `γ t₀ = w`, then the real winding integrand (the ordinary derivative, which agrees
with the within-piece one strictly inside `[t₀, d]`) is bounded on a small enough right-window
`[t₀, t₀ + ρ]` -- no second derivative, pointwise or almost everywhere, is assumed to exist
anywhere, and no assumption is made about `γ` to the left of `t₀`. At `t₀` itself `deriv γ t₀` may
take any junk value (it need not equal the one-sided `derivWithin`): the integrand there is
`realWindingIntegrand 0 _`, independent of the velocity argument, so the junk value is harmless.
This is the corner case of `Winding/BoundedIntegrand.lean`'s smooth-crossing result: `t₀` may
coincide with a breakpoint of a piecewise-`C¹` immersion, where the left tangent may disagree with
this one. -/
theorem exists_isBounded_image_realWindingIntegrand_of_lipschitzOnWith_derivWithin_right
    {γ : ℝ → ℂ} {w : ℂ} {t₀ d : ℝ} {K : ℝ≥0} (htd : t₀ < d)
    (hdiff : DifferentiableOn ℝ γ (Icc t₀ d))
    (hlip : LipschitzOnWith K (derivWithin γ (Icc t₀ d)) (Icc t₀ d))
    (h_eq : γ t₀ = w) (hvel : derivWithin γ (Icc t₀ d) t₀ ≠ 0) :
    ∃ ρ > 0, ρ < d - t₀ ∧ Bornology.IsBounded
      ((fun t => realWindingIntegrand (γ t - w) (deriv γ t)) '' Icc t₀ (t₀ + ρ)) := by
  set ρ : ℝ := min ((d - t₀) / 2) (‖derivWithin γ (Icc t₀ d) t₀‖ / (4 * ((K : ℝ) + 1))) with hρ_def
  have hρ_pos : 0 < ρ := lt_min (by linarith) (by positivity)
  have hρ_lt : ρ < d - t₀ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  set r : ℝ := 4 * (2 * ‖derivWithin γ (Icc t₀ d) t₀‖ * K + K ^ 2 * (d - t₀)) /
    ‖derivWithin γ (Icc t₀ d) t₀‖ ^ 2 with hr_def
  have hr_nonneg : 0 ≤ r := by rw [hr_def]; positivity
  refine ⟨ρ, hρ_pos, hρ_lt, Bornology.IsBounded.subset
    (Metric.isBounded_closedBall (x := (0 : ℝ)) (r := r)) ?_⟩
  rintro x ⟨t, ht, rfl⟩
  -- Beta-reduce the `(fun t => ...) t` left behind by `rfl` above, so the next `rw` can see
  -- `realWindingIntegrand` at the head of the goal.
  simp only []
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]
  rcases eq_or_ne t t₀ with rfl | htne
  · have hz0 : γ t - w = 0 := by rw [h_eq, sub_self]
    simp only [hz0, realWindingIntegrand_eq_div, Complex.zero_re, Complex.zero_im, zero_mul,
      sub_zero, Complex.normSq_zero, div_zero, abs_zero]
    exact hr_nonneg
  · have htcd : t ∈ Icc t₀ d := ⟨ht.1, by linarith [ht.2]⟩
    have hDeq : deriv γ t = derivWithin γ (Icc t₀ d) t :=
      (derivWithin_of_mem_nhds
        (Icc_mem_nhds (lt_of_le_of_ne ht.1 (Ne.symm htne)) (by linarith [ht.2]))).symm
    rw [hDeq]
    refine abs_realWindingIntegrand_le_of_lipschitzOnWith_derivWithin hdiff hlip
      (left_mem_Icc.mpr htd.le) h_eq hvel htcd ?_
    have habs : |t - t₀| = t - t₀ := abs_of_nonneg (by linarith [ht.1])
    rw [habs]
    have h1 : t - t₀ ≤ ρ := by linarith [ht.2]
    have h2 : ρ ≤ ‖derivWithin γ (Icc t₀ d) t₀‖ / (4 * ((K : ℝ) + 1)) := min_le_right _ _
    have hK1 : (0 : ℝ) < 2 * ((K : ℝ) + 1) := by positivity
    calc (t - t₀) * (2 * (K : ℝ)) ≤ (t - t₀) * (2 * ((K : ℝ) + 1)) :=
            mul_le_mul_of_nonneg_left (by linarith) (by linarith [ht.1])
      _ ≤ ρ * (2 * ((K : ℝ) + 1)) := mul_le_mul_of_nonneg_right h1 hK1.le
      _ ≤ (‖derivWithin γ (Icc t₀ d) t₀‖ / (4 * ((K : ℝ) + 1))) * (2 * ((K : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_right h2 hK1.le
      _ = ‖derivWithin γ (Icc t₀ d) t₀‖ / 2 := by field_simp; ring
      _ ≤ ‖derivWithin γ (Icc t₀ d) t₀‖ := half_le_self (norm_nonneg _)

/-- **The point-reflected piece is differentiable.** If `γ` is differentiable on `[c, t₀]`, then
`s ↦ γ (2 * t₀ - s)` is differentiable on the mirrored piece `[t₀, 2 * t₀ - c]`. -/
private theorem differentiableOn_comp_const_sub {γ : ℝ → ℂ} {c t₀ : ℝ}
    (hdiff : DifferentiableOn ℝ γ (Icc c t₀)) :
    DifferentiableOn ℝ (fun s => γ (2 * t₀ - s)) (Icc t₀ (2 * t₀ - c)) := by
  have hmap : Set.MapsTo (fun s : ℝ => 2 * t₀ - s) (Icc t₀ (2 * t₀ - c)) (Icc c t₀) :=
    fun s hs => ⟨by linarith [hs.2], by linarith [hs.1]⟩
  exact hdiff.comp (differentiable_id.const_sub (2 * t₀)).differentiableOn hmap

/-- **The within-derivative of the point-reflected piece.** The within-derivative of
`s ↦ γ (2 * t₀ - s)` on `[t₀, 2 * t₀ - c]` is minus `γ`'s own within-derivative on `[c, t₀]` at
the reflected point. -/
private theorem derivWithin_comp_const_sub_Icc (γ : ℝ → ℂ) (c t₀ t : ℝ) :
    derivWithin (fun s => γ (2 * t₀ - s)) (Icc t₀ (2 * t₀ - c)) t
      = -derivWithin γ (Icc c t₀) (2 * t₀ - t) := by
  -- `Mathlib`'s `derivWithin_comp_const_sub`, simplified from a pointwise-negated-and-shifted set
  -- to the plain `Icc c t₀` it amounts to here.
  have hset : 2 * t₀ +ᵥ -Icc t₀ (2 * t₀ - c) = Icc c t₀ := by
    ext x
    simp only [Set.mem_vadd_set, Set.mem_neg, Set.mem_Icc, vadd_eq_add]
    constructor
    · rintro ⟨y, ⟨hy1, hy2⟩, rfl⟩; constructor <;> linarith
    · rintro ⟨hx1, hx2⟩; exact ⟨x - 2 * t₀, ⟨by linarith, by linarith⟩, by ring⟩
  rw [derivWithin_comp_const_sub, hset]

/-- **The point-reflected piece is `C^{1,1}` with the same Lipschitz constant.** If
`derivWithin γ (Icc c t₀)` is `K`-Lipschitz, so is the within-derivative of the point-reflected
piece `s ↦ γ (2 * t₀ - s)` on `[t₀, 2 * t₀ - c]`, with the *same* constant `K`. -/
private theorem lipschitzOnWith_derivWithin_comp_const_sub {γ : ℝ → ℂ} {c t₀ : ℝ}
    {K : ℝ≥0} (hlip : LipschitzOnWith K (derivWithin γ (Icc c t₀)) (Icc c t₀)) :
    LipschitzOnWith K (derivWithin (fun s => γ (2 * t₀ - s)) (Icc t₀ (2 * t₀ - c)))
      (Icc t₀ (2 * t₀ - c)) := by
  rw [lipschitzOnWith_iff_dist_le_mul] at hlip ⊢
  intro t ht s hs
  rw [derivWithin_comp_const_sub_Icc γ c t₀ t, derivWithin_comp_const_sub_Icc γ c t₀ s,
    dist_neg_neg]
  have hmem_t : 2 * t₀ - t ∈ Icc c t₀ := ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hmem_s : 2 * t₀ - s ∈ Icc c t₀ := ⟨by linarith [hs.2], by linarith [hs.1]⟩
  rw [← dist_sub_left (2 * t₀) t s]
  exact hlip (2 * t₀ - t) hmem_t (2 * t₀ - s) hmem_s

/-- **Boundedness of the real winding integrand at a `C^{1,1}` crossing, from the left.** If `γ`
is differentiable on `[c, t₀]` and `derivWithin γ (Icc c t₀)` is `K`-Lipschitz there and non-zero
at `t₀`, where `γ t₀ = w`, then the real winding integrand (the ordinary derivative, which agrees
with the within-piece one strictly inside `[c, t₀]`) is bounded on a small enough left-window
`[t₀ - ρ, t₀]` -- no second derivative, pointwise or almost everywhere, is assumed to exist
anywhere, and no assumption is made about `γ` to the right of `t₀`. As in `_right`, `deriv γ t₀`'s
junk value at the crossing itself is harmless: the integrand there is `realWindingIntegrand 0 _`,
independent of the velocity argument. The mirror case of `_right` above. -/
theorem exists_isBounded_image_realWindingIntegrand_of_lipschitzOnWith_derivWithin_left
    {γ : ℝ → ℂ} {w : ℂ} {c t₀ : ℝ} {K : ℝ≥0} (hct : c < t₀)
    (hdiff : DifferentiableOn ℝ γ (Icc c t₀))
    (hlip : LipschitzOnWith K (derivWithin γ (Icc c t₀)) (Icc c t₀))
    (h_eq : γ t₀ = w) (hvel : derivWithin γ (Icc c t₀) t₀ ≠ 0) :
    ∃ ρ > 0, ρ < t₀ - c ∧ Bornology.IsBounded
      ((fun t => realWindingIntegrand (γ t - w) (deriv γ t)) '' Icc (t₀ - ρ) t₀) := by
  -- Apply `_right` to the point-reflected curve `γ'` rather than repeating its proof.
  set γ' : ℝ → ℂ := fun s => γ (2 * t₀ - s) with hγ'_def
  have hd'_gt : t₀ < 2 * t₀ - c := by linarith
  -- The crossing `t₀` reflects to itself; used at each of the several places below that need to
  -- relate a fact about `γ'` (stated via `2 * t₀ - t₀`) back to the corresponding fact about `γ`.
  have h2t₀ : (2 : ℝ) * t₀ - t₀ = t₀ := by ring
  have hdiff' : DifferentiableOn ℝ γ' (Icc t₀ (2 * t₀ - c)) :=
    differentiableOn_comp_const_sub hdiff
  have hlip' : LipschitzOnWith K (derivWithin γ' (Icc t₀ (2 * t₀ - c))) (Icc t₀ (2 * t₀ - c)) :=
    lipschitzOnWith_derivWithin_comp_const_sub hlip
  have h_eq' : γ' t₀ = w := by
    -- `rw [hγ'_def]` alone would leave the unapplied `(fun s => γ (2 * t₀ - s)) t₀`, since `rw`
    -- does not beta-reduce; `change` unfolds `γ'` and applies it in one step (both defeq to it).
    change γ (2 * t₀ - t₀) = w
    rw [h2t₀]; exact h_eq
  have hvel' : derivWithin γ' (Icc t₀ (2 * t₀ - c)) t₀ ≠ 0 := by
    rw [hγ'_def, derivWithin_comp_const_sub_Icc γ c t₀ t₀, h2t₀]
    simpa using hvel
  obtain ⟨ρ, hρ_pos, hρ_lt, hbdd⟩ :=
    exists_isBounded_image_realWindingIntegrand_of_lipschitzOnWith_derivWithin_right
      hd'_gt hdiff' hlip' h_eq' hvel'
  refine ⟨ρ, hρ_pos, by linarith, ?_⟩
  have himg : (fun t => realWindingIntegrand (γ t - w) (deriv γ t)) '' Icc (t₀ - ρ) t₀
      = Neg.neg '' ((fun t => realWindingIntegrand (γ' t - w) (deriv γ' t)) ''
          Icc t₀ (t₀ + ρ)) := by
    have hIcc_eq : Icc (t₀ - ρ) t₀ = (fun t => 2 * t₀ - t) '' Icc t₀ (t₀ + ρ) := by
      rw [image_const_sub_Icc]; congr 1 <;> ring
    rw [hIcc_eq, Set.image_image, Set.image_image]
    apply Set.image_congr
    intro t ht
    rcases eq_or_ne t t₀ with heq | htne
    · have hz2 : γ (2 * t₀ - t) - w = 0 := by
        rw [heq, h2t₀, h_eq, sub_self]
      -- `Set.image_congr`'s goal states the right side's position as `γ' t - w`, defeq (via
      -- `γ'`'s definition) but not syntactically equal to the `γ (2 * t₀ - t) - w` on the left;
      -- `change` records that both sides already talk about the same position, before `hz2`
      -- zeroes it out on both.
      change realWindingIntegrand (γ (2 * t₀ - t) - w) (deriv γ (2 * t₀ - t))
        = -realWindingIntegrand (γ (2 * t₀ - t) - w) (deriv γ' t)
      simp [hz2]
    · have htlt : t₀ < t := lt_of_le_of_ne ht.1 (Ne.symm htne)
      have hint : t ∈ Ioo t₀ (2 * t₀ - c) := ⟨htlt, by linarith [ht.2]⟩
      have hDeq' : deriv γ' t = derivWithin γ' (Icc t₀ (2 * t₀ - c)) t :=
        (derivWithin_of_mem_nhds (Icc_mem_nhds hint.1 hint.2)).symm
      have hint2 : 2 * t₀ - t ∈ Ioo c t₀ := ⟨by linarith [ht.2], by linarith [htlt]⟩
      have hDeq : deriv γ (2 * t₀ - t) = derivWithin γ (Icc c t₀) (2 * t₀ - t) :=
        (derivWithin_of_mem_nhds (Icc_mem_nhds hint2.1 hint2.2)).symm
      have hDeriv_eq : deriv γ' t = -deriv γ (2 * t₀ - t) := by
        rw [hDeq', hγ'_def, derivWithin_comp_const_sub_Icc γ c t₀ t, hDeq]
      -- Same defeq-not-syntactic gap as the `heq` case above: restate the position on both
      -- sides as `γ (2 * t₀ - t) - w` so the remaining rewrites only need to track the velocity.
      change realWindingIntegrand (γ (2 * t₀ - t) - w) (deriv γ (2 * t₀ - t))
        = -realWindingIntegrand (γ (2 * t₀ - t) - w) (deriv γ' t)
      rw [hDeriv_eq, realWindingIntegrand_neg_right, neg_neg]
  rw [himg, Set.image_neg_eq_neg]
  exact hbdd.neg

/-- **Boundedness of the real winding integrand on the full neighborhood of a `C^{1,1}` corner
crossing.** Combines `_right` and `_left` above into the full two-sided window `[t₀ - ρ, t₀ + ρ]`,
allowing the two sides to have genuinely different pieces and Lipschitz constants, as at a
corner where the one-sided tangents themselves may differ. -/
theorem exists_isBounded_image_realWindingIntegrand_of_lipschitzOnWith_derivWithin_corner
    {γ : ℝ → ℂ} {w : ℂ} {c t₀ d : ℝ} {KR KL : ℝ≥0} (hct : c < t₀) (htd : t₀ < d)
    (hdiffR : DifferentiableOn ℝ γ (Icc t₀ d))
    (hlipR : LipschitzOnWith KR (derivWithin γ (Icc t₀ d)) (Icc t₀ d))
    (hdiffL : DifferentiableOn ℝ γ (Icc c t₀))
    (hlipL : LipschitzOnWith KL (derivWithin γ (Icc c t₀)) (Icc c t₀)) (h_eq : γ t₀ = w)
    (hvelR : derivWithin γ (Icc t₀ d) t₀ ≠ 0) (hvelL : derivWithin γ (Icc c t₀) t₀ ≠ 0) :
    ∃ ρ > 0, ρ < min (d - t₀) (t₀ - c) ∧ Bornology.IsBounded
      ((fun t => realWindingIntegrand (γ t - w) (deriv γ t)) '' Icc (t₀ - ρ) (t₀ + ρ)) := by
  obtain ⟨ρR, hρR_pos, hρR_lt, hbddR⟩ :=
    exists_isBounded_image_realWindingIntegrand_of_lipschitzOnWith_derivWithin_right
      htd hdiffR hlipR h_eq hvelR
  obtain ⟨ρL, hρL_pos, hρL_lt, hbddL⟩ :=
    exists_isBounded_image_realWindingIntegrand_of_lipschitzOnWith_derivWithin_left
      hct hdiffL hlipL h_eq hvelL
  refine ⟨min ρR ρL, lt_min hρR_pos hρL_pos,
    lt_min ((min_le_left ρR ρL).trans_lt hρR_lt) ((min_le_right ρR ρL).trans_lt hρL_lt), ?_⟩
  -- Split the symmetric window at `t₀` so the left/right one-sided boundedness facts
  -- `hbddL`/`hbddR` combine via `Set.image_union` into one on the whole window.
  have hsplit : Icc (t₀ - min ρR ρL) (t₀ + min ρR ρL)
      = Icc (t₀ - min ρR ρL) t₀ ∪ Icc t₀ (t₀ + min ρR ρL) :=
    (Set.Icc_union_Icc_eq_Icc (by linarith [lt_min hρR_pos hρL_pos])
      (by linarith [lt_min hρR_pos hρL_pos])).symm
  rw [hsplit, Set.image_union]
  exact (hbddL.subset (Set.image_mono
      (Icc_subset_Icc (by linarith [min_le_right ρR ρL]) le_rfl))).union
    (hbddR.subset (Set.image_mono (Icc_subset_Icc le_rfl (by linarith [min_le_left ρR ρL]))))

end TauCeti.Contour

end
