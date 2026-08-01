/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.LeftRightNhds

/-!
# Chord-quotient asymptotics at a transverse crossing

For a curve `γ : ℝ → ℂ` through a pole `s = γ t₀` with non-vanishing one-sided derivative `L`,
the chord quotient `(γ t - s) / (t - t₀)` tends to `L`, so on a small one-sided interval the
normalized chord `(γ t - s) / (L (t - t₀))` is close to `1`. Two consequences feed the
principal-value existence argument at the crossing:

* chord quotients `(γ b - s) / (γ a - s)` for `a, b` on a common side lie in
  `Complex.slitPlane` — the hypothesis under which the logarithmic fundamental theorem of
  calculus (`Contour.integral_inv_sub_mul_deriv_eq_log`) applies on the excised pieces;
* the arguments of the annular quotients converge as the excision cutoff `δ(ε) → 0⁺`, which
  pins the angle contribution of each branch at the pole.

Where the two sides share a proof, the statement is parametrised over the within-set `u`
(`Ioi t₀` on the right, `Iio t₀` on the left).

## Main results

* `Contour.chord_quotient_tendsto` — `(γ t - s) / (t - t₀) → L` along `𝓝[u] t₀` for `t₀ ∉ u`.
* `Contour.exists_normalized_chord_bound_right` / `_left` — `‖(γ t - s)/(L(t - t₀)) - 1‖ ≤ ρ`
  on a fixed one-sided interval.
* `Contour.div_mem_slitPlane_of_close_to_one` — `z / w ∈ slitPlane` for `z, w` `1/4`-close
  to `1`.
* `Contour.exists_chord_quotient_mem_slitPlane_right` / `_left` — chord quotients on a small
  one-sided interval lie in the slit plane.
* `Contour.arg_annular_quotient_tendsto_right` / `_left` — convergence of the annular
  quotient arguments along a positive cutoff `δ(ε) → 0⁺`.
* `Contour.exists_chord_div_tangent_mem_slitPlane_right` /
  `Contour.exists_neg_tangent_div_chord_mem_slitPlane_left` — a window radius on which the
  boundary quotients (chord over tangent on the right, negated tangent over chord on the left)
  lie in the slit plane, discharging the `h_slit` hypotheses of the annular lemmas.
* `Contour.exists_crossing_slitPlane_radius` — the per-crossing package: one radius carrying
  all four slit-plane properties together with the non-zero one-sided derivatives, ready for a
  common minimum across the crossings of a pole.

## Provenance

Migrated from `chord_div_t_tendsto`, `normalized_chord_close`, `exists_normalized_chord_*`,
`div_mem_slitPlane_of_close_to_one`, `chord_quotient_mem_slitPlane`,
`exists_slitPlane_chord_quotient_*`, `tendsto_arg_of_pos_smul_tendsto`, and
`arg_*_annular_tendsto` of `CPVExistence.lean`, together with
`exists_chord_div_endpoint_slitPlane_right`/`_left` of `LocalCutoffs.lean`, in the AINTLIB
`LeanModularForms` development.
See N. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a generalized Residue
Theorem*, arXiv:1808.00997, §3.
-/

public section

noncomputable section

namespace TauCeti.Contour

open Filter Set Topology

variable {γ : ℝ → ℂ} {t₀ : ℝ} {s L : ℂ}

/-- **Chord-to-tangent quotient limit.** Given `HasDerivWithinAt γ L u t₀` with `t₀ ∉ u` and
`γ t₀ = s`, the chord quotient `(γ t - s) / (t - t₀)` tends to `L` along `𝓝[u] t₀`.
Specialises to the one-sided limits at `u = Ioi t₀` (right) and `u = Iio t₀` (left). -/
theorem chord_quotient_tendsto {u : Set ℝ} (hu : t₀ ∉ u)
    (h_deriv : HasDerivWithinAt γ L u t₀) (h_at : γ t₀ = s) :
    Tendsto (fun t : ℝ => (γ t - s) / ((t - t₀ : ℝ) : ℂ)) (𝓝[u] t₀) (𝓝 L) := by
  refine ((hasDerivWithinAt_iff_tendsto_slope' hu).mp h_deriv).congr fun t => ?_
  rw [slope_def_module, h_at, Complex.real_smul, Complex.ofReal_inv, inv_mul_eq_div]

/-- **The normalized chord is eventually close to `1`**: for any `ρ > 0`, eventually along
`𝓝[u] t₀`, `‖(γ t - s) / (L (t - t₀)) - 1‖ ≤ ρ`. -/
private theorem eventually_normalized_chord_close {u : Set ℝ} (hu : t₀ ∉ u)
    (h_deriv : HasDerivWithinAt γ L u t₀) (h_at : γ t₀ = s) (hL : L ≠ 0) {ρ : ℝ} (hρ_pos : 0 < ρ) :
    ∀ᶠ t in 𝓝[u] t₀, ‖(γ t - s) / (L * ((t - t₀ : ℝ) : ℂ)) - 1‖ ≤ ρ := by
  have h_div := (chord_quotient_tendsto hu h_deriv h_at).div_const L
  rw [div_self hL] at h_div
  have h_one : Tendsto (fun t : ℝ => (γ t - s) / (L * ((t - t₀ : ℝ) : ℂ)))
      (𝓝[u] t₀) (𝓝 1) := h_div.congr fun t => by rw [div_div, mul_comm]
  filter_upwards [Metric.tendsto_nhds.mp h_one ρ hρ_pos] with t ht
  rw [dist_eq_norm] at ht
  exact ht.le

/-- **Fixed-radius normalized chord bound (right side)**: a positive radius `r` on whose
right interval `(t₀, t₀ + r]` the normalized chord is uniformly `ρ`-close to `1`. -/
theorem exists_normalized_chord_bound_right
    (h_deriv : HasDerivWithinAt γ L (Ioi t₀) t₀) (h_at : γ t₀ = s) (hL : L ≠ 0)
    {ρ : ℝ} (hρ_pos : 0 < ρ) :
    ∃ r > 0, ∀ t ∈ Ioc t₀ (t₀ + r),
      ‖(γ t - s) / (L * ((t - t₀ : ℝ) : ℂ)) - 1‖ ≤ ρ := by
  obtain ⟨c, hc, h⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp
    (eventually_normalized_chord_close self_notMem_Ioi h_deriv h_at hL hρ_pos)
  exact ⟨c - t₀, sub_pos.mpr hc, fun t ht => h ⟨ht.1, by linarith [ht.2]⟩⟩

/-- **Fixed-radius normalized chord bound (left side)**: the counterpart of
`exists_normalized_chord_bound_right` on `[t₀ - r, t₀)`. -/
theorem exists_normalized_chord_bound_left
    (h_deriv : HasDerivWithinAt γ L (Iio t₀) t₀) (h_at : γ t₀ = s) (hL : L ≠ 0)
    {ρ : ℝ} (hρ_pos : 0 < ρ) :
    ∃ r > 0, ∀ t ∈ Ico (t₀ - r) t₀,
      ‖(γ t - s) / (L * ((t - t₀ : ℝ) : ℂ)) - 1‖ ≤ ρ := by
  obtain ⟨c, hc, h⟩ := mem_nhdsLT_iff_exists_Ico_subset.mp
    (eventually_normalized_chord_close self_notMem_Iio h_deriv h_at hL hρ_pos)
  exact ⟨t₀ - c, sub_pos.mpr hc, fun t ht => h ⟨by linarith [ht.1], ht.2⟩⟩

/-- **Slit-plane condition for quotients near `1`.** If `‖z - 1‖ ≤ 1/4` and `‖w - 1‖ ≤ 1/4`,
then `z / w ∈ Complex.slitPlane`: the quotient stays in the unit ball around `1`. -/
theorem div_mem_slitPlane_of_close_to_one {z w : ℂ} (hz : ‖z - 1‖ ≤ 1 / 4) (hw : ‖w - 1‖ ≤ 1 / 4) :
    z / w ∈ Complex.slitPlane := by
  have hw_ne : w ≠ 0 := fun hw_eq => by
    rw [hw_eq, zero_sub, norm_neg, norm_one] at hw
    linarith
  have h_zw : ‖z - w‖ ≤ 1 / 2 := by
    calc ‖z - w‖ = ‖(z - 1) - (w - 1)‖ := by congr 1; ring
      _ ≤ ‖z - 1‖ + ‖w - 1‖ := norm_sub_le _ _
      _ ≤ 1 / 4 + 1 / 4 := add_le_add hz hw
      _ = 1 / 2 := by ring
  have hw_norm_ge : (3 : ℝ) / 4 ≤ ‖w‖ := by
    have h_sub_nn := norm_sub_norm_le (1 : ℂ) w
    rw [show ((1 : ℂ) - w) = -(w - 1) from by ring, norm_neg, norm_one] at h_sub_nn
    linarith
  have hw_pos : 0 < ‖w‖ := by linarith
  have h_diff_norm : ‖z / w - 1‖ < 1 := by
    rw [show z / w - 1 = (z - w) / w from by field_simp, norm_div, div_lt_iff₀ hw_pos]
    nlinarith
  exact Complex.ball_one_subset_slitPlane (by simpa [Metric.mem_ball, dist_eq_norm]
    using h_diff_norm)

/-- Multiplication by a positive real preserves membership in `Complex.slitPlane`. -/
private theorem ofReal_pos_mul_mem_slitPlane {c : ℝ} (hc : 0 < c) {z : ℂ}
    (hz : z ∈ Complex.slitPlane) : ((c : ℝ) : ℂ) * z ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff] at hz ⊢
  rcases hz with h_re | h_im
  · exact Or.inl <| by simpa using mul_pos hc h_re
  · exact Or.inr <| by simpa using mul_ne_zero hc.ne' h_im

/-- **Chord quotient in the slit plane (algebraic core).** If the normalized chords at `a` and
`b` are `1/4`-close to `1` and `a`, `b` lie on a common side of `t₀` — so that
`(b - t₀) / (a - t₀) > 0` — then `(γ b - s) / (γ a - s) ∈ Complex.slitPlane`. -/
theorem chord_quotient_mem_slitPlane (hL : L ≠ 0) {a b : ℝ}
    (ha : ‖(γ a - s) / (L * ((a - t₀ : ℝ) : ℂ)) - 1‖ ≤ 1 / 4)
    (hb : ‖(γ b - s) / (L * ((b - t₀ : ℝ) : ℂ)) - 1‖ ≤ 1 / 4) (hab : 0 < (b - t₀) / (a - t₀)) :
    (γ b - s) / (γ a - s) ∈ Complex.slitPlane := by
  have ha_ne : (a - t₀ : ℝ) ≠ 0 := fun h => by simp [h] at hab
  have hb_ne : (b - t₀ : ℝ) ≠ 0 := fun h => by simp [h] at hab
  have hL_a : L * ((a - t₀ : ℝ) : ℂ) ≠ 0 :=
    mul_ne_zero hL (Complex.ofReal_ne_zero.mpr ha_ne)
  have hL_b : L * ((b - t₀ : ℝ) : ℂ) ≠ 0 :=
    mul_ne_zero hL (Complex.ofReal_ne_zero.mpr hb_ne)
  set z := (γ b - s) / (L * ((b - t₀ : ℝ) : ℂ)) with hz
  set w := (γ a - s) / (L * ((a - t₀ : ℝ) : ℂ)) with hw
  have h_ratio : (γ b - s) / (γ a - s) =
      (((b - t₀) / (a - t₀) : ℝ) : ℂ) * (z / w) := by
    rw [show (γ b - s) / (γ a - s) =
        (z * (L * ((b - t₀ : ℝ) : ℂ))) / (w * (L * ((a - t₀ : ℝ) : ℂ))) from by
      congr 1
      · simp only [z]
        exact (div_mul_cancel₀ _ hL_b).symm
      · simp only [w]
        exact (div_mul_cancel₀ _ hL_a).symm]
    push_cast
    field_simp
  rw [h_ratio]
  exact ofReal_pos_mul_mem_slitPlane hab (div_mem_slitPlane_of_close_to_one hb ha)

/-- **Chord quotients on a small right interval lie in the slit plane**: there is `r > 0` such
that `(γ b - s) / (γ a - s) ∈ Complex.slitPlane` whenever `t₀ < a ≤ b ≤ t₀ + r`. -/
theorem exists_chord_quotient_mem_slitPlane_right
    (h_deriv : HasDerivWithinAt γ L (Ioi t₀) t₀) (h_at : γ t₀ = s) (hL : L ≠ 0) :
    ∃ r > 0, ∀ a b, t₀ < a → a ≤ b → b ≤ t₀ + r →
      (γ b - s) / (γ a - s) ∈ Complex.slitPlane := by
  obtain ⟨r, hr_pos, hr_close⟩ :=
    exists_normalized_chord_bound_right h_deriv h_at hL (ρ := 1 / 4) (by norm_num)
  refine ⟨r, hr_pos, fun a b ha hab hb => ?_⟩
  exact chord_quotient_mem_slitPlane hL (hr_close a ⟨ha, by linarith⟩)
    (hr_close b ⟨by linarith, hb⟩) (div_pos (by linarith) (by linarith))

/-- **Chord quotients on a small left interval lie in the slit plane**: there is `r > 0` such
that `(γ b - s) / (γ a - s) ∈ Complex.slitPlane` whenever `t₀ - r ≤ a ≤ b < t₀`. Stated with
`a` the left endpoint — the form in which the argument-lift fundamental theorem of calculus
consumes it on the left excised piece. -/
theorem exists_chord_quotient_mem_slitPlane_left
    (h_deriv : HasDerivWithinAt γ L (Iio t₀) t₀) (h_at : γ t₀ = s) (hL : L ≠ 0) :
    ∃ r > 0, ∀ a b, t₀ - r ≤ a → a ≤ b → b < t₀ →
      (γ b - s) / (γ a - s) ∈ Complex.slitPlane := by
  obtain ⟨r, hr_pos, hr_close⟩ :=
    exists_normalized_chord_bound_left h_deriv h_at hL (ρ := 1 / 4) (by norm_num)
  refine ⟨r, hr_pos, fun a b ha hab hb => ?_⟩
  exact chord_quotient_mem_slitPlane hL (hr_close a ⟨ha, by linarith⟩)
    (hr_close b ⟨by linarith, hb⟩)
    (div_pos_of_neg_of_neg (by linarith) (by linarith))

/-- **Positive real scaling does not move the argument**: if `Q ∈ slitPlane`, `c ε > 0`
eventually, and `(c ε : ℂ) * f ε → Q`, then `arg (f ε) → arg Q`. -/
theorem arg_tendsto_of_pos_mul_tendsto {α : Type*} {l : Filter α} {c : α → ℝ} {f : α → ℂ}
    {Q : ℂ} (hQ : Q ∈ Complex.slitPlane) (hc : ∀ᶠ ε in l, 0 < c ε)
    (h : Tendsto (fun ε => ((c ε : ℝ) : ℂ) * f ε) l (𝓝 Q)) :
    Tendsto (fun ε => (f ε).arg) l (𝓝 Q.arg) := by
  refine ((Complex.continuousAt_arg hQ).tendsto.comp h).congr' ?_
  filter_upwards [hc] with ε hε
  exact Complex.arg_real_mul _ hε

/-- **Right annular quotient argument convergence**: along a positive cutoff `δ(ε) → 0⁺`, the
argument of the annular quotient `(γ (t₀ + r) - s) / (γ (t₀ + δ ε) - s)` converges to the
argument of `(γ (t₀ + r) - s) / L`. -/
theorem arg_annular_quotient_tendsto_right
    (h_deriv : HasDerivWithinAt γ L (Ioi t₀) t₀) (h_at : γ t₀ = s) {δ : ℝ → ℝ} {r : ℝ}
    (h_slit : (γ (t₀ + r) - s) / L ∈ Complex.slitPlane) (hδ_pos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < δ ε)
    (hδ_to_zero : Tendsto δ (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ))) :
    Tendsto (fun ε : ℝ => Complex.arg ((γ (t₀ + r) - s) / (γ (t₀ + δ ε) - s)))
      (𝓝[>] (0 : ℝ)) (𝓝 ((γ (t₀ + r) - s) / L).arg) := by
  have hL : L ≠ 0 := fun h0 => by
    rw [h0, div_zero] at h_slit
    exact Complex.zero_notMem_slitPlane h_slit
  have h_compose : Tendsto (fun ε : ℝ => t₀ + δ ε) (𝓝[>] (0 : ℝ)) (𝓝[>] t₀) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, hδ_pos.mono fun ε hε => by simpa using hε⟩
    simpa using tendsto_const_nhds.add
      (hδ_to_zero.mono_right nhdsWithin_le_nhds : Tendsto δ (𝓝[>] (0 : ℝ)) (𝓝 0))
  have h_chord : Tendsto (fun ε : ℝ => (γ (t₀ + δ ε) - s) / ((δ ε : ℝ) : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 L) :=
    ((chord_quotient_tendsto self_notMem_Ioi h_deriv h_at).comp h_compose).congr
      fun ε => by simp [Function.comp_apply, add_sub_cancel_left]
  refine arg_tendsto_of_pos_mul_tendsto h_slit hδ_pos ?_
  have h_recip := (h_chord.inv₀ hL).const_mul (γ (t₀ + r) - s)
  rw [← div_eq_mul_inv] at h_recip
  exact h_recip.congr fun ε => by rw [inv_div]; ring

/-- **Left annular quotient argument convergence**: along a positive cutoff `δ(ε) → 0⁺`, the
argument of the annular quotient `(γ (t₀ - δ ε) - s) / (γ (t₀ - r) - s)` converges to the
argument of `(-L) / (γ (t₀ - r) - s)`. -/
theorem arg_annular_quotient_tendsto_left
    (h_deriv : HasDerivWithinAt γ L (Iio t₀) t₀) (h_at : γ t₀ = s) {δ : ℝ → ℝ} {r : ℝ}
    (h_slit : (-L) / (γ (t₀ - r) - s) ∈ Complex.slitPlane) (hδ_pos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < δ ε)
    (hδ_to_zero : Tendsto δ (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ))) :
    Tendsto (fun ε : ℝ => Complex.arg ((γ (t₀ - δ ε) - s) / (γ (t₀ - r) - s)))
      (𝓝[>] (0 : ℝ)) (𝓝 ((-L) / (γ (t₀ - r) - s)).arg) := by
  have h_compose : Tendsto (fun ε : ℝ => t₀ - δ ε) (𝓝[>] (0 : ℝ)) (𝓝[<] t₀) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, hδ_pos.mono fun ε hε => by simpa using hε⟩
    simpa using tendsto_const_nhds.sub
      (hδ_to_zero.mono_right nhdsWithin_le_nhds : Tendsto δ (𝓝[>] (0 : ℝ)) (𝓝 0))
  have h_chord : Tendsto (fun ε : ℝ => (γ (t₀ - δ ε) - s) / ((δ ε : ℝ) : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 (-L)) :=
    ((chord_quotient_tendsto self_notMem_Iio h_deriv h_at).comp h_compose).neg.congr
      fun ε => by
        simp only [Function.comp_apply]
        rw [show t₀ - δ ε - t₀ = -δ ε from by ring, Complex.ofReal_neg, div_neg, neg_neg]
  refine arg_tendsto_of_pos_mul_tendsto h_slit
    (hδ_pos.mono fun ε hε => inv_pos.mpr hε) ?_
  refine (h_chord.div_const (γ (t₀ - r) - s)).congr fun ε => ?_
  push_cast
  ring

/-- For `q` with `‖-q - 1‖ ≤ 1/4`, the negated inverse `-1/q` lies in the slit plane: the
`z = 1`, `w = -q` instance of `div_mem_slitPlane_of_close_to_one`. -/
private theorem neg_inv_mem_slitPlane_of_neg_close_to_one {q : ℂ} (hq : ‖-q - 1‖ ≤ 1 / 4) :
    -1 / q ∈ Complex.slitPlane := by
  have h := div_mem_slitPlane_of_close_to_one (z := 1) (w := -q) (by norm_num) hq
  rwa [div_neg, ← neg_div] at h

/-- **Boundary chord-to-tangent quotients in the slit plane (right)**: there is a window radius
`r > 0` such that `(γ (t₀ + r') - s) / L ∈ Complex.slitPlane` for every `0 < r' ≤ r` — the
`h_slit` input of `arg_annular_quotient_tendsto_right` at any admissible window radius. -/
theorem exists_chord_div_tangent_mem_slitPlane_right
    (h_deriv : HasDerivWithinAt γ L (Ioi t₀) t₀) (h_at : γ t₀ = s) (hL : L ≠ 0) :
    ∃ r > 0, ∀ r', 0 < r' → r' ≤ r → (γ (t₀ + r') - s) / L ∈ Complex.slitPlane := by
  obtain ⟨r, hr_pos, hr_close⟩ :=
    exists_normalized_chord_bound_right h_deriv h_at hL (ρ := 1 / 4) (by norm_num)
  refine ⟨r, hr_pos, fun r' hr'_pos hr'_le => ?_⟩
  have h_close : ‖(γ (t₀ + r') - s) / (L * ((r' : ℝ) : ℂ)) - 1‖ ≤ 1 / 4 := by
    rw [show ((r' : ℝ) : ℂ) = (((t₀ + r') - t₀ : ℝ) : ℂ) from by push_cast; ring]
    exact hr_close (t₀ + r') ⟨by linarith, by linarith⟩
  have h_div_eq : (γ (t₀ + r') - s) / L =
      ((r' : ℝ) : ℂ) * ((γ (t₀ + r') - s) / (L * ((r' : ℝ) : ℂ))) := by
    have hr'_ne : ((r' : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr'_pos.ne'
    field_simp
  rw [h_div_eq]
  refine ofReal_pos_mul_mem_slitPlane hr'_pos (Complex.ball_one_subset_slitPlane ?_)
  rw [Metric.mem_ball, dist_eq_norm]
  linarith

/-- **Boundary chord-to-tangent quotients in the slit plane (left)**: there is a window radius
`r > 0` such that `(-L) / (γ (t₀ - r') - s) ∈ Complex.slitPlane` for every `0 < r' ≤ r` — the
`h_slit` input of `arg_annular_quotient_tendsto_left` at any admissible window radius. -/
theorem exists_neg_tangent_div_chord_mem_slitPlane_left
    (h_deriv : HasDerivWithinAt γ L (Iio t₀) t₀) (h_at : γ t₀ = s) (hL : L ≠ 0) :
    ∃ r > 0, ∀ r', 0 < r' → r' ≤ r →
      (-L) / (γ (t₀ - r') - s) ∈ Complex.slitPlane := by
  obtain ⟨r, hr_pos, hr_close⟩ :=
    exists_normalized_chord_bound_left h_deriv h_at hL (ρ := 1 / 4) (by norm_num)
  refine ⟨r, hr_pos, fun r' hr'_pos hr'_le => ?_⟩
  set q : ℂ := (γ (t₀ - r') - s) / (L * ((r' : ℝ) : ℂ)) with hq_def
  have hq_close : ‖-q - 1‖ ≤ 1 / 4 := by
    have h_close := hr_close (t₀ - r') ⟨by linarith, by linarith⟩
    rw [show (((t₀ - r') - t₀ : ℝ) : ℂ) = -((r' : ℝ) : ℂ) from by push_cast; ring, mul_neg,
      div_neg, ← hq_def] at h_close
    exact h_close
  have hq_ne : q ≠ 0 := by
    intro h0
    rw [h0, neg_zero, zero_sub, norm_neg, norm_one] at hq_close
    norm_num at hq_close
  have h_γ_ne : γ (t₀ - r') - s ≠ 0 := fun h0 => hq_ne (by rw [hq_def, h0, zero_div])
  have h_eq_target : (-L) / (γ (t₀ - r') - s) = (((1 / r' : ℝ)) : ℂ) * (-1 / q) := by
    have hr'_ne : ((r' : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr'_pos.ne'
    rw [hq_def]
    push_cast
    field_simp
  rw [h_eq_target]
  exact ofReal_pos_mul_mem_slitPlane (by positivity)
    (neg_inv_mem_slitPlane_of_neg_close_to_one hq_close)

/-- **The per-crossing slit-plane radius package**: at a transverse crossing with non-zero
one-sided derivatives, a single radius `r > 0` carries all four slit-plane properties — the
two-sided chord quotients and the two boundary tangent quotients at every admissible offset —
so a common minimum over the crossings of a pole inherits them all. -/
theorem exists_crossing_slitPlane_radius {γ : ℝ → ℂ} {t₀ : ℝ} {s L_R L_L : ℂ}
    (h_deriv_R : HasDerivWithinAt γ L_R (Ioi t₀) t₀)
    (h_deriv_L : HasDerivWithinAt γ L_L (Iio t₀) t₀)
    (h_at : γ t₀ = s) (hL_R : L_R ≠ 0) (hL_L : L_L ≠ 0) :
    ∃ r > 0,
      (∀ a b, t₀ < a → a ≤ b → b ≤ t₀ + r →
        (γ b - s) / (γ a - s) ∈ Complex.slitPlane) ∧
      (∀ a b, t₀ - r ≤ a → a ≤ b → b < t₀ →
        (γ b - s) / (γ a - s) ∈ Complex.slitPlane) ∧
      (∀ r', 0 < r' → r' ≤ r → (γ (t₀ + r') - s) / L_R ∈ Complex.slitPlane) ∧
      (∀ r', 0 < r' → r' ≤ r → (-L_L) / (γ (t₀ - r') - s) ∈ Complex.slitPlane) := by
  obtain ⟨r₁, hr₁_pos, h₁⟩ := exists_chord_quotient_mem_slitPlane_right h_deriv_R h_at hL_R
  obtain ⟨r₂, hr₂_pos, h₂⟩ := exists_chord_quotient_mem_slitPlane_left h_deriv_L h_at hL_L
  obtain ⟨r₃, hr₃_pos, h₃⟩ := exists_chord_div_tangent_mem_slitPlane_right h_deriv_R h_at hL_R
  obtain ⟨r₄, hr₄_pos, h₄⟩ :=
    exists_neg_tangent_div_chord_mem_slitPlane_left h_deriv_L h_at hL_L
  have hr₁ : min (min r₁ r₂) (min r₃ r₄) ≤ r₁ := (min_le_left _ _).trans (min_le_left _ _)
  have hr₂ : min (min r₁ r₂) (min r₃ r₄) ≤ r₂ := (min_le_left _ _).trans (min_le_right _ _)
  have hr₃ : min (min r₁ r₂) (min r₃ r₄) ≤ r₃ := (min_le_right _ _).trans (min_le_left _ _)
  have hr₄ : min (min r₁ r₂) (min r₃ r₄) ≤ r₄ := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨min (min r₁ r₂) (min r₃ r₄),
    lt_min (lt_min hr₁_pos hr₂_pos) (lt_min hr₃_pos hr₄_pos), ?_, ?_, ?_, ?_⟩
  · exact fun a b ha hab hb => h₁ a b ha hab (by linarith)
  · exact fun a b ha hab hb => h₂ a b (by linarith) hab hb
  · exact fun r' hr' hle => h₃ r' hr' (hle.trans hr₃)
  · exact fun r' hr' hle => h₄ r' hr' (hle.trans hr₄)

end TauCeti.Contour

end
