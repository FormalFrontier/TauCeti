/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Topology.UnitInterval
import TauCeti.Analysis.Contour.Curve.Distance

/-!
# Continuous argument lift for a point-avoiding curve

For a curve `γ : ℝ → ℂ` continuous on `[a, b]` and avoiding a point `w`, the function
`t ↦ γ t - w` is nowhere zero there, so on `[a, b]` it admits a real-valued *argument lift* `θ`,
continuous on `[a, b]`, with `γ t - w = ‖γ t - w‖ · exp (i θ t)` for `t ∈ [a, b]`. This is the
geometric heart of the integer-valuedness of the generalized winding number: for a closed
curve the total argument change `θ b - θ a` is an integer multiple of `2π`.

The lift is built on a partition `a = s₀ ≤ ⋯ ≤ s_N = b` fine enough that each segment ratio
`(γ t - w) / (γ (s j) - w)` stays within distance `1/2` of `1`, hence in `Complex.slitPlane`, where
`Complex.log` extracts a single-valued argument; the segment contributions telescope to the global
lift.

Mathlib's `Complex.exists_continuousOn_eqOn_exp_comp` already gives a continuous logarithm (hence
argument) branch for a nowhere-zero continuous function on a simply connected open set. The explicit
partition-and-`segRatio` construction here is retained because the downstream winding-number
integral is evaluated segment by segment, which needs the partition data that the bare-existence
API does not expose.

## Main results

* `TauCeti.Contour.exists_continuousOn_arg_lift_with_partition` — a real argument lift, continuous
  on `[a, b]`, for a curve continuous there and avoiding `w`, plus a monotone partition witness.
* `TauCeti.Contour.segRatio` and its evaluation lemmas — the segment-ratio building block used to
  assemble the index integral downstream.
* `TauCeti.Contour.div_norm_eq_exp_arg_mul_I` — the unit direction of a nonzero complex number
  in polar form, shared with the sector-resonance bridges.

## Provenance

Adapted from `WindingInteger.lean` in the AINTLIB `LeanModularForms` development. Prerequisite for
the integer-valuedness and local constancy of the generalized winding number, hence for the homology
Cauchy theorem (roadmap `homologyCauchyTheorem`) and the generalized residue theorem.
-/

public section

noncomputable section

open Set

namespace TauCeti.Contour


/-! ### Partition lemma -/

/-- For a continuous function `γ : ℝ → ℂ` avoiding `w` on a compact interval, there
exists `δ > 0` such that on any sub-interval of length `< δ`, `γ` varies by less than
half the minimum distance to `w`. This gives a partition where each segment of
`γ - w` lies in a ball avoiding `0`. -/
private theorem exists_uniform_modulus_avoiding {γ : ℝ → ℂ} {w : ℂ} {a b : ℝ} (hab : a ≤ b)
    (hγ : ContinuousOn γ (Icc a b))
    (h_avoid : ∀ t ∈ Icc a b, γ t ≠ w) :
    ∃ δ' > 0, ∃ ρ > 0, (∀ t ∈ Icc a b, ρ ≤ ‖γ t - w‖) ∧
      ∀ t s, t ∈ Icc a b → s ∈ Icc a b → |t - s| < δ' →
        ‖γ t - γ s‖ < ρ / 2 := by
  -- Step 1: positive lower bound ρ for ‖γ t - w‖ (distance from `w` to the curve image)
  obtain ⟨ρ, hρ_pos, h_dist_lb⟩ := exists_curve_dist_lower_bound
    (by rw [Set.uIcc_of_le hab]; exact hγ) (by rw [Set.uIcc_of_le hab]; exact h_avoid)
  rw [Set.uIcc_of_le hab] at h_dist_lb
  -- Step 2: by uniform continuity on compact, get δ' for variation < ρ/2
  have h_unif : UniformContinuousOn γ (Icc a b) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hγ
  rw [Metric.uniformContinuousOn_iff] at h_unif
  obtain ⟨δ', hδ'_pos, h_unif⟩ := h_unif (ρ / 2) (by linarith)
  refine ⟨δ', hδ'_pos, ρ, hρ_pos, h_dist_lb, ?_⟩
  intro t s ht hs h_dist
  rw [← Complex.dist_eq]
  exact h_unif t ht s hs (by rwa [Real.dist_eq])

/-! ### Segment-ratio helpers

The continuous argument lift below is assembled from a partition of `[a, b]`: on each segment the
ratio `(γ t - w) / (γ (s j) - w)` lies within distance `1/2` of `1`, hence in `Complex.slitPlane`
(via Mathlib's `Complex.ball_one_subset_slitPlane`), where `Complex.log` extracts a single-valued
argument; the `Im (log ·)` contributions telescope across the partition. The definitions and lemmas
supporting that construction follow. -/

/-- Helper: clamp `t` to `[s_j, s_{j+1}]`. For partition segment `j`. -/
private def segClamp (s_j s_jp1 t : ℝ) : ℝ := max s_j (min t s_jp1)

@[fun_prop]
private theorem segClamp_continuous (s_j s_jp1 : ℝ) :
    Continuous (segClamp s_j s_jp1) :=
  continuous_const.max (continuous_id.min continuous_const)

private theorem segClamp_mem_Icc (s_j s_jp1 t : ℝ) (h : s_j ≤ s_jp1) :
    segClamp s_j s_jp1 t ∈ Icc s_j s_jp1 := by
  refine ⟨le_max_left _ _, ?_⟩
  unfold segClamp
  rcases le_total t s_jp1 with ht | ht
  · simpa [min_eq_left ht] using max_le h ht
  · rw [min_eq_right ht, max_le_iff]; exact ⟨h, le_rfl⟩

private theorem segClamp_eq_left {s_j s_jp1 t : ℝ} (ht : t ≤ s_j) :
    segClamp s_j s_jp1 t = s_j := by
  rw [segClamp, max_eq_left ((min_le_left t s_jp1).trans ht)]

private theorem segClamp_eq_self {s_j s_jp1 t : ℝ} (ht_lo : s_j ≤ t) (ht_hi : t ≤ s_jp1) :
    segClamp s_j s_jp1 t = t := by
  rw [segClamp, min_eq_left ht_hi, max_eq_right ht_lo]

private theorem segClamp_eq_right {s_j s_jp1 t : ℝ} (h : s_j ≤ s_jp1) (ht : s_jp1 ≤ t) :
    segClamp s_j s_jp1 t = s_jp1 := by
  rw [segClamp, min_eq_right ht, max_eq_right h]

/-- The **segment ratio** `(γ (segClamp s_j s_jp1 t) - w) / (γ s_j - w)`: on the partition segment
`[s_j, s_{j+1}]` it measures `γ t - w` against its value at the left endpoint `s_j`, held constant
in `t` outside the segment. Summing the `Complex.log`s of these ratios over a partition yields a
continuous argument lift of `t ↦ γ t - w`. -/
noncomputable def segRatio (γ : ℝ → ℂ) (w : ℂ) (s_j s_jp1 t : ℝ) : ℂ :=
  (γ (segClamp s_j s_jp1 t) - w) / (γ s_j - w)

/-- Before its segment (`t ≤ s_j`), the segment ratio equals `1`. -/
theorem segRatio_eq_one_of_le {γ : ℝ → ℂ} {w : ℂ} {s_j s_jp1 t : ℝ}
    (ht : t ≤ s_j) (h_ne : γ s_j - w ≠ 0) :
    segRatio γ w s_j s_jp1 t = 1 := by
  rw [segRatio, segClamp_eq_left ht, div_self h_ne]

/-- On its segment (`t ∈ [s_j, s_{j+1}]`), the segment ratio is `(γ t - w) / (γ s_j - w)` — the
primary meaning of `segRatio`. -/
theorem segRatio_eq_div_of_mem_Icc {γ : ℝ → ℂ} {w : ℂ} {s_j s_jp1 t : ℝ}
    (ht : t ∈ Set.Icc s_j s_jp1) :
    segRatio γ w s_j s_jp1 t = (γ t - w) / (γ s_j - w) := by
  rw [segRatio, segClamp_eq_self ht.1 ht.2]

/-- After its segment (`s_{j+1} ≤ t`), the segment ratio equals the full endpoint ratio
`(γ s_{j+1} - w) / (γ s_j - w)`. -/
theorem segRatio_eq_endpoint_div_of_le {γ : ℝ → ℂ} {w : ℂ} {s_j s_jp1 t : ℝ}
    (h : s_j ≤ s_jp1) (ht : s_jp1 ≤ t) :
    segRatio γ w s_j s_jp1 t = (γ s_jp1 - w) / (γ s_j - w) := by
  rw [segRatio, segClamp_eq_right h ht]

/-- For partition with mesh < δ' and segments [s_j, s_{j+1}] of length ≤ mesh,
on the j-th segment, `γ(clamp t) - γ s_j` is small, so `segRatio j t ∈ ball(1, 1/2)`. -/
private theorem segRatio_mem_ball_one
    {γ : ℝ → ℂ} {w : ℂ} {a b δ' ρ : ℝ} (hρ_pos : 0 < ρ)
    (h_dist_lb : ∀ t ∈ Icc a b, ρ ≤ ‖γ t - w‖)
    (h_unif : ∀ t s : ℝ, t ∈ Icc a b → s ∈ Icc a b →
      |t - s| < δ' → ‖γ t - γ s‖ < ρ / 2)
    {s_j s_jp1 : ℝ} (hsj : s_j ∈ Icc a b) (hsjp1 : s_jp1 ∈ Icc a b)
    (h_le : s_j ≤ s_jp1) (h_mesh : s_jp1 - s_j < δ') (t : ℝ) :
    ‖segRatio γ w s_j s_jp1 t - 1‖ < 1 / 2 := by
  have h_clamp_mem : segClamp s_j s_jp1 t ∈ Icc s_j s_jp1 :=
    segClamp_mem_Icc s_j s_jp1 t h_le
  have h_clamp_in : segClamp s_j s_jp1 t ∈ Icc a b :=
    ⟨hsj.1.trans h_clamp_mem.1, h_clamp_mem.2.trans hsjp1.2⟩
  have h_dist : |segClamp s_j s_jp1 t - s_j| < δ' := by
    have h_nn : 0 ≤ segClamp s_j s_jp1 t - s_j := by linarith [h_clamp_mem.1]
    rw [abs_of_nonneg h_nn]; linarith [h_clamp_mem.2]
  have h_lb : ρ ≤ ‖γ s_j - w‖ := h_dist_lb _ hsj
  have h_pos : 0 < ‖γ s_j - w‖ := hρ_pos.trans_le h_lb
  have h_ne : γ s_j - w ≠ 0 := norm_pos_iff.mp h_pos
  unfold segRatio
  have h_rewrite : (γ (segClamp s_j s_jp1 t) - w) / (γ s_j - w) - 1 =
      (γ (segClamp s_j s_jp1 t) - γ s_j) / (γ s_j - w) := by
    rw [div_sub_one h_ne, sub_sub_sub_cancel_right]
  rw [h_rewrite, norm_div, div_lt_iff₀ h_pos]
  calc ‖γ (segClamp s_j s_jp1 t) - γ s_j‖
      < ρ / 2 := h_unif _ _ h_clamp_in hsj h_dist
    _ ≤ ‖γ s_j - w‖ / 2 := by linarith
    _ = 1 / 2 * ‖γ s_j - w‖ := by ring

/-- Continuity of `t ↦ segRatio γ w s_j s_jp1 t` on `Icc a b`. -/
private theorem continuousOn_segRatio {γ : ℝ → ℂ} {a b : ℝ} (hγ : ContinuousOn γ (Icc a b))
    {w : ℂ} {s_j s_jp1 : ℝ} (hsj : s_j ∈ Icc a b)
    (hsjp1 : s_jp1 ∈ Icc a b) (h_le : s_j ≤ s_jp1) :
    ContinuousOn (fun t ↦ segRatio γ w s_j s_jp1 t) (Icc a b) := by
  unfold segRatio
  refine ContinuousOn.div_const ?_ _
  refine ContinuousOn.sub ?_ continuousOn_const
  refine hγ.comp (segClamp_continuous s_j s_jp1).continuousOn ?_
  intro t _
  exact ⟨hsj.1.trans (segClamp_mem_Icc s_j s_jp1 t h_le).1,
    (segClamp_mem_Icc s_j s_jp1 t h_le).2.trans hsjp1.2⟩

/-- Combined: for partition with mesh < δ', `segRatio j t ∈ slitPlane`. -/
private theorem segRatio_mem_slitPlane
    {γ : ℝ → ℂ} {w : ℂ} {a b δ' ρ : ℝ} (hρ_pos : 0 < ρ)
    (h_dist_lb : ∀ t ∈ Icc a b, ρ ≤ ‖γ t - w‖)
    (h_unif : ∀ t s : ℝ, t ∈ Icc a b → s ∈ Icc a b →
      |t - s| < δ' → ‖γ t - γ s‖ < ρ / 2)
    {s_j s_jp1 : ℝ} (hsj : s_j ∈ Icc a b) (hsjp1 : s_jp1 ∈ Icc a b)
    (h_le : s_j ≤ s_jp1) (h_mesh : s_jp1 - s_j < δ') (t : ℝ) :
    segRatio γ w s_j s_jp1 t ∈ Complex.slitPlane :=
  Complex.ball_one_subset_slitPlane <| by
    rw [Metric.mem_ball, Complex.dist_eq]
    exact (segRatio_mem_ball_one hρ_pos h_dist_lb h_unif hsj hsjp1 h_le h_mesh t).trans
      (by norm_num)

/-! ### Telescoping product over a partition -/

/-- Telescoping product in `ℂ` over `Finset.range`. For `a : ℕ → ℂ` nonzero on indices `0..k`,
`∏ j ∈ range k, a (j+1)/a j = a k / a 0`. The nonzero-field analogue of the group telescoping lemma
`Finset.prod_range_div`, obtained from it by lifting the nonzero values into `ℂˣ`. -/
private lemma prod_range_div_complex (a : ℕ → ℂ) (k : ℕ)
    (ha : ∀ j ≤ k, a j ≠ 0) :
    ∏ j ∈ Finset.range k, (a (j + 1) / a j) = a k / a 0 := by
  classical
  set u : ℕ → ℂˣ := fun j ↦ if h : a j = 0 then 1 else Units.mk0 (a j) h with hu_def
  have hu : ∀ j ≤ k, (u j : ℂ) = a j := by
    intro j hj; simp only [hu_def, dif_neg (ha j hj), Units.val_mk0]
  have hstep : ∏ j ∈ Finset.range k, (a (j + 1) / a j)
      = ((∏ j ∈ Finset.range k, u (j + 1) / u j : ℂˣ) : ℂ) := by
    rw [Units.coe_prod]
    refine Finset.prod_congr rfl fun j hj ↦ ?_
    rw [Finset.mem_range] at hj
    rw [Units.val_div_eq_div_val, hu (j + 1) hj, hu j hj.le]
  rw [hstep, Finset.prod_range_div u k, Units.val_div_eq_div_val, hu k le_rfl,
    hu 0 (Nat.zero_le k)]

/-- Telescoping product: for `t ∈ [s_k, s_{k+1}]` along a monotone partition
`s : ℕ → ℝ` with `γ(s_j) ≠ w` for `0 ≤ j ≤ N`, the product
`∏_{j < N} segRatio γ w (s j) (s (j+1)) t` collapses to `(γ t - w) / (γ (s 0) - w)`.

This is the key identity making `Im(log)` of each `segRatio` add up to a
continuous argument lift of `t ↦ γ t - w`. -/
private theorem prod_segRatio_telescope
    {γ : ℝ → ℂ} {w : ℂ} {N : ℕ} {s : ℕ → ℝ}
    (hs_mono : Monotone s)
    (h_avoid : ∀ j ≤ N, γ (s j) - w ≠ 0)
    {t : ℝ} {k : ℕ} (hk : k < N) (hk_lo : s k ≤ t) (hk_hi : t ≤ s (k + 1)) :
    ∏ j ∈ Finset.range N, segRatio γ w (s j) (s (j + 1)) t = (γ t - w) / (γ (s 0) - w) := by
  -- Split range N = range (k+1) ∪ Ico (k+1) N
  rw [Finset.range_eq_Ico, ← Finset.prod_Ico_consecutive _ (Nat.zero_le (k + 1)) hk,
      ← Finset.range_eq_Ico]
  -- Tail Ico (k+1) N: each segRatio = 1
  have h_ico_eq_one : ∀ j ∈ Finset.Ico (k + 1) N,
      segRatio γ w (s j) (s (j + 1)) t = 1 := by
    intro j hj
    rw [Finset.mem_Ico] at hj
    refine segRatio_eq_one_of_le ?_ (h_avoid j hj.2.le)
    exact hk_hi.trans (hs_mono hj.1)
  rw [Finset.prod_congr rfl h_ico_eq_one, Finset.prod_const_one, mul_one]
  -- Peel off middle term j = k from range (k+1)
  rw [Finset.prod_range_succ]
  -- Range k: each segRatio = (γ s_{j+1} - w) / (γ s_j - w) (full ratio)
  have h_range_k_eq : ∀ j ∈ Finset.range k,
      segRatio γ w (s j) (s (j + 1)) t = (γ (s (j + 1)) - w) / (γ (s j) - w) := by
    intro j hj
    rw [Finset.mem_range] at hj
    refine segRatio_eq_endpoint_div_of_le (hs_mono (Nat.le_succ _)) ?_
    exact (hs_mono (Nat.succ_le_of_lt hj)).trans hk_lo
  rw [Finset.prod_congr rfl h_range_k_eq]
  -- Middle term: segRatio at index k = (γ t - w) / (γ s_k - w)
  rw [segRatio_eq_div_of_mem_Icc ⟨hk_lo, hk_hi⟩]
  -- Apply telescoping lemma to range k product
  rw [prod_range_div_complex (fun j ↦ γ (s j) - w) k
        (fun j hj ↦ h_avoid j (hj.trans hk.le))]
  -- Cancel γ s_k - w
  rw [div_mul_div_comm, mul_comm (γ (s k) - w) (γ t - w),
      mul_div_mul_right _ _ (h_avoid k hk.le)]

/-! ### Continuous arg-lift summand (continued) -/

/-- Each summand in the telescoping arg-lift sum is continuous. -/
private theorem continuousOn_im_log_segRatio {γ : ℝ → ℂ} {a b : ℝ}
    (hγ : ContinuousOn γ (Icc a b)) {w : ℂ} {δ' ρ : ℝ} (hρ_pos : 0 < ρ)
    (h_dist_lb : ∀ t ∈ Icc a b, ρ ≤ ‖γ t - w‖)
    (h_unif : ∀ t s : ℝ, t ∈ Icc a b → s ∈ Icc a b →
      |t - s| < δ' → ‖γ t - γ s‖ < ρ / 2)
    {s_j s_jp1 : ℝ} (hsj : s_j ∈ Icc a b) (hsjp1 : s_jp1 ∈ Icc a b)
    (h_le : s_j ≤ s_jp1) (h_mesh : s_jp1 - s_j < δ') :
    ContinuousOn (fun t ↦ (Complex.log (segRatio γ w s_j s_jp1 t)).im)
      (Icc a b) := by
  refine Complex.continuous_im.comp_continuousOn ?_
  exact (continuousOn_segRatio hγ hsj hsjp1 h_le).clog
    fun t _ ↦ segRatio_mem_slitPlane hρ_pos h_dist_lb h_unif hsj hsjp1 h_le h_mesh t

/-! ### The unit direction in polar form -/

/-- **A nonzero complex number over its norm is the exponential of its argument**:
`w / ↑‖w‖ = exp(arg w · I)`. -/
theorem div_norm_eq_exp_arg_mul_I {w : ℂ} (hw : w ≠ 0) :
    w / (‖w‖ : ℂ) = Complex.exp ((Complex.arg w : ℂ) * Complex.I) := by
  rw [div_eq_iff (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hw)), mul_comm]
  exact (Complex.norm_mul_exp_arg_mul_I w).symm

/-- For a nonzero complex number `z`, `exp(I · Im(log z)) = z / ↑‖z‖`. -/
private lemma exp_I_log_im_eq_div_norm {z : ℂ} (hz : z ≠ 0) :
    Complex.exp (Complex.I * ((Complex.log z).im : ℂ)) = z / (‖z‖ : ℂ) := by
  rw [Complex.log_im, mul_comm, ← div_norm_eq_exp_arg_mul_I hz]

/-! ### Polar form of a product -/

/-- If `z = z0 · ∏ zs j` with `z0` and each factor `zs j` nonzero, then
`z = ‖z‖ · exp (I · θ)` with `θ = arg z0 + ∑ Im (log (zs j))`: the arguments of the factors add
and the norms multiply out to `‖z‖`. This packages the argument bookkeeping of the continuous
lift, whose telescoped product `(γ a - w) · ∏ segRatio = γ t - w` has exactly this shape. -/
private lemma polar_form_of_prod {N : ℕ} {z0 : ℂ} {zs : ℕ → ℂ} {z : ℂ}
    (hz0 : z0 ≠ 0) (hzs : ∀ j ∈ Finset.range N, zs j ≠ 0)
    (hprod : z0 * ∏ j ∈ Finset.range N, zs j = z) :
    z = (‖z‖ : ℂ) * Complex.exp (Complex.I *
      ((Complex.arg z0 + ∑ j ∈ Finset.range N, (Complex.log (zs j)).im : ℝ) : ℂ)) := by
  have hz : z ≠ 0 := by
    rw [← hprod]; exact mul_ne_zero hz0 (Finset.prod_ne_zero_iff.mpr hzs)
  have h_theta_cast :
      ((Complex.arg z0 + ∑ j ∈ Finset.range N, (Complex.log (zs j)).im : ℝ) : ℂ) =
      (Complex.arg z0 : ℂ) + ∑ j ∈ Finset.range N, ((Complex.log (zs j)).im : ℂ) := by
    push_cast; rfl
  have h_exp_split :
      Complex.exp (Complex.I *
        ((Complex.arg z0 + ∑ j ∈ Finset.range N, (Complex.log (zs j)).im : ℝ) : ℂ)) =
      Complex.exp (Complex.I * (Complex.arg z0 : ℂ)) *
        ∏ j ∈ Finset.range N, Complex.exp (Complex.I * ((Complex.log (zs j)).im : ℂ)) := by
    rw [h_theta_cast, mul_add, Complex.exp_add, Finset.mul_sum, Complex.exp_sum]
  have h_arg : Complex.exp (Complex.I * (Complex.arg z0 : ℂ)) = z0 / ((‖z0‖ : ℝ) : ℂ) := by
    rw [← Complex.log_im z0]; exact exp_I_log_im_eq_div_norm hz0
  have h_z_eq : ∀ j ∈ Finset.range N,
      Complex.exp (Complex.I * ((Complex.log (zs j)).im : ℂ)) = zs j / ((‖zs j‖ : ℝ) : ℂ) :=
    fun j hj ↦ exp_I_log_im_eq_div_norm (hzs j hj)
  have h_norm_prod_real : (‖z0‖ : ℝ) * (∏ j ∈ Finset.range N, ‖zs j‖) = ‖z‖ := by
    rw [← Complex.norm_prod, ← norm_mul, hprod]
  have h_norm_ne : ((‖z‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)
  rw [h_exp_split, h_arg, Finset.prod_congr rfl h_z_eq, Finset.prod_div_distrib,
      div_mul_div_comm, ← Complex.ofReal_prod, ← Complex.ofReal_mul, h_norm_prod_real, hprod,
      mul_div_cancel₀ _ h_norm_ne]

/-! ### Covering segment -/

/-- On a monotone partition covering `[s 0, s N]`, every point `t` with `s 0 ≤ t ≤ s N` lies in
some segment `[s k, s (k+1)]` with `k < N`. -/
private lemma exists_covering_segment {N : ℕ} (hN : 0 < N) {s : ℕ → ℝ} (hmono : Monotone s)
    {t : ℝ} (h_lo : s 0 ≤ t) (h_hi : t ≤ s N) :
    ∃ k, k < N ∧ s k ≤ t ∧ t ≤ s (k + 1) := by
  classical
  set k := Nat.findGreatest (fun j ↦ s j ≤ t) N with hk_def
  have hk_le : k ≤ N := Nat.findGreatest_le N
  have hk_spec : s k ≤ t := Nat.findGreatest_spec (P := fun j ↦ s j ≤ t) (Nat.zero_le N) h_lo
  rcases lt_or_eq_of_le hk_le with hklt | hkN
  · refine ⟨k, hklt, hk_spec, ?_⟩
    by_contra h_con
    rw [not_le] at h_con
    have h := Nat.le_findGreatest (P := fun j ↦ s j ≤ t) hklt h_con.le
    rw [← hk_def] at h
    omega
  · obtain ⟨M, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
    refine ⟨M, ?_, ?_, h_hi⟩
    · omega
    · have hMk : M ≤ k := by omega
      exact (hmono hMk).trans hk_spec

/-! ### Uniform partition with bounded mesh -/

/-- **Monotone partition with mesh below `δ`.** For `a ≤ b` and `δ > 0`, the interval `[a, b]`
admits a monotone partition `a = s 0 ≤ ⋯ ≤ s N = b` with `N > 0` segments (so `N + 1` nodes), each
node in `[a, b]`, and every gap `s (j + 1) - s j` strictly below `δ`. Built from Mathlib's
fixed-step `Set.Icc.addNSMul` partition (step `δ / 2`, stabilising at `b`). -/
private theorem exists_monotone_partition_mesh_lt {a b δ : ℝ} (hab : a ≤ b) (hδ : 0 < δ) :
    ∃ (N : ℕ) (s : ℕ → ℝ), 0 < N ∧ s 0 = a ∧ s N = b ∧ Monotone s ∧
      (∀ j ≤ N, s j ∈ Icc a b) ∧ ∀ j, s (j + 1) - s j < δ := by
  have hδ2 : (0 : ℝ) < δ / 2 := half_pos hδ
  obtain ⟨m, hm⟩ := Set.Icc.addNSMul_eq_right hab hδ2
  refine ⟨m + 1, fun j => ↑(Set.Icc.addNSMul hab (δ / 2) j), m.succ_pos, ?_, ?_,
    fun i j hij => Subtype.coe_le_coe.mpr (Set.Icc.monotone_addNSMul hab hδ2.le hij),
    fun j _ => (Set.Icc.addNSMul hab (δ / 2) j).2, fun j => ?_⟩
  · exact Set.Icc.addNSMul_zero hab
  · exact hm (m + 1) (Nat.le_succ m)
  · -- gap `< δ`: the fixed step gives `≤ δ / 2` (Mathlib's `abs_sub_addNSMul_le`), and `δ / 2 < δ`.
    have hle : (Set.Icc.addNSMul hab (δ / 2) j : ℝ) ≤ Set.Icc.addNSMul hab (δ / 2) (j + 1) :=
      Subtype.coe_le_coe.mpr (Set.Icc.monotone_addNSMul hab hδ2.le (Nat.le_succ j))
    have hbd := Set.Icc.abs_sub_addNSMul_le hab hδ2.le
      (t := Set.Icc.addNSMul hab (δ / 2) (j + 1)) j
      ⟨Set.Icc.monotone_addNSMul hab hδ2.le (Nat.le_succ j), le_refl _⟩
    rw [abs_of_nonneg (by linarith)] at hbd
    linarith

/-! ### Main theorem: argument lift on `[a, b]` -/

/-- **Argument lift on `[a, b]`, with a partition.** For `γ` continuous on `[a, b]` (`a ≤ b`) and
avoiding `w`, there is a monotone partition `a = s 0 ≤ ⋯ ≤ s N = b` and a real function
`θ t = arg (γ a - w) + ∑_{j < N} (log (segRatio γ w (s j) (s (j+1)) t)).im`, continuous on `[a, b]`,
satisfying `γ t - w = ‖γ t - w‖ · exp (I · θ t)` there. Each node has `γ (s j) ≠ w`, and on each
segment `j` the ratio `(γ t - w) / (γ (s j) - w)` lies in `Complex.slitPlane`. -/
theorem exists_continuousOn_arg_lift_with_partition
    {γ : ℝ → ℂ} {w : ℂ} {a b : ℝ} (hab : a ≤ b)
    (hγ : ContinuousOn γ (Icc a b))
    (h_avoid : ∀ t ∈ Icc a b, γ t ≠ w) :
    ∃ (N : ℕ) (s : ℕ → ℝ),
      0 < N ∧ s 0 = a ∧ s N = b ∧ Monotone s ∧
      (∀ j ≤ N, s j ∈ Icc a b) ∧
      (∀ j ≤ N, γ (s j) - w ≠ 0) ∧
      (∀ j, j < N → ∀ t ∈ Icc (s j) (s (j + 1)),
        (γ t - w) / (γ (s j) - w) ∈ Complex.slitPlane) ∧
      ContinuousOn
        (fun t ↦ Complex.arg (γ a - w) +
          ∑ j ∈ Finset.range N, (Complex.log (segRatio γ w (s j) (s (j + 1)) t)).im)
        (Icc a b) ∧
      (∀ t ∈ Icc a b, γ t - w = (‖γ t - w‖ : ℂ) * Complex.exp (Complex.I *
        ((Complex.arg (γ a - w) +
          ∑ j ∈ Finset.range N,
            (Complex.log (segRatio γ w (s j) (s (j + 1)) t)).im : ℝ) : ℂ))) := by
  obtain ⟨δ', hδ'_pos, ρ, hρ_pos, h_dist_lb, h_unif⟩ :=
    exists_uniform_modulus_avoiding hab hγ h_avoid
  obtain ⟨N, s, hN_pos, hs_zero, hs_N, hs_mono, hs_in, hs_mesh⟩ :=
    exists_monotone_partition_mesh_lt hab hδ'_pos
  have hs_avoid : ∀ j ≤ N, γ (s j) - w ≠ 0 := fun j hj ↦
    sub_ne_zero.mpr (h_avoid (s j) (hs_in j hj))
  have hs_le : ∀ j, s j ≤ s (j + 1) := fun j ↦ hs_mono (Nat.le_succ _)
  have h_slit : ∀ j, j < N → ∀ t ∈ Icc (s j) (s (j + 1)),
      (γ t - w) / (γ (s j) - w) ∈ Complex.slitPlane := by
    intro j hj t ht
    rw [← segRatio_eq_div_of_mem_Icc ht]
    exact segRatio_mem_slitPlane hρ_pos h_dist_lb h_unif
      (hs_in j hj.le) (hs_in (j + 1) hj) (hs_le j) (hs_mesh j) t
  refine ⟨N, s, hN_pos, hs_zero, hs_N, hs_mono, hs_in, hs_avoid, h_slit, ?_, ?_⟩
  -- Continuity of θ
  · refine ContinuousOn.add continuousOn_const ?_
    refine continuousOn_finsetSum _ ?_
    intro j hj
    refine continuousOn_im_log_segRatio hγ hρ_pos h_dist_lb h_unif
      (hs_in j (Finset.mem_range.mp hj).le) (hs_in (j + 1) (Finset.mem_range.mp hj))
      (hs_le j) (hs_mesh j)
  -- Lift property
  · intro t ht
    have h_avoid_a : γ a - w ≠ 0 :=
      sub_ne_zero.mpr (h_avoid a ⟨le_rfl, hab⟩)
    have h_cov_lo : s 0 ≤ t := by rw [hs_zero]; exact ht.1
    have h_cov_hi : t ≤ s N := by rw [hs_N]; exact ht.2
    obtain ⟨k, hk_lt, hk_lo, hk_hi⟩ := exists_covering_segment hN_pos hs_mono h_cov_lo h_cov_hi
    have h_telescope := prod_segRatio_telescope hs_mono hs_avoid hk_lt hk_lo hk_hi
    rw [hs_zero] at h_telescope
    have h_ratio_ne : ∀ j ∈ Finset.range N,
        segRatio γ w (s j) (s (j + 1)) t ≠ 0 := fun j hj ↦
      Complex.slitPlane_ne_zero
        (segRatio_mem_slitPlane hρ_pos h_dist_lb h_unif
          (hs_in j (Finset.mem_range.mp hj).le)
          (hs_in (j + 1) (Finset.mem_range.mp hj))
          (hs_le j) (hs_mesh j) t)
    have h_prod_eq : (γ a - w) *
        ∏ j ∈ Finset.range N, segRatio γ w (s j) (s (j + 1)) t = γ t - w := by
      rw [h_telescope, mul_div_cancel₀ _ h_avoid_a]
    exact polar_form_of_prod (zs := fun j ↦ segRatio γ w (s j) (s (j + 1)) t)
      h_avoid_a h_ratio_ne h_prod_eq

end TauCeti.Contour

end
