/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# `dslope` as a parameter integral

For `f : ℂ → ℂ` differentiable on an open set and points `c, w` there, the divided slope
`dslope f c w` is a fundamental-theorem-of-calculus average of the derivative of `f` along the
segment `[c, w]` — on a convex set,

  `dslope f c w = ∫ t in 0..1, deriv f (c + t • (w - c))`.

The representation unifies the two branches of `dslope` (`deriv f c` at `c = w`, the slope
`(f w - f c) / (w - c)` otherwise) into a single integral that is manifestly continuous through the
diagonal. From it we read off the analytic inputs the Dixon homology Cauchy theorem needs about the
map `(c, w) ↦ dslope f c w`: joint continuity and a Cauchy bound on its `w`-derivative.

## Main results

* `TauCeti.dslope_eq_integral_deriv` — the integral representation on an open convex set.
* `TauCeti.continuousOn_dslope_prod` — joint continuity of `(c, w) ↦ dslope f c w` on `U ×ˢ U` for
  arbitrary open `U`.
* `TauCeti.continuousOn_dslope_first_arg` — continuity of `c ↦ dslope f c w₀` on open `U`.
* `TauCeti.deriv_dslope_bounded_on_compact` — a uniform bound on `‖deriv (dslope f c) w‖`
  for `c` in a compact subset of `U` and `w` near a point of `U`.

## Provenance

Adapted from `DslopeIntegral.lean` in the AINTLIB `LeanModularForms` development. Prerequisite for
the holomorphy of the Dixon `dslope` integral, hence for the homology Cauchy theorem and the
generalized residue theorem on the roadmap.
-/

public section

noncomputable section

namespace TauCeti

open Set MeasureTheory Filter Topology intervalIntegral

variable {f : ℂ → ℂ}

/-- The `dslope` integral representation on a convex open set: when `f` is
differentiable on `U` and both `c, w ∈ U` (so the segment `[c, w] ⊆ U`), then
`dslope f c w` equals the integral of the derivative of `f` along the segment. -/
theorem dslope_eq_integral_deriv {U : Set ℂ} (hU : Convex ℝ U) (hU_open : IsOpen U)
    (hf : DifferentiableOn ℂ f U) {c w : ℂ} (hc : c ∈ U) (hw : w ∈ U) :
    dslope f c w = ∫ t in (0 : ℝ)..1, deriv f (c + t • (w - c)) := by
  have h_seg : ∀ t ∈ Icc (0 : ℝ) 1, c + t • (w - c) ∈ U := fun t ht ↦ by
    rw [show c + t • (w - c) = (1 - t) • c + t • w by module]
    exact hU hc hw (by linarith [ht.2]) ht.1 (by linarith)
  have h_deriv : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt f (deriv f (c + t • (w - c))) (c + t • (w - c)) := fun t ht ↦
    ((hf (c + t • (w - c)) (h_seg t ht)).differentiableAt
      (hU_open.mem_nhds (h_seg t ht))).hasDerivAt
  have h_deriv_contU : ContinuousOn (deriv f) U :=
    (hf.analyticOnNhd hU_open).deriv.continuousOn
  have h_cont : ContinuousOn (fun t : ℝ ↦ deriv f (c + t • (w - c))) (Icc (0 : ℝ) 1) :=
    h_deriv_contU.comp (by continuity : Continuous _).continuousOn h_seg
  have h_int := integral_unitInterval_deriv_eq_sub h_cont h_deriv
  rw [show c + (w - c) = w by ring] at h_int
  by_cases hwc : w = c
  · subst hwc; simp
  · have hne : w - c ≠ 0 := sub_ne_zero.mpr hwc
    have h_mul : (w - c) * ∫ t in (0 : ℝ)..1, deriv f (c + t • (w - c)) = f w - f c := by
      rwa [← smul_eq_mul]
    rw [dslope_of_ne f hwc, slope_def_module, smul_eq_mul, ← h_mul, ← mul_assoc,
      inv_mul_cancel₀ hne, one_mul]

private lemma exists_compact_tube_prod {U : Set ℂ} (hU : Convex ℝ U) (hU_open : IsOpen U)
    {c₀ w₀ : ℂ} (hc₀ : c₀ ∈ U) (hw₀ : w₀ ∈ U) :
    ∃ ε > 0, ∃ K ⊆ U, IsCompact K ∧
      ∀ c ∈ Metric.ball c₀ ε, ∀ w ∈ Metric.ball w₀ ε,
        ∀ t ∈ Icc (0 : ℝ) 1, c + t • (w - c) ∈ K := by
  obtain ⟨ρ_c, hρ_c_pos, hρ_c_sub⟩ := Metric.isOpen_iff.mp hU_open c₀ hc₀
  obtain ⟨ρ_w, hρ_w_pos, hρ_w_sub⟩ := Metric.isOpen_iff.mp hU_open w₀ hw₀
  set ρ := min ρ_c ρ_w / 2
  have hρ_pos : 0 < ρ := by positivity
  refine ⟨ρ, hρ_pos,
    (fun p : ℂ × ℂ × ℝ ↦ (1 - p.2.2) • p.1 + p.2.2 • p.2.1) ''
      (Metric.closedBall c₀ ρ ×ˢ Metric.closedBall w₀ ρ ×ˢ Icc (0 : ℝ) 1),
    ?_, ?_, ?_⟩
  · rintro z ⟨⟨c, w, t⟩, ⟨hc, hw, ht⟩, rfl⟩
    rw [Metric.mem_closedBall] at hc hw
    simp only [ρ] at hc hw
    exact hU
      (hρ_c_sub (Metric.mem_ball.mpr (by linarith [min_le_left ρ_c ρ_w])))
      (hρ_w_sub (Metric.mem_ball.mpr (by linarith [min_le_right ρ_c ρ_w])))
      (by linarith [ht.2]) ht.1 (by linarith)
  · exact IsCompact.image_of_continuousOn ((isCompact_closedBall _ _).prod
      ((isCompact_closedBall _ _).prod isCompact_Icc))
      (((continuous_const.sub continuous_snd.snd).smul continuous_fst).add
        (continuous_snd.snd.smul continuous_snd.fst)).continuousOn
  · intro c hc w hw t ht
    rw [Metric.mem_ball] at hc hw
    refine ⟨(c, w, t), ⟨?_, ?_, ht⟩, ?_⟩
    · rw [Metric.mem_closedBall]; linarith
    · rw [Metric.mem_closedBall]; linarith
    · -- beta-reduce the applied image map to its evaluated form before `module`
      change (1 - t) • c + t • w = c + t • (w - c)
      module

/-- Joint continuity of `(c, w) ↦ dslope f c w` on `U × U` for `f` differentiable
on open convex `U`. -/
private theorem continuousOn_dslope_prod_of_convex {U : Set ℂ} (hU : Convex ℝ U)
    (hU_open : IsOpen U) (hf : DifferentiableOn ℂ f U) :
    ContinuousOn (fun p : ℂ × ℂ ↦ dslope f p.1 p.2) (U ×ˢ U) := by
  rintro ⟨c₀, w₀⟩ ⟨hc₀, hw₀⟩
  obtain ⟨ε, hε_pos, K, hK_sub, hK_compact, hK_tube⟩ :=
    exists_compact_tube_prod hU hU_open hc₀ hw₀
  have h_deriv_contU : ContinuousOn (deriv f) U :=
    (hf.analyticOnNhd hU_open).deriv.continuousOn
  obtain ⟨M, hM⟩ := hK_compact.bddAbove_image (h_deriv_contU.norm.mono hK_sub)
  have h_eq_nbhd : (fun p : ℂ × ℂ ↦ dslope f p.1 p.2) =ᶠ[nhds (c₀, w₀)]
      fun p ↦ ∫ t in (0 : ℝ)..1, deriv f (p.1 + t • (p.2 - p.1)) := by
    filter_upwards [(hU_open.prod hU_open).mem_nhds
      (⟨hc₀, hw₀⟩ : (c₀, w₀) ∈ U ×ˢ U)] with p hp
    exact dslope_eq_integral_deriv hU hU_open hf hp.1 hp.2
  have hp_proj : ∀ p : ℂ × ℂ, p ∈ Metric.ball (c₀, w₀) ε →
      p.1 ∈ Metric.ball c₀ ε ∧ p.2 ∈ Metric.ball w₀ ε := fun p hp ↦ by
    rw [Metric.mem_ball, Prod.dist_eq] at hp
    exact ⟨Metric.mem_ball.mpr (lt_of_le_of_lt (le_max_left _ _) hp),
      Metric.mem_ball.mpr (lt_of_le_of_lt (le_max_right _ _) hp)⟩
  refine (ContinuousAt.congr ?_ h_eq_nbhd.symm).continuousWithinAt
  refine continuousAt_of_dominated_interval
    (bound := fun _ ↦ max M 0) ?_ ?_ intervalIntegrable_const ?_
  · filter_upwards [Metric.ball_mem_nhds (c₀, w₀) hε_pos] with p hp
    rw [uIoc_of_le (zero_le_one' ℝ)]
    obtain ⟨hp_c, hp_w⟩ := hp_proj p hp
    have h_cont : ContinuousOn (fun t : ℝ ↦ deriv f (p.1 + t • (p.2 - p.1)))
        (Icc (0 : ℝ) 1) :=
      h_deriv_contU.comp (by continuity : Continuous _).continuousOn
        fun t ht ↦ hK_sub (hK_tube p.1 hp_c p.2 hp_w t ht)
    exact (h_cont.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  · filter_upwards [Metric.ball_mem_nhds (c₀, w₀) hε_pos] with p hp
    filter_upwards with t ht
    rw [uIoc_of_le zero_le_one] at ht
    obtain ⟨hp_c, hp_w⟩ := hp_proj p hp
    exact le_max_of_le_left (hM ⟨p.1 + t • (p.2 - p.1),
      hK_tube p.1 hp_c p.2 hp_w t (Ioc_subset_Icc_self ht), rfl⟩)
  · filter_upwards with t ht
    rw [uIoc_of_le zero_le_one] at ht
    have hmem : c₀ + t • (w₀ - c₀) ∈ U :=
      hK_sub (hK_tube c₀ (Metric.mem_ball_self hε_pos) w₀
        (Metric.mem_ball_self hε_pos) t (Ioc_subset_Icc_self ht))
    exact (h_deriv_contU.continuousAt (hU_open.mem_nhds hmem)).comp_of_eq
      (by continuity : Continuous _).continuousAt rfl

/-- **Joint continuity of `(c, w) ↦ dslope f c w` on `U ×ˢ U`** for `f` differentiable on an
arbitrary open set `U` (no convexity assumption). -/
theorem continuousOn_dslope_prod {U : Set ℂ} (hU_open : IsOpen U) (hf : DifferentiableOn ℂ f U) :
    ContinuousOn (fun p : ℂ × ℂ ↦ dslope f p.1 p.2) (U ×ˢ U) := by
  rintro ⟨c₀, w₀⟩ ⟨hc₀, hw₀⟩
  by_cases h_eq : c₀ = w₀
  · subst h_eq
    obtain ⟨ρ, hρ_pos, hρ_sub⟩ := Metric.isOpen_iff.mp hU_open c₀ hc₀
    exact ((continuousOn_dslope_prod_of_convex (convex_ball c₀ ρ) Metric.isOpen_ball
      (hf.mono hρ_sub)).continuousAt ((Metric.isOpen_ball.prod
        Metric.isOpen_ball).mem_nhds ⟨Metric.mem_ball_self hρ_pos,
          Metric.mem_ball_self hρ_pos⟩)).continuousWithinAt
  · have hf_diff_at : ∀ z ∈ U, DifferentiableAt ℂ f z := fun z hz ↦
      (hf z hz).differentiableAt (hU_open.mem_nhds hz)
    have h_sub_ne : (fun p : ℂ × ℂ ↦ p.2 - p.1) (c₀, w₀) ≠ 0 :=
      sub_ne_zero.mpr (Ne.symm h_eq)
    have h_eventually_ne : ∀ᶠ p : ℂ × ℂ in nhds (c₀, w₀), p.2 ≠ p.1 := by
      filter_upwards [(by continuity : Continuous fun p : ℂ × ℂ ↦
        p.2 - p.1).continuousAt.tendsto.eventually_ne h_sub_ne] with p hp using
        sub_ne_zero.mp hp
    have h_eq_nbhd : (fun p : ℂ × ℂ ↦ dslope f p.1 p.2) =ᶠ[nhds (c₀, w₀)]
        fun p ↦ (f p.2 - f p.1) / (p.2 - p.1) := by
      filter_upwards [h_eventually_ne] with p hp
      rw [dslope_of_ne f hp, slope_def_field]
    have h_quot_cont : ContinuousAt
        (fun p : ℂ × ℂ ↦ (f p.2 - f p.1) / (p.2 - p.1)) (c₀, w₀) :=
      ContinuousAt.div
        (((hf_diff_at w₀ hw₀).continuousAt.comp continuousAt_snd).sub
          ((hf_diff_at c₀ hc₀).continuousAt.comp continuousAt_fst))
        (continuousAt_snd.sub continuousAt_fst) h_sub_ne
    exact (h_quot_cont.congr h_eq_nbhd.symm).continuousWithinAt

/-- **Continuity of `c ↦ dslope f c w₀` on any open set `U`** (no convexity).
Follows from `continuousOn_dslope_prod` by partial application. -/
theorem continuousOn_dslope_first_arg {U : Set ℂ} (hU_open : IsOpen U)
    (hf : DifferentiableOn ℂ f U) {w₀ : ℂ} (hw₀ : w₀ ∈ U) :
    ContinuousOn (fun c ↦ dslope f c w₀) U := by
  rw [show (fun c : ℂ ↦ dslope f c w₀) =
    (fun p : ℂ × ℂ ↦ dslope f p.1 p.2) ∘ (fun c : ℂ ↦ (c, w₀)) from rfl]
  exact (continuousOn_dslope_prod hU_open hf).comp
    (continuous_id.prodMk continuous_const).continuousOn fun c hc ↦ ⟨hc, hw₀⟩

/-- **Uniform bound on `deriv (dslope f c) w`.** For `f` differentiable on an open set `U`, with `c`
ranging over a compact subset of `U` and `w` over a small ball around a point `w₀ ∈ U`, the norm
`‖deriv (dslope f c) w‖` is bounded by a single constant. -/
theorem deriv_dslope_bounded_on_compact {U : Set ℂ} (hU_open : IsOpen U)
    (hf : DifferentiableOn ℂ f U) {K_c : Set ℂ} (hK_compact : IsCompact K_c)
    (hK_sub : K_c ⊆ U) {w₀ : ℂ} (hw₀ : w₀ ∈ U) :
    ∃ C > 0, ∃ δ > 0, ∀ c ∈ K_c, ∀ w ∈ Metric.ball w₀ δ,
      ‖deriv (dslope f c) w‖ ≤ C := by
  obtain ⟨ρ_w, hρ_w_pos, hρ_w_sub⟩ := Metric.isOpen_iff.mp hU_open w₀ hw₀
  set ρ := ρ_w / 4
  have hρ_pos : 0 < ρ := by positivity
  have h_cB_w_sub : Metric.closedBall w₀ (3 * ρ / 2) ⊆ U := fun z hz ↦
    hρ_w_sub <| Metric.mem_ball.mpr <| by
      rw [Metric.mem_closedBall] at hz; simp only [ρ] at hz ⊢; linarith
  have hK_sub_prod : K_c ×ˢ Metric.closedBall w₀ (3 * ρ / 2) ⊆ U ×ˢ U :=
    fun ⟨c, z⟩ ⟨hc, hz⟩ ↦ ⟨hK_sub hc, h_cB_w_sub hz⟩
  have hKprod_compact : IsCompact (K_c ×ˢ Metric.closedBall w₀ (3 * ρ / 2)) :=
    hK_compact.prod (isCompact_closedBall _ _)
  obtain ⟨M, hM⟩ :=
    hKprod_compact.bddAbove_image ((continuousOn_dslope_prod hU_open hf).mono hK_sub_prod).norm
  refine ⟨max M 0 / (ρ / 2) + 1, by positivity, ρ / 2, by positivity, ?_⟩
  intro c hc w hw
  rw [Metric.mem_ball] at hw
  have h_ds_diff_U : DifferentiableOn ℂ (dslope f c) U :=
    (Complex.differentiableOn_dslope (hU_open.mem_nhds (hK_sub hc))).mpr hf
  have h_cB_w_w0 :
      Metric.closedBall w (ρ / 2) ⊆ Metric.closedBall w₀ (3 * ρ / 2) := fun z hz ↦ by
    rw [Metric.mem_closedBall] at hz ⊢
    linarith [dist_triangle z w w₀]
  have h_DC : DiffContOnCl ℂ (dslope f c) (Metric.ball w (ρ / 2)) :=
    ⟨h_ds_diff_U.mono fun z hz ↦
      h_cB_w_sub (h_cB_w_w0 (Metric.ball_subset_closedBall hz)),
     (h_ds_diff_U.mono fun z hz ↦
       h_cB_w_sub (h_cB_w_w0 (Metric.closure_ball_subset_closedBall hz))).continuousOn⟩
  have h_sphere_bound : ∀ z ∈ Metric.sphere w (ρ / 2),
      ‖dslope f c z‖ ≤ max M 0 := fun z hz ↦
    le_max_of_le_left
      (hM ⟨(c, z), ⟨hc, h_cB_w_w0 (Metric.sphere_subset_closedBall hz)⟩, rfl⟩)
  linarith [Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by positivity : (0:ℝ) < ρ / 2)
    h_DC h_sphere_bound]

end TauCeti

end
