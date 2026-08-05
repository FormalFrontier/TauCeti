/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.Analysis.Contour.PwC1ImmersionOn
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Normed.Module.HahnBanach

/-!
# Crossing finiteness for piecewise-`C¹` immersions (HW Proposition 2.2)

A piecewise-`C¹` immersion meets any given point `z₀ ∈ ℂ` at only finitely many parameters —
Proposition 2.2 of Hungerbühler–Wasem (there stated with endpoint avoidance; the one-sided
isolation lemmas here cover the endpoints, so no avoidance is needed), the geometric input
that makes the on-cycle singularity set of the generalized residue theorem a finite crossing
family. It discharges the `finite_crossings` field of `Contour.ConditionAprime` for immersed
cycles.

The mechanism: at a crossing the one-sided tangent is non-zero, so a dual functional of it makes
`t ↦ γ t - z₀` strictly monotone in that functional on a one-sided neighbourhood, forbidding
nearby crossings; crossings are therefore isolated, and an infinite crossing set inside the
compact `[[a, b]]` would have an accumulation point.

## Main results

* `Contour.IsPwC1ImmersionOn.eventually_ne_nhdsNE` — crossings of an immersion are isolated.
* `Contour.IsPwC1ImmersionOn.finite_crossings` — **HW Proposition 2.2**: the crossing set
  `[[a, b]] ∩ γ ⁻¹' {z₀}` of an immersion is finite.
* `Contour.IsPwC1ImmersionOn.mem_toFinset_finite_crossings` — membership in the resulting
  crossing finset.

## Provenance

Migrated from `CrossingAnalysis.lean` (`PwC1Immersion.crossingSet_finite` and the isolation
lemmas) of the AINTLIB `LeanModularForms` development, restated for the raw curve `γ : ℝ → ℂ` on
`[[a, b]]`: the one-sided tangent data carried there by the `left_deriv_limit` /
`right_deriv_limit` fields of the bundled `PwC1Immersion` comes from the `IsPwC1ImmersionOn`
tangent-limit API (`PwC1ImmersionOn.lean`), which uniformises the smooth-point and breakpoint
cases of the isolation argument. See N. Hungerbühler, M. Wasem, *Non-integer valued
winding numbers and a generalized Residue Theorem*, arXiv:1808.00997, Proposition 2.2.
-/

public section

noncomputable section

namespace TauCeti.Contour

open Set Filter Topology

variable {γ : ℝ → ℂ} {a b : ℝ} {z₀ : ℂ}

/-- Differentiability and a non-zero derivative at interior non-breakpoint parameters, relative
to a breakpoint witness of the immersion clause. -/
private theorem deriv_ne_zero_off_breakpoints {p : Finset ℝ}
    (hpieces : ∀ c d : ℝ, c < d → Icc c d ⊆ uIcc a b → Disjoint (↑p : Set ℝ) (Ioo c d) →
      ContDiffOn ℝ 1 γ (Icc c d) ∧ ∀ t ∈ Icc c d, derivWithin γ (Icc c d) t ≠ 0)
    {t : ℝ} (ht : t ∈ Ioo (min a b) (max a b)) (htp : t ∉ (↑p : Set ℝ)) :
    DifferentiableAt ℝ γ t ∧ deriv γ t ≠ 0 := by
  obtain ⟨c, d, htcd, hsub, hdisj⟩ := exists_Icc_subset_uIcc_disjoint p.finite_toSet.isClosed ht htp
  have hC1 : ContDiffOn ℝ 1 γ (Icc c d) := (hpieces c d (htcd.1.trans htcd.2) hsub hdisj).1
  have hne := (hpieces c d (htcd.1.trans htcd.2) hsub hdisj).2
  have hmem : Icc c d ∈ 𝓝 t := Icc_mem_nhds htcd.1 htcd.2
  have hdiff : DifferentiableAt ℝ γ t :=
    (hC1.differentiableOn one_ne_zero).differentiableAt hmem
  have hrw : derivWithin γ (Icc c d) t = deriv γ t := derivWithin_of_mem_nhds hmem
  exact ⟨hdiff, hrw ▸ hne t (Ioo_subset_Icc_self htcd)⟩

/-- **At-most-one-crossing core.** If a continuous linear functional is positive on `deriv γ`
throughout an open interval on which `γ` is differentiable, then that functional of `γ - z₀` is
strictly monotone on the closed interval, so `γ` meets `z₀` at most once there. -/
private theorem crossing_atMostOne_of_dual_deriv_pos {f : StrongDual ℝ ℂ} {c d : ℝ}
    (hγ_cont : ContinuousOn γ (Icc c d))
    (h_cond : ∀ t ∈ Ioo c d, DifferentiableAt ℝ γ t ∧ 0 < f (deriv γ t)) :
    ∀ t₁ ∈ Icc c d, ∀ t₂ ∈ Icc c d, γ t₁ = z₀ → γ t₂ = z₀ → t₁ = t₂ := by
  set g : ℝ → ℝ := fun t => f (γ t - z₀) with hg_def
  have hg_cont : ContinuousOn g (Icc c d) :=
    f.continuous.comp_continuousOn (hγ_cont.sub continuousOn_const)
  have hg_deriv_pos : ∀ s ∈ interior (Icc c d), 0 < deriv g s := by
    rw [interior_Icc]
    intro s hs
    obtain ⟨hs_diff, hs_pos⟩ := h_cond s hs
    have hder : HasDerivAt (fun t => γ t - z₀) (deriv γ s) s :=
      hs_diff.hasDerivAt.sub_const z₀
    exact (f.hasFDerivAt.comp_hasDerivAt s hder).deriv ▸ hs_pos
  intro t₁ ht₁ t₂ ht₂ hc₁ hc₂
  refine (strictMonoOn_of_deriv_pos (convex_Icc c d) hg_cont hg_deriv_pos).injOn ht₁ ht₂ ?_
  simp only [hg_def, hc₁, hc₂]

/-- A nonempty open interval inside `(min a b, max a b)` has its closure inside `[[a, b]]`. -/
private theorem Icc_subset_uIcc_of_Ioo_subset {c d : ℝ} (hcd : c < d)
    (h : Ioo c d ⊆ Ioo (min a b) (max a b)) : Icc c d ⊆ uIcc a b := by
  obtain ⟨t, ht⟩ := nonempty_Ioo.mpr hcd
  have hab : min a b < max a b := (h ht).1.trans (h ht).2
  have h2 := closure_mono h
  rw [closure_Ioo hcd.ne, closure_Ioo hab.ne] at h2
  exact h2.trans Icc_min_max.subset

/-- The parameters near `t₀` (from the given side) that lie in the interior, avoid the
breakpoints, and see a positive dual value of `deriv γ`. -/
private theorem eventually_interior_off_pos {p : Finset ℝ} {t₀ : ℝ} {L : ℂ}
    {f : StrongDual ℝ ℂ} {l : Filter ℝ} (hl : l ≤ 𝓝 t₀) (hne : ∀ᶠ t in l, t ≠ t₀)
    (h_Ioo : ∀ᶠ t in l, t ∈ Ioo (min a b) (max a b))
    (hL_tendsto : Tendsto (deriv γ) l (𝓝 L)) (hfL_pos : 0 < f L) :
    ∀ᶠ t in l, (t ∈ Ioo (min a b) (max a b) ∧ t ∉ (↑p : Set ℝ)) ∧ 0 < f (deriv γ t) := by
  have h_off : ∀ᶠ t in l, t ∉ (↑p : Set ℝ) := by
    have hcl : IsClosed ((↑p \ {t₀} : Set ℝ)) := (p.finite_toSet.subset sdiff_subset).isClosed
    have h1 : ∀ᶠ t in l, t ∈ (↑p \ {t₀} : Set ℝ)ᶜ :=
      hl (hcl.isOpen_compl.mem_nhds (by simp))
    filter_upwards [h1, hne] with t htc htne htp
    exact htc ⟨htp, htne⟩
  have h_pos : ∀ᶠ t in l, 0 < f (deriv γ t) :=
    (f.continuous.continuousAt.tendsto.comp hL_tendsto).eventually (Ioi_mem_nhds hfL_pos)
  exact (h_Ioo.and h_off).and h_pos

/-- Crossings of an immersion are isolated from the right: if `γ t₀ = z₀` with
`t₀ ∈ [min, max)`, then `γ t ≠ z₀` for `t` in a punctured right neighbourhood of `t₀`. -/
private theorem crossing_isolated_right (h : IsPwC1ImmersionOn γ a b) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Ico (min a b) (max a b)) (hcross : γ t₀ = z₀) :
    ∀ᶠ t in 𝓝[>] t₀, γ t ≠ z₀ := by
  obtain ⟨p, hp, hpieces⟩ := h.exists_breakpoints
  obtain ⟨L, hL_ne, hL_tendsto⟩ := h.exists_deriv_right_limit ht₀
  obtain ⟨f, -, hf_L⟩ := exists_dual_vector ℝ L (norm_ne_zero_iff.mpr hL_ne)
  have hfL_pos : (0 : ℝ) < f L := by
    rw [hf_L]; exact_mod_cast norm_pos_iff.mpr hL_ne
  have h_Ioo : ∀ᶠ t in 𝓝[>] t₀, t ∈ Ioo (min a b) (max a b) := by
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds ht₀.2),
      self_mem_nhdsWithin] with t ht1 ht2
    exact ⟨ht₀.1.trans_lt ht2, ht1⟩
  have h_ev := eventually_interior_off_pos (p := p) nhdsWithin_le_nhds
    (eventually_nhdsWithin_of_forall fun t ht => ne_of_gt ht) h_Ioo hL_tendsto hfL_pos
  obtain ⟨d, hd_gt, hd_cond⟩ :=
    mem_nhdsGT_iff_exists_Ioo_subset.mp (Filter.eventually_iff.mp h_ev)
  have h_once := crossing_atMostOne_of_dual_deriv_pos (z₀ := z₀) (f := f)
    (h.continuousOn.mono (Icc_subset_uIcc_of_Ioo_subset hd_gt fun t ht => (hd_cond ht).1.1))
    fun t ht => ⟨(deriv_ne_zero_off_breakpoints hpieces (hd_cond ht).1.1 (hd_cond ht).1.2).1,
      (hd_cond ht).2⟩
  refine Filter.eventually_iff.mpr (mem_nhdsGT_iff_exists_Ioo_subset.mpr ⟨d, hd_gt, ?_⟩)
  exact fun t ht hγt => (ne_of_gt ht.1)
    (h_once t (Ioo_subset_Icc_self ht) t₀ (left_mem_Icc.mpr (le_of_lt hd_gt)) hγt hcross)

/-- Crossings of an immersion are isolated from the left: if `γ t₀ = z₀` with
`t₀ ∈ (min, max]`, then `γ t ≠ z₀` for `t` in a punctured left neighbourhood of `t₀`. -/
private theorem crossing_isolated_left (h : IsPwC1ImmersionOn γ a b) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Ioc (min a b) (max a b)) (hcross : γ t₀ = z₀) :
    ∀ᶠ t in 𝓝[<] t₀, γ t ≠ z₀ := by
  obtain ⟨p, hp, hpieces⟩ := h.exists_breakpoints
  obtain ⟨L, hL_ne, hL_tendsto⟩ := h.exists_deriv_left_limit ht₀
  obtain ⟨f, -, hf_L⟩ := exists_dual_vector ℝ L (norm_ne_zero_iff.mpr hL_ne)
  have hfL_pos : (0 : ℝ) < f L := by
    rw [hf_L]; exact_mod_cast norm_pos_iff.mpr hL_ne
  have h_Ioo : ∀ᶠ t in 𝓝[<] t₀, t ∈ Ioo (min a b) (max a b) := by
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds (eventually_gt_nhds ht₀.1),
      self_mem_nhdsWithin] with t ht1 ht2
    exact ⟨ht1, ht2.trans_le ht₀.2⟩
  have h_ev := eventually_interior_off_pos (p := p) nhdsWithin_le_nhds
    (eventually_nhdsWithin_of_forall fun t ht => ne_of_lt ht) h_Ioo hL_tendsto hfL_pos
  obtain ⟨c, hc_lt, hc_cond⟩ :=
    mem_nhdsLT_iff_exists_Ioo_subset.mp (Filter.eventually_iff.mp h_ev)
  have h_once := crossing_atMostOne_of_dual_deriv_pos (z₀ := z₀) (f := f)
    (h.continuousOn.mono (Icc_subset_uIcc_of_Ioo_subset hc_lt fun t ht => (hc_cond ht).1.1))
    fun t ht => ⟨(deriv_ne_zero_off_breakpoints hpieces (hc_cond ht).1.1 (hc_cond ht).1.2).1,
      (hc_cond ht).2⟩
  refine Filter.eventually_iff.mpr (mem_nhdsLT_iff_exists_Ioo_subset.mpr ⟨c, hc_lt, ?_⟩)
  exact fun t ht hγt => (ne_of_lt ht.2)
    (h_once t (Ioo_subset_Icc_self ht) t₀ (right_mem_Icc.mpr (le_of_lt hc_lt)) hγt hcross)

/-- **Crossings of an immersion are isolated**: at every interior crossing there is a punctured
neighbourhood on which the immersion avoids `z₀`. -/
theorem IsPwC1ImmersionOn.eventually_ne_nhdsNE (h : IsPwC1ImmersionOn γ a b) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Ioo (min a b) (max a b)) (hcross : γ t₀ = z₀) :
    ∀ᶠ t in 𝓝[≠] t₀, γ t ≠ z₀ := by
  rw [punctured_nhds_eq_nhdsWithin_sup_nhdsWithin, Filter.eventually_sup]
  exact ⟨crossing_isolated_left h ⟨ht₀.1, ht₀.2.le⟩ hcross,
    crossing_isolated_right h ⟨ht₀.1.le, ht₀.2⟩ hcross⟩

/-- **HW Proposition 2.2: the crossing set of a piecewise-`C¹` immersion is finite** — the
geometric input that makes the on-cycle singularities of the generalized residue theorem a
finite crossing family. -/
theorem IsPwC1ImmersionOn.finite_crossings (h : IsPwC1ImmersionOn γ a b) :
    (uIcc a b ∩ γ ⁻¹' {z₀}).Finite := by
  by_contra hS_inf
  obtain ⟨t₀, -, ht₀_acc⟩ := (Set.not_finite.mp hS_inf).exists_accPt_of_subset_isCompact
    isCompact_uIcc inter_subset_left
  have huIcc : IsClosed (uIcc a b) := by rw [← Icc_min_max]; exact isClosed_Icc
  have hcl : IsClosed (uIcc a b ∩ γ ⁻¹' {z₀}) :=
    h.continuousOn.preimage_isClosed_of_isClosed huIcc isClosed_singleton
  have ht₀_mem : t₀ ∈ uIcc a b ∩ γ ⁻¹' {z₀} :=
    hcl.closure_eq ▸ mem_closure_iff_clusterPt.mpr ht₀_acc.clusterPt
  have ht₀_Icc : t₀ ∈ Icc (min a b) (max a b) := by rw [Icc_min_max]; exact ht₀_mem.1
  rw [accPt_iff_frequently_nhdsNE, punctured_nhds_eq_nhdsWithin_sup_nhdsWithin,
    Filter.frequently_sup] at ht₀_acc
  rcases ht₀_acc with hfreq | hfreq
  · rcases eq_or_lt_of_le ht₀_Icc.1 with heq | hlt
    · have hev : ∀ᶠ t in 𝓝[<] t₀, t ∉ uIcc a b ∩ γ ⁻¹' {z₀} :=
        eventually_nhdsWithin_of_forall fun t ht hts => absurd
          (by rw [← Icc_min_max] at hts; exact hts.1.1) (not_le.mpr (ht.trans_le heq.ge))
      exact (hfreq.and_eventually hev).exists.elim fun t ht => ht.2 ht.1
    · have hev := crossing_isolated_left h ⟨hlt, ht₀_Icc.2⟩ ht₀_mem.2
      exact (hfreq.and_eventually hev).exists.elim fun t ht => ht.2 ht.1.2
  · rcases eq_or_lt_of_le ht₀_Icc.2 with heq | hlt
    · have hev : ∀ᶠ t in 𝓝[>] t₀, t ∉ uIcc a b ∩ γ ⁻¹' {z₀} :=
        eventually_nhdsWithin_of_forall fun t ht hts => absurd
          (by rw [← Icc_min_max] at hts; exact hts.1.2) (not_le.mpr (heq.ge.trans_lt ht))
      exact (hfreq.and_eventually hev).exists.elim fun t ht => ht.2 ht.1
    · have hev := crossing_isolated_right h ⟨ht₀_Icc.1, hlt⟩ ht₀_mem.2
      exact (hfreq.and_eventually hev).exists.elim fun t ht => ht.2 ht.1.2

/-- **Membership in the crossing finset.** The finset supplied by
`IsPwC1ImmersionOn.finite_crossings` consists of exactly the parameters of `[[a, b]]` at which
`γ` takes the value `z₀`. Multi-crossing principal-value arguments index their windows by this
finset, so they need the characterisation and not just the finiteness; for ordered endpoints
follow with `uIcc_of_le`. -/
theorem IsPwC1ImmersionOn.mem_toFinset_finite_crossings (h : IsPwC1ImmersionOn γ a b) {t : ℝ} :
    t ∈ (h.finite_crossings (z₀ := z₀)).toFinset ↔ t ∈ uIcc a b ∧ γ t = z₀ := by
  rw [Set.Finite.mem_toFinset, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]

end TauCeti.Contour

end
