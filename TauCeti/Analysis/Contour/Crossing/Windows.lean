/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Order.Interval.Set.Defs
import TauCeti.Analysis.Contour.Curve.Distance
import Mathlib.Algebra.Order.Field.Pi
import Mathlib.Order.Interval.Set.UnorderedInterval
import Mathlib.Topology.MetricSpace.Infsep

/-!
# Pairwise-disjoint windows around a finite set of crossings

For a finite set of crossing parameters in an open interval `(a, b)`, off a finite exceptional
set, there is a common radius `r > 0` whose closed windows `[t_i - r, t_i + r]` stay within
`[a, b]`, are pairwise disjoint, and avoid the exceptional set
(`exists_common_window_radius`). Inside such a window, completeness of the crossing set makes
the crossing unique (`eq_of_mem_window_of_eq`), and the distance from the curve to the crossed
point is bounded below off the crossing (`exists_window_dist_lower_bound`) — the geometric
scaffolding that localizes the principal-value analysis to one crossing per window.

## Main results

* `Contour.exists_common_window_radius` — the common window radius.
* `Contour.exists_common_window_radius_le` — a common window radius additionally held below a
  positive per-crossing bound, with strict endpoint margins.
* `Contour.eq_of_mem_window_of_eq_of_le_of_lt` — in-window uniqueness of the crossing, from
  margins at that crossing alone.
* `Contour.eq_of_mem_window_of_eq` — the same for a whole crossing family.
* `Contour.eq_of_mem_window_of_eq_of_lt_of_two_mul_lt` — the same, from the strict margins
  returned by `exists_common_window_radius_le`.
* `Contour.exists_window_dist_lower_bound` — a positive lower bound for `‖γ t - s‖` on the two
  closed half-windows excluding the crossing.
* `Contour.exists_complement_windows_dist_lower_bound` — a positive lower bound for
  `‖γ t - s‖` on the complement of the open crossing windows in `[a, b]`.

## Provenance

Migrated from `multi_pole_common_radius`, `multi_pole_local_uniqueness`,
`multi_pole_local_far_bound` (`CPVExistenceMulti.lean`), and
`multi_pole_smooth_complement_far_bound` (`LocalCutoffs.lean`) in the AINTLIB
`LeanModularForms` development, restated for a raw curve over an arbitrary interval (there the
domain is the bundled `[0, 1]` of a `ClosedPwC1Immersion`), with the half-window bounds from
`Contour.exists_curve_dist_lower_bound` rather than a bespoke compactness argument. See
N. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a generalized Residue
Theorem*, arXiv:1808.00997, §3.
-/

public section

noncomputable section

namespace TauCeti.Contour

open Set

/-- The minimum pairwise distance of a finite set with at least two elements is positive:
`Set.infsep` positivity for finite sets. -/
private theorem min_pairwise_distance_pos {crossings : Finset ℝ}
    (h_card : 2 ≤ crossings.card) :
    ∃ d > 0, ∀ t₁ ∈ crossings, ∀ t₂ ∈ crossings, t₁ ≠ t₂ → d ≤ |t₁ - t₂| := by
  have h_nt : (↑crossings : Set ℝ).Nontrivial := by
    obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp h_card
    exact ⟨p, hp, q, hq, hpq⟩
  refine ⟨(↑crossings : Set ℝ).infsep,
    Set.infsep_pos.mpr ⟨crossings.finite_toSet.einfsep_pos, h_nt.einfsep_lt_top⟩,
    fun t₁ ht₁ t₂ ht₂ ht_ne => ?_⟩
  have h := Set.infsep_le_dist_of_mem (s := (↑crossings : Set ℝ))
    (Finset.mem_coe.mpr ht₁) (Finset.mem_coe.mpr ht₂) ht_ne
  rwa [Real.dist_eq] at h

/-- A finite subset of the open interval `(a, b)` is uniformly separated from both
endpoints. -/
private theorem crossings_bounded_from_endpoints {a b : ℝ} {crossings : Finset ℝ}
    (h_nonempty : crossings.Nonempty)
    (h_Ioo : ∀ t ∈ crossings, t ∈ Ioo a b) :
    ∃ c > 0, ∀ t ∈ crossings, a + c ≤ t ∧ t ≤ b - c := by
  obtain ⟨t_min, ht_min_mem, ht_min⟩ :=
    Finset.exists_min_image crossings (fun t => min (t - a) (b - t)) h_nonempty
  have h0 := h_Ioo t_min ht_min_mem
  refine ⟨min (t_min - a) (b - t_min),
    lt_min (by linarith [h0.1]) (by linarith [h0.2]), fun t ht => ?_⟩
  have h_ge := ht_min t ht
  exact ⟨by linarith [h_ge.trans (min_le_left (t - a) (b - t))],
    by linarith [h_ge.trans (min_le_right (t - a) (b - t))]⟩

/-- A finite set disjoint from a finite exceptional set is uniformly separated from it. -/
private theorem crossings_bounded_from_exceptional {crossings P : Finset ℝ}
    (h_nonempty : crossings.Nonempty)
    (h_off : ∀ t ∈ crossings, t ∉ P) :
    ∃ c > 0, ∀ t ∈ crossings, ∀ p ∈ P, c ≤ |t - p| := by
  by_cases hP : P = ∅
  · exact ⟨1, one_pos, fun _ _ p hp => absurd (hP ▸ hp) (Finset.notMem_empty p)⟩
  · obtain ⟨p₀, hp₀⟩ := Finset.nonempty_iff_ne_empty.mpr hP
    obtain ⟨t₀, ht₀⟩ := h_nonempty
    obtain ⟨m, hm_mem, hm⟩ :=
      Finset.exists_min_image (crossings ×ˢ P) (fun q => |q.1 - q.2|)
        ⟨(t₀, p₀), Finset.mem_product.mpr ⟨ht₀, hp₀⟩⟩
    rw [Finset.mem_product] at hm_mem
    refine ⟨|m.1 - m.2|, abs_pos.mpr fun h_eq =>
      h_off m.1 hm_mem.1 (sub_eq_zero.mp h_eq ▸ hm_mem.2), ?_⟩
    exact fun t ht p hp => hm (t, p) (Finset.mem_product.mpr ⟨ht, hp⟩)

/-- **The common window radius**: for a finite set of crossings in `(a, b)` avoiding a finite
exceptional set `P`, there is `r > 0` such that every window `[t_i - r, t_i + r]` stays within
`[a, b]`, distinct crossings are more than `2r` apart (so the windows are pairwise disjoint),
and no exceptional point comes within `r` of a crossing. -/
theorem exists_common_window_radius {a b : ℝ} {crossings P : Finset ℝ}
    (h_nonempty : crossings.Nonempty)
    (h_Ioo : ∀ t ∈ crossings, t ∈ Ioo a b)
    (h_off : ∀ t ∈ crossings, t ∉ P) :
    ∃ r > 0,
      (∀ t ∈ crossings, a + r ≤ t ∧ t ≤ b - r) ∧
      (∀ t ∈ crossings, ∀ t' ∈ crossings, t' ≠ t → 2 * r < |t - t'|) ∧
      (∀ t ∈ crossings, ∀ p ∈ P, r < |t - p|) := by
  obtain ⟨c, hc_pos, h_endpts⟩ := crossings_bounded_from_endpoints h_nonempty h_Ioo
  obtain ⟨e, he_pos, h_exc⟩ := crossings_bounded_from_exceptional h_nonempty h_off
  by_cases h_card_one : crossings.card = 1
  · refine ⟨min c (e / 2), lt_min hc_pos (by linarith), fun t ht => ?_, ?_, fun t ht p hp => ?_⟩
    · obtain ⟨h1, h2⟩ := h_endpts t ht
      exact ⟨by linarith [min_le_left c (e / 2)], by linarith [min_le_left c (e / 2)]⟩
    · intro t ht t' ht' ht_ne
      obtain ⟨u, hu⟩ := Finset.card_eq_one.mp h_card_one
      rw [hu, Finset.mem_singleton] at ht ht'
      exact absurd (ht'.trans ht.symm) ht_ne
    · linarith [h_exc t ht p hp, min_le_right c (e / 2)]
  · have h_card : 2 ≤ crossings.card := by
      have := Finset.card_pos.mpr h_nonempty
      omega
    obtain ⟨d, hd_pos, h_dist⟩ := min_pairwise_distance_pos h_card
    refine ⟨min c (min (e / 2) (d / 4)),
      lt_min hc_pos (lt_min (by linarith) (by linarith)),
      fun t ht => ?_, fun t ht t' ht' ht_ne => ?_, fun t ht p hp => ?_⟩
    · obtain ⟨h1, h2⟩ := h_endpts t ht
      exact ⟨by linarith [min_le_left c (min (e / 2) (d / 4))],
        by linarith [min_le_left c (min (e / 2) (d / 4))]⟩
    · have h_d := h_dist t' ht' t ht ht_ne
      rw [abs_sub_comm] at h_d
      linarith [(min_le_right c (min (e / 2) (d / 4))).trans (min_le_right (e / 2) (d / 4))]
    · linarith [h_exc t ht p hp,
        (min_le_right c (min (e / 2) (d / 4))).trans (min_le_left (e / 2) (d / 4))]

/-- **A common window radius below a prescribed per-crossing bound.** The `P = ∅` case of
`exists_common_window_radius` with the radius additionally placed under a given positive `R t` at
every crossing — which is what lets a family of per-crossing window results, each valid only below
its own radius, be applied at one shared radius. There is no exceptional-set clause; use
`exists_common_window_radius` directly when one is needed.

Unlike that lemma this one does not ask for a nonempty family: for no crossings all three
conditions are vacuous and any positive radius serves.

The endpoint margins come out *strict* here: the radius is chosen strictly below the one that lemma
supplies, so it clears both endpoints with room to spare. -/
theorem exists_common_window_radius_le {a b : ℝ} {crossings : Finset ℝ}
    (h_Ioo : ∀ t ∈ crossings, t ∈ Ioo a b)
    (R : ℝ → ℝ) (hR_pos : ∀ t ∈ crossings, 0 < R t) :
    ∃ r > 0,
      (∀ t ∈ crossings, a + r < t ∧ t < b - r) ∧
      (∀ t ∈ crossings, ∀ t' ∈ crossings, t' ≠ t → 2 * r < |t - t'|) ∧
      (∀ t ∈ crossings, r ≤ R t) := by
  classical
  rcases crossings.eq_empty_or_nonempty with rfl | h_nonempty
  · exact ⟨1, one_pos, by simp, by simp, by simp⟩
  obtain ⟨r₀, hr₀_pos, h_endpts, h_pair, -⟩ :=
    exists_common_window_radius (P := ∅) h_nonempty h_Ioo fun t _ => Finset.notMem_empty t
  -- Pick one radius strictly under `r₀` and under every `R t`, indexing the bounds by
  -- `Option {t // t ∈ crossings}` so that `r₀` is the `none` component.
  obtain ⟨r, hr_pos, hr_all⟩ := Pi.exists_forall_pos_add_lt
    (ι := Option {t // t ∈ crossings}) (x := fun _ => (0 : ℝ))
    (y := fun i => i.elim r₀ fun t => R t.1)
    (fun i => by
      cases i with
      | none => simpa using hr₀_pos
      | some t => simpa using hR_pos t.1 t.2)
  have hr_lt : r < r₀ := by simpa using hr_all none
  exact ⟨r, hr_pos, fun t ht => ⟨by linarith [(h_endpts t ht).1], by
    linarith [(h_endpts t ht).2]⟩,
    fun t ht t' ht' hne => by linarith [h_pair t ht t' ht' hne],
    fun t ht => le_of_lt (by simpa using hr_all (some ⟨t, ht⟩))⟩

/-- **In-window uniqueness of the crossing, from margins at that crossing alone.** If the window
`[t_i - r, t_i + r]` lies inside `[a, b]`, every listed crossing other than `t_i` is more than
`r` from `t_i`, and the listing is complete — every parameter of `[a, b]` where `γ` takes the
value `s` is listed — then the only parameter of that window where `γ` takes the value `s` is
`t_i` itself.

This is the pointwise core: nothing is assumed about the other crossings' own windows, and
`t_i` need not itself be listed. `eq_of_mem_window_of_eq` is the family-wide form, for callers
holding margins for every crossing at once. Stated for a bare function; no regularity is
used. -/
theorem eq_of_mem_window_of_eq_of_le_of_lt {α : Type*} {γ : ℝ → α} {s : α} {a b : ℝ}
    {crossings : Finset ℝ} {r t_i : ℝ}
    (h_endpts : a + r ≤ t_i ∧ t_i ≤ b - r)
    (h_pairwise : ∀ t' ∈ crossings, t' ≠ t_i → r < |t_i - t'|)
    (h_complete : ∀ t ∈ Icc a b, γ t = s → t ∈ crossings)
    {t : ℝ} (ht : t ∈ Icc (t_i - r) (t_i + r)) (h_eq : γ t = s) :
    t = t_i := by
  obtain ⟨h_ge, h_le⟩ := h_endpts
  have h_t_cross : t ∈ crossings :=
    h_complete t ⟨by linarith [ht.1], by linarith [ht.2]⟩ h_eq
  by_contra h_ne
  have h_dist := h_pairwise t h_t_cross h_ne
  have : |t_i - t| ≤ r := by
    rw [abs_sub_comm, abs_le]
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  linarith [abs_nonneg (t_i - t)]

/-- **In-window uniqueness of the crossing**: with windows inside `[a, b]`, distinct crossings
more than `r` apart, and completeness — every parameter of `[a, b]` where `γ` takes the value
`s` is a listed crossing — the only parameter of the window `[t_i - r, t_i + r]` where `γ`
takes the value `s` is `t_i` itself. Stated for a bare function; no regularity is used.

The family-wide form, for callers holding margins for every crossing at once; it reads them off
at `t_i` and defers to `eq_of_mem_window_of_eq_of_le_of_lt`. -/
theorem eq_of_mem_window_of_eq {α : Type*} {γ : ℝ → α} {s : α} {a b : ℝ}
    {crossings : Finset ℝ} {r : ℝ}
    (h_endpts : ∀ t ∈ crossings, a + r ≤ t ∧ t ≤ b - r)
    (h_pairwise : ∀ t ∈ crossings, ∀ t' ∈ crossings, t' ≠ t → r < |t - t'|)
    (h_complete : ∀ t ∈ Icc a b, γ t = s → t ∈ crossings)
    {t_i : ℝ} (ht_i : t_i ∈ crossings)
    {t : ℝ} (ht : t ∈ Icc (t_i - r) (t_i + r)) (h_eq : γ t = s) :
    t = t_i :=
  eq_of_mem_window_of_eq_of_le_of_lt (h_endpts t_i ht_i) (h_pairwise t_i ht_i) h_complete ht h_eq

/-- **In-window uniqueness of the crossing, from a common window radius.** The variant of
`eq_of_mem_window_of_eq_of_le_of_lt` whose margins are the *strict* ones
`exists_common_window_radius_le` returns, read off at `t_i`: `t_i` more than `r` inside the
endpoints, and every other crossing more than `2 * r` from it. No sign condition on `r` is
required — halving the pairwise margin needs `0 ≤ r`, but a negative radius leaves the window
`[t_i - r, t_i + r]` empty, so `ht` supplies it. -/
theorem eq_of_mem_window_of_eq_of_lt_of_two_mul_lt {α : Type*} {γ : ℝ → α} {s : α} {a b : ℝ}
    {crossings : Finset ℝ} {r t_i : ℝ}
    (h_endpts : a + r < t_i ∧ t_i < b - r)
    (h_pairwise : ∀ t' ∈ crossings, t' ≠ t_i → 2 * r < |t_i - t'|)
    (h_complete : ∀ t ∈ Icc a b, γ t = s → t ∈ crossings)
    {t : ℝ} (ht : t ∈ Icc (t_i - r) (t_i + r)) (h_eq : γ t = s) :
    t = t_i := by
  have hr : 0 ≤ r := by linarith [ht.1, ht.2]
  exact eq_of_mem_window_of_eq_of_le_of_lt ⟨h_endpts.1.le, h_endpts.2.le⟩
    (fun t' ht' hne => by linarith [h_pairwise t' ht' hne]) h_complete ht h_eq

/-- **Positive distance bound on the half-windows**: when the crossing is unique in its window,
`‖γ t - s‖` is bounded below by a common `m > 0` on the two closed half-windows
`[t_i - r, t_i - r']` and `[t_i + r', t_i + r]` excluding the crossing. -/
theorem exists_window_dist_lower_bound {γ : ℝ → ℂ} {s : ℂ} {t_i r : ℝ}
    (hγ_cont : ContinuousOn γ (Icc (t_i - r) (t_i + r)))
    (h_unique : ∀ t ∈ Icc (t_i - r) (t_i + r), γ t = s → t = t_i)
    {r' : ℝ} (hr'_pos : 0 < r') (hr'_le : r' ≤ r) :
    ∃ m > 0,
      (∀ t ∈ Icc (t_i - r) (t_i - r'), m ≤ ‖γ t - s‖) ∧
      (∀ t ∈ Icc (t_i + r') (t_i + r), m ≤ ‖γ t - s‖) := by
  have h_sub_l : uIcc (t_i - r) (t_i - r') ⊆ Icc (t_i - r) (t_i + r) := by
    rw [uIcc_of_le (by linarith)]
    exact Icc_subset_Icc le_rfl (by linarith)
  have h_sub_r : uIcc (t_i + r') (t_i + r) ⊆ Icc (t_i - r) (t_i + r) := by
    rw [uIcc_of_le (by linarith)]
    exact Icc_subset_Icc (by linarith) le_rfl
  obtain ⟨ml, hml_pos, hml⟩ := exists_curve_dist_lower_bound (hγ_cont.mono h_sub_l)
    fun t ht h_eq => by
      have h_t := h_unique t (h_sub_l ht) h_eq
      rw [uIcc_of_le (by linarith)] at ht
      linarith [ht.2]
  obtain ⟨mr, hmr_pos, hmr⟩ := exists_curve_dist_lower_bound (hγ_cont.mono h_sub_r)
    fun t ht h_eq => by
      have h_t := h_unique t (h_sub_r ht) h_eq
      rw [uIcc_of_le (by linarith)] at ht
      linarith [ht.1]
  refine ⟨min ml mr, lt_min hml_pos hmr_pos, fun t ht => ?_, fun t ht => ?_⟩
  · exact (min_le_left _ _).trans (hml t (by rwa [uIcc_of_le (by linarith)]))
  · exact (min_le_right _ _).trans (hmr t (by rwa [uIcc_of_le (by linarith)]))

/-- **Positive distance bound off the crossing windows**: with every value-`s` parameter of
`[a, b]` a listed crossing, `‖γ t - s‖` is bounded below by a positive `m` on the complement of
the open crossing windows in `[a, b]` — the far bound on the smooth part of a multi-crossing
excision. -/
theorem exists_complement_windows_dist_lower_bound {γ : ℝ → ℂ} {s : ℂ} {a b : ℝ}
    {crossings : Finset ℝ} (hγ_cont : ContinuousOn γ (Icc a b))
    (h_complete : ∀ t ∈ Icc a b, γ t = s → t ∈ crossings)
    (r_at : ℝ → ℝ) (hr_pos : ∀ t ∈ crossings, 0 < r_at t) :
    ∃ m > 0, ∀ t ∈ Icc a b,
      (∀ t_i ∈ crossings, t ∉ Ioo (t_i - r_at t_i) (t_i + r_at t_i)) →
      m ≤ ‖γ t - s‖ := by
  classical
  set C : Set ℝ := {t ∈ Icc a b |
    ∀ t_i ∈ crossings, t ∉ Ioo (t_i - r_at t_i) (t_i + r_at t_i)} with hC_def
  have hC_subset : C ⊆ Icc a b := fun t ht => ht.1
  have hC_closed : IsClosed C := by
    have h_eq : C = Icc a b ∩ ⋂ t_i ∈ crossings, (Ioo (t_i - r_at t_i) (t_i + r_at t_i))ᶜ := by
      ext t
      simp only [hC_def, mem_ofPred_eq, mem_inter_iff, mem_iInter, mem_compl_iff]
    rw [h_eq]
    exact isClosed_Icc.inter (isClosed_biInter fun _ _ => isOpen_Ioo.isClosed_compl)
  have hC_compact : IsCompact C := isCompact_Icc.of_isClosed_subset hC_closed hC_subset
  rcases C.eq_empty_or_nonempty with hC_empty | hC_ne
  · refine ⟨1, one_pos, fun t ht h_avoid => absurd ?_ (notMem_empty t)⟩
    have h_mem : t ∈ C := ⟨ht, h_avoid⟩
    rwa [hC_empty] at h_mem
  · obtain ⟨t_min, ht_min_mem, ht_min⟩ := hC_compact.exists_isMinOn hC_ne
      (((hγ_cont.mono hC_subset).sub continuousOn_const).norm)
    refine ⟨‖γ t_min - s‖, ?_, fun t ht h_avoid => ht_min ⟨ht, h_avoid⟩⟩
    refine norm_pos_iff.mpr (sub_ne_zero.mpr fun h_eq => ?_)
    have h_cross : t_min ∈ crossings := h_complete t_min (hC_subset ht_min_mem) h_eq
    exact ht_min_mem.2 t_min h_cross
      ⟨by linarith [hr_pos t_min h_cross], by linarith [hr_pos t_min h_cross]⟩

end TauCeti.Contour

end
