/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Topology.Algebra.Group.Basic

/-!
# Exit times of a curve from small balls around a crossed point

For a curve `γ : ℝ → E` with `γ t₀ = s`, the **first exit time at radius `ε`** on the right is
the first parameter `t ≥ t₀` in a window `[t₀, t₀ + δ]` with `‖γ t - s‖ = ε`; symmetrically on
the left. This file constructs the exit times as `sInf`/`sSup` of the closed set of
outside-the-ball times and establishes the API the principal-value excision consumes: the exit
time lies in the window, sits at exact distance `ε` (for small `ε`), tends to `t₀` one-sidedly
as `ε → 0⁺`, and eventually has exact radius — the `t_eps` hypotheses of
`Contour.antiderivative_diff_across_crossing_tendsto_zero`.

## Main definitions

* `Contour.firstExitTimeRight γ t₀ δ s ε` — `sInf {t ∈ [t₀, t₀+δ] | ε ≤ ‖γ t - s‖}`.
* `Contour.firstExitTimeLeft γ t₀ δ s ε` — `sSup {t ∈ [t₀-δ, t₀] | ε ≤ ‖γ t - s‖}` (the latest
  outside-the-ball time before `t₀`, i.e. the first exit when approaching `t₀` from the left).

## Main results

* `Contour.firstExitTimeRight_mem_Icc` / `Left` — the exit time lies in the window.
* `Contour.norm_at_firstExitTimeRight_eq` / `Left` — the exit time is at exact distance `ε`.
* `Contour.firstExitTimeRight_tendsto` / `Left` — the exit time tends to `t₀` one-sidedly as
  `ε → 0⁺`, provided `γ` leaves `s` on the window.
* `Contour.eventually_norm_at_firstExitTimeRight_eq` / `Left` — eventual exact radius along
  `𝓝[>] 0`.

## Provenance

Migrated from `firstExitTimeRight`/`firstExitTimeLeft` and their API in `ExitTime.lean` of the
AINTLIB `LeanModularForms` development, restated for a curve into a normed group. See
N. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a generalized Residue
Theorem*, arXiv:1808.00997, §3.
-/

public section

noncomputable section

namespace TauCeti.Contour

open Filter Set Topology

variable {E : Type*} [NormedAddCommGroup E]

/-- **First exit time at radius `ε` (right side)**: the `sInf` of the times
`t ∈ [t₀, t₀ + δ]` with `ε ≤ ‖γ t - s‖`; the junk value is `sInf ∅` when the curve never
reaches distance `ε` in the window. -/
def firstExitTimeRight (γ : ℝ → E) (t₀ δ : ℝ) (s : E) (ε : ℝ) : ℝ :=
  sInf {t ∈ Icc t₀ (t₀ + δ) | ε ≤ ‖γ t - s‖}

/-- The set defining `firstExitTimeRight` contains the window endpoint when the curve is far
enough there. -/
private theorem right_endpoint_mem {γ : ℝ → E} {t₀ δ ε : ℝ} {s : E}
    (hδ : 0 ≤ δ) (h_far : ε ≤ ‖γ (t₀ + δ) - s‖) :
    (t₀ + δ) ∈ {t ∈ Icc t₀ (t₀ + δ) | ε ≤ ‖γ t - s‖} :=
  ⟨⟨by linarith, le_rfl⟩, h_far⟩

/-- The set defining `firstExitTimeRight` is bounded below by `t₀`. -/
private theorem right_set_bddBelow (γ : ℝ → E) (t₀ δ ε : ℝ) (s : E) :
    ∀ t ∈ {t ∈ Icc t₀ (t₀ + δ) | ε ≤ ‖γ t - s‖}, t₀ ≤ t :=
  fun _ ⟨hmem, _⟩ => hmem.1

/-- **The right exit time lies in the window** `[t₀, t₀ + δ]`. -/
theorem firstExitTimeRight_mem_Icc {γ : ℝ → E} {t₀ δ ε : ℝ} {s : E} (hδ : 0 ≤ δ)
    (hε_le : ε ≤ ‖γ (t₀ + δ) - s‖) :
    t₀ ≤ firstExitTimeRight γ t₀ δ s ε ∧ firstExitTimeRight γ t₀ δ s ε ≤ t₀ + δ :=
  ⟨le_csInf ⟨t₀ + δ, right_endpoint_mem hδ hε_le⟩ (right_set_bddBelow γ t₀ δ ε s),
    csInf_le ⟨t₀, right_set_bddBelow γ t₀ δ ε s⟩ (right_endpoint_mem hδ hε_le)⟩

/-- **Radius lower bound at the right exit time**: the `sInf` of the closed set of
outside-the-ball times is itself outside the open ball. -/
theorem le_norm_at_firstExitTimeRight {γ : ℝ → E} {t₀ δ ε : ℝ} {s : E}
    (hδ : 0 ≤ δ) (hγ_cont : ContinuousOn γ (Icc t₀ (t₀ + δ))) (hε_le : ε ≤ ‖γ (t₀ + δ) - s‖) :
    ε ≤ ‖γ (firstExitTimeRight γ t₀ δ s ε) - s‖ :=
  (((hγ_cont.sub continuousOn_const).norm.preimage_isClosed_of_isClosed
      isClosed_Icc isClosed_Ici).csInf_mem
    ⟨t₀ + δ, right_endpoint_mem hδ hε_le⟩
    ⟨t₀, right_set_bddBelow γ t₀ δ ε s⟩).2

/-- **The right exit time is strictly after the crossing** when `γ t₀ = s` and `0 < ε`. -/
theorem lt_firstExitTimeRight {γ : ℝ → E} {t₀ δ ε : ℝ} {s : E} (hδ : 0 < δ)
    (hγ_cont : ContinuousOn γ (Icc t₀ (t₀ + δ)))
    (h_s : γ t₀ = s) (hε_pos : 0 < ε) (hε_le : ε ≤ ‖γ (t₀ + δ) - s‖) :
    t₀ < firstExitTimeRight γ t₀ δ s ε := by
  have h_cont : ContinuousWithinAt (fun t => ‖γ t - s‖) (Icc t₀ (t₀ + δ)) t₀ :=
    ((hγ_cont t₀ ⟨le_rfl, by linarith⟩).sub continuousWithinAt_const).norm
  have h_eventually : ∀ᶠ t in 𝓝[Icc t₀ (t₀ + δ)] t₀, ‖γ t - s‖ < ε :=
    h_cont.tendsto.eventually_lt_const (by simp [h_s, hε_pos])
  obtain ⟨η, hη_pos, hη⟩ := Metric.nhdsWithin_basis_ball.eventually_iff.mp h_eventually
  refine lt_of_lt_of_le (a := t₀) (b := t₀ + min η δ / 2)
    (by linarith [lt_min hη_pos hδ]) ?_
  refine le_csInf ⟨t₀ + δ, right_endpoint_mem hδ.le hε_le⟩ fun t ht => ?_
  by_contra! h_lt
  have h_in_Icc : t ∈ Icc t₀ (t₀ + δ) := ht.1
  exact absurd ht.2 <| not_le.mpr <| hη ⟨Metric.mem_ball.mpr <| by
    rw [Real.dist_eq, abs_of_nonneg (by linarith [h_in_Icc.1] : 0 ≤ t - t₀)]
    linarith [min_le_left η δ], h_in_Icc⟩

/-- **Exact radius at the right exit time**: for `0 < ε ≤ ‖γ (t₀ + δ) - s‖`, the curve is at
distance exactly `ε` at `firstExitTimeRight γ t₀ δ s ε`. -/
theorem norm_at_firstExitTimeRight_eq {γ : ℝ → E} {t₀ δ ε : ℝ} {s : E}
    (hδ : 0 < δ) (hγ_cont : ContinuousOn γ (Icc t₀ (t₀ + δ)))
    (h_s : γ t₀ = s) (hε_pos : 0 < ε) (hε_le : ε ≤ ‖γ (t₀ + δ) - s‖) :
    ‖γ (firstExitTimeRight γ t₀ δ s ε) - s‖ = ε := by
  refine le_antisymm ?_ (le_norm_at_firstExitTimeRight hδ.le hγ_cont hε_le)
  set τ := firstExitTimeRight γ t₀ δ s ε
  have h_lt : t₀ < τ := lt_firstExitTimeRight hδ hγ_cont h_s hε_pos hε_le
  have h_mem : τ ∈ Icc t₀ (t₀ + δ) := firstExitTimeRight_mem_Icc hδ.le hε_le
  by_contra! h
  obtain ⟨η, hη_pos, hη⟩ := Metric.nhdsWithin_basis_ball.eventually_iff.mp <|
    (((hγ_cont τ h_mem).sub continuousWithinAt_const).norm.tendsto).eventually_const_lt h
  set r := min (η / 2) ((τ - t₀) / 2)
  have hr_pos : 0 < r := lt_min (by linarith) (by linarith)
  have h_in_Icc : τ - r ∈ Icc t₀ (t₀ + δ) :=
    ⟨by linarith [min_le_right (η / 2) ((τ - t₀) / 2)], by linarith [h_mem.2]⟩
  have h_dist : dist (τ - r) τ < η := by
    rw [Real.dist_eq, abs_of_neg (by linarith : τ - r - τ < 0)]
    linarith [min_le_left (η / 2) ((τ - t₀) / 2)]
  have h_inf_le : τ ≤ τ - r :=
    csInf_le ⟨t₀, right_set_bddBelow γ t₀ δ ε s⟩
      ⟨h_in_Icc, (hη ⟨Metric.mem_ball.mpr h_dist, h_in_Icc⟩).le⟩
  linarith

/-- **First exit time at radius `ε` (left side)**: the `sSup` of the times `t ∈ [t₀ - δ, t₀]`
with `ε ≤ ‖γ t - s‖` — the latest outside-the-ball time before `t₀`, which is the first exit
when approaching `t₀` from the left. -/
def firstExitTimeLeft (γ : ℝ → E) (t₀ δ : ℝ) (s : E) (ε : ℝ) : ℝ :=
  sSup {t ∈ Icc (t₀ - δ) t₀ | ε ≤ ‖γ t - s‖}

/-- The set defining `firstExitTimeLeft` contains the window endpoint when the curve is far
enough there. -/
private theorem left_endpoint_mem {γ : ℝ → E} {t₀ δ ε : ℝ} {s : E}
    (hδ : 0 ≤ δ) (h_far : ε ≤ ‖γ (t₀ - δ) - s‖) :
    (t₀ - δ) ∈ {t ∈ Icc (t₀ - δ) t₀ | ε ≤ ‖γ t - s‖} :=
  ⟨⟨le_rfl, by linarith⟩, h_far⟩

/-- The set defining `firstExitTimeLeft` is bounded above by `t₀`. -/
private theorem left_set_bddAbove (γ : ℝ → E) (t₀ δ ε : ℝ) (s : E) :
    ∀ t ∈ {t ∈ Icc (t₀ - δ) t₀ | ε ≤ ‖γ t - s‖}, t ≤ t₀ :=
  fun _ ⟨hmem, _⟩ => hmem.2

/-- **The left exit time lies in the window** `[t₀ - δ, t₀]`. -/
theorem firstExitTimeLeft_mem_Icc {γ : ℝ → E} {t₀ δ ε : ℝ} {s : E} (hδ : 0 ≤ δ)
    (hε_le : ε ≤ ‖γ (t₀ - δ) - s‖) :
    t₀ - δ ≤ firstExitTimeLeft γ t₀ δ s ε ∧ firstExitTimeLeft γ t₀ δ s ε ≤ t₀ :=
  ⟨le_csSup ⟨t₀, left_set_bddAbove γ t₀ δ ε s⟩ (left_endpoint_mem hδ hε_le),
    csSup_le ⟨t₀ - δ, left_endpoint_mem hδ hε_le⟩ (left_set_bddAbove γ t₀ δ ε s)⟩

/-- **Radius lower bound at the left exit time**: the `sSup` of the closed set of
outside-the-ball times is itself outside the open ball. -/
theorem le_norm_at_firstExitTimeLeft {γ : ℝ → E} {t₀ δ ε : ℝ} {s : E}
    (hδ : 0 ≤ δ) (hγ_cont : ContinuousOn γ (Icc (t₀ - δ) t₀)) (hε_le : ε ≤ ‖γ (t₀ - δ) - s‖) :
    ε ≤ ‖γ (firstExitTimeLeft γ t₀ δ s ε) - s‖ :=
  (((hγ_cont.sub continuousOn_const).norm.preimage_isClosed_of_isClosed
      isClosed_Icc isClosed_Ici).csSup_mem
    ⟨t₀ - δ, left_endpoint_mem hδ hε_le⟩
    ⟨t₀, left_set_bddAbove γ t₀ δ ε s⟩).2

/-- **The left exit time is strictly before the crossing**: the counterpart of
`lt_firstExitTimeRight`. -/
theorem firstExitTimeLeft_lt {γ : ℝ → E} {t₀ δ ε : ℝ} {s : E} (hδ : 0 < δ)
    (hγ_cont : ContinuousOn γ (Icc (t₀ - δ) t₀))
    (h_s : γ t₀ = s) (hε_pos : 0 < ε) (hε_le : ε ≤ ‖γ (t₀ - δ) - s‖) :
    firstExitTimeLeft γ t₀ δ s ε < t₀ := by
  have h_cont : ContinuousWithinAt (fun t => ‖γ t - s‖) (Icc (t₀ - δ) t₀) t₀ :=
    ((hγ_cont t₀ ⟨by linarith, le_rfl⟩).sub continuousWithinAt_const).norm
  have h_eventually : ∀ᶠ t in 𝓝[Icc (t₀ - δ) t₀] t₀, ‖γ t - s‖ < ε :=
    h_cont.tendsto.eventually_lt_const (by simp [h_s, hε_pos])
  obtain ⟨η, hη_pos, hη⟩ := Metric.nhdsWithin_basis_ball.eventually_iff.mp h_eventually
  refine lt_of_le_of_lt (a := firstExitTimeLeft γ t₀ δ s ε)
    (b := t₀ - min η δ / 2) ?_ (by linarith [lt_min hη_pos hδ])
  refine csSup_le ⟨t₀ - δ, left_endpoint_mem hδ.le hε_le⟩ fun t ht => ?_
  by_contra! h_lt
  have h_in_Icc : t ∈ Icc (t₀ - δ) t₀ := ht.1
  exact absurd ht.2 <| not_le.mpr <| hη ⟨Metric.mem_ball.mpr <| by
    rw [Real.dist_eq, abs_of_nonpos (by linarith [h_in_Icc.2] : t - t₀ ≤ 0)]
    linarith [min_le_left η δ], h_in_Icc⟩

/-- **Exact radius at the left exit time**: the counterpart of
`norm_at_firstExitTimeRight_eq`. -/
theorem norm_at_firstExitTimeLeft_eq {γ : ℝ → E} {t₀ δ ε : ℝ} {s : E}
    (hδ : 0 < δ) (hγ_cont : ContinuousOn γ (Icc (t₀ - δ) t₀))
    (h_s : γ t₀ = s) (hε_pos : 0 < ε) (hε_le : ε ≤ ‖γ (t₀ - δ) - s‖) :
    ‖γ (firstExitTimeLeft γ t₀ δ s ε) - s‖ = ε := by
  refine le_antisymm ?_ (le_norm_at_firstExitTimeLeft hδ.le hγ_cont hε_le)
  set τ := firstExitTimeLeft γ t₀ δ s ε
  have h_lt : τ < t₀ := firstExitTimeLeft_lt hδ hγ_cont h_s hε_pos hε_le
  have h_mem : τ ∈ Icc (t₀ - δ) t₀ := firstExitTimeLeft_mem_Icc hδ.le hε_le
  by_contra! h
  obtain ⟨η, hη_pos, hη⟩ := Metric.nhdsWithin_basis_ball.eventually_iff.mp <|
    (((hγ_cont τ h_mem).sub continuousWithinAt_const).norm.tendsto).eventually_const_lt h
  set r := min (η / 2) ((t₀ - τ) / 2)
  have hr_pos : 0 < r := lt_min (by linarith) (by linarith)
  have h_in_Icc : τ + r ∈ Icc (t₀ - δ) t₀ :=
    ⟨by linarith [h_mem.1], by linarith [min_le_right (η / 2) ((t₀ - τ) / 2)]⟩
  have h_dist : dist (τ + r) τ < η := by
    rw [Real.dist_eq, abs_of_pos (by linarith : 0 < τ + r - τ)]
    linarith [min_le_left (η / 2) ((t₀ - τ) / 2)]
  have h_sup_ge : τ + r ≤ τ :=
    le_csSup ⟨t₀, left_set_bddAbove γ t₀ δ ε s⟩
      ⟨h_in_Icc, (hη ⟨Metric.mem_ball.mpr h_dist, h_in_Icc⟩).le⟩
  linarith

/-- **Upper bound through any witness (right)**: the right exit time is at most any window
time already at distance `≥ ε`. -/
theorem firstExitTimeRight_le_of_mem {γ : ℝ → E} {t₀ δ ε : ℝ} {s : E}
    {t₁ : ℝ} (ht₁ : t₁ ∈ Icc t₀ (t₀ + δ)) (h_far : ε ≤ ‖γ t₁ - s‖) :
    firstExitTimeRight γ t₀ δ s ε ≤ t₁ :=
  csInf_le ⟨t₀, right_set_bddBelow γ t₀ δ ε s⟩ ⟨ht₁, h_far⟩

/-- **Lower bound through any witness (left)**: the left exit time is at least any window
time already at distance `≥ ε`. -/
theorem le_firstExitTimeLeft_of_mem {γ : ℝ → E} {t₀ δ ε : ℝ} {s : E}
    {t₁ : ℝ} (ht₁ : t₁ ∈ Icc (t₀ - δ) t₀) (h_far : ε ≤ ‖γ t₁ - s‖) :
    t₁ ≤ firstExitTimeLeft γ t₀ δ s ε :=
  le_csSup ⟨t₀, left_set_bddAbove γ t₀ δ ε s⟩ ⟨ht₁, h_far⟩

/-- **The right exit time tends to `t₀` from above as `ε → 0⁺`**, provided `γ` leaves `s` on
`(t₀, t₀ + δ]`. -/
theorem firstExitTimeRight_tendsto {γ : ℝ → E} {t₀ δ : ℝ} {s : E} (hδ : 0 < δ)
    (hγ_cont : ContinuousOn γ (Icc t₀ (t₀ + δ)))
    (h_s : γ t₀ = s) (h_leave : ∀ t ∈ Ioc t₀ (t₀ + δ), γ t ≠ s) :
    Tendsto (fun ε => firstExitTimeRight γ t₀ δ s ε) (𝓝[>] 0) (𝓝[>] t₀) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, ?_⟩
  · rw [Metric.tendsto_nhdsWithin_nhds]
    intro η hη_pos
    set t₁ := t₀ + min η δ / 2 with ht₁_def
    have ht₁_mem : t₁ ∈ Ioc t₀ (t₀ + δ) :=
      ⟨by linarith [lt_min hη_pos hδ], by linarith [min_le_right η δ]⟩
    refine ⟨‖γ t₁ - s‖, by simpa [norm_pos_iff, sub_ne_zero] using h_leave t₁ ht₁_mem, ?_⟩
    intro ε hε_pos hε_lt
    rw [Real.dist_eq, sub_zero, abs_of_pos hε_pos] at hε_lt
    have h_t₁_mem_Icc : t₁ ∈ Icc t₀ (t₀ + δ) := ⟨ht₁_mem.1.le, ht₁_mem.2⟩
    have h_t₀_le : t₀ ≤ firstExitTimeRight γ t₀ δ s ε :=
      le_csInf ⟨t₁, h_t₁_mem_Icc, hε_lt.le⟩ (right_set_bddBelow γ t₀ δ ε s)
    rw [Real.dist_eq, abs_of_nonneg (by linarith : 0 ≤ firstExitTimeRight γ t₀ δ s ε - t₀)]
    linarith [firstExitTimeRight_le_of_mem h_t₁_mem_Icc hε_lt.le, min_le_left η δ,
      show t₁ = t₀ + min η δ / 2 from ht₁_def]
  · have h_far_pos : (0 : ℝ) < ‖γ (t₀ + δ) - s‖ :=
      norm_pos_iff.mpr (sub_ne_zero.mpr (h_leave _ ⟨by linarith, le_rfl⟩))
    rw [eventually_iff_exists_mem]
    refine ⟨Ioo 0 ‖γ (t₀ + δ) - s‖, Ioo_mem_nhdsGT h_far_pos, fun ε hε => ?_⟩
    exact lt_firstExitTimeRight hδ hγ_cont h_s hε.1 hε.2.le

/-- **The left exit time tends to `t₀` from below as `ε → 0⁺`**: the counterpart of
`firstExitTimeRight_tendsto`. -/
theorem firstExitTimeLeft_tendsto {γ : ℝ → E} {t₀ δ : ℝ} {s : E} (hδ : 0 < δ)
    (hγ_cont : ContinuousOn γ (Icc (t₀ - δ) t₀))
    (h_s : γ t₀ = s) (h_leave : ∀ t ∈ Ico (t₀ - δ) t₀, γ t ≠ s) :
    Tendsto (fun ε => firstExitTimeLeft γ t₀ δ s ε) (𝓝[>] 0) (𝓝[<] t₀) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, ?_⟩
  · rw [Metric.tendsto_nhdsWithin_nhds]
    intro η hη_pos
    set t₁ := t₀ - min η δ / 2 with ht₁_def
    have ht₁_mem : t₁ ∈ Ico (t₀ - δ) t₀ :=
      ⟨by linarith [min_le_right η δ], by linarith [lt_min hη_pos hδ]⟩
    refine ⟨‖γ t₁ - s‖, by simpa [norm_pos_iff, sub_ne_zero] using h_leave t₁ ht₁_mem, ?_⟩
    intro ε hε_pos hε_lt
    rw [Real.dist_eq, sub_zero, abs_of_pos hε_pos] at hε_lt
    have h_t₁_mem_Icc : t₁ ∈ Icc (t₀ - δ) t₀ := ⟨ht₁_mem.1, ht₁_mem.2.le⟩
    have h_le : firstExitTimeLeft γ t₀ δ s ε ≤ t₀ :=
      csSup_le ⟨t₁, h_t₁_mem_Icc, hε_lt.le⟩ (left_set_bddAbove γ t₀ δ ε s)
    rw [Real.dist_eq, abs_of_nonpos
      (by linarith : firstExitTimeLeft γ t₀ δ s ε - t₀ ≤ 0)]
    linarith [le_firstExitTimeLeft_of_mem h_t₁_mem_Icc hε_lt.le, min_le_left η δ,
      show t₁ = t₀ - min η δ / 2 from ht₁_def]
  · have h_far_pos : (0 : ℝ) < ‖γ (t₀ - δ) - s‖ :=
      norm_pos_iff.mpr (sub_ne_zero.mpr (h_leave _ ⟨le_rfl, by linarith⟩))
    rw [eventually_iff_exists_mem]
    refine ⟨Ioo 0 ‖γ (t₀ - δ) - s‖, Ioo_mem_nhdsGT h_far_pos, fun ε hε => ?_⟩
    exact firstExitTimeLeft_lt hδ hγ_cont h_s hε.1 hε.2.le

/-- **Eventual exact radius (right)**: for all sufficiently small `ε > 0`, the right exit time
is at distance exactly `ε` — the radius hypothesis of
`Contour.antiderivative_diff_across_crossing_tendsto_zero`. -/
theorem eventually_norm_at_firstExitTimeRight_eq {γ : ℝ → E} {t₀ δ : ℝ} {s : E} (hδ : 0 < δ)
    (hγ_cont : ContinuousOn γ (Icc t₀ (t₀ + δ)))
    (h_s : γ t₀ = s) (h_leave : ∀ t ∈ Ioc t₀ (t₀ + δ), γ t ≠ s) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖γ (firstExitTimeRight γ t₀ δ s ε) - s‖ = ε := by
  have h_far_pos : (0 : ℝ) < ‖γ (t₀ + δ) - s‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr (h_leave _ ⟨by linarith, le_rfl⟩))
  filter_upwards [Ioo_mem_nhdsGT h_far_pos] with ε hε
  exact norm_at_firstExitTimeRight_eq hδ hγ_cont h_s hε.1 hε.2.le

/-- **Eventual exact radius (left)**: the counterpart of
`eventually_norm_at_firstExitTimeRight_eq`. -/
theorem eventually_norm_at_firstExitTimeLeft_eq {γ : ℝ → E} {t₀ δ : ℝ} {s : E} (hδ : 0 < δ)
    (hγ_cont : ContinuousOn γ (Icc (t₀ - δ) t₀))
    (h_s : γ t₀ = s) (h_leave : ∀ t ∈ Ico (t₀ - δ) t₀, γ t ≠ s) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖γ (firstExitTimeLeft γ t₀ δ s ε) - s‖ = ε := by
  have h_far_pos : (0 : ℝ) < ‖γ (t₀ - δ) - s‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr (h_leave _ ⟨le_rfl, by linarith⟩))
  filter_upwards [Ioo_mem_nhdsGT h_far_pos] with ε hε
  exact norm_at_firstExitTimeLeft_eq hδ hγ_cont h_s hε.1 hε.2.le

end TauCeti.Contour

end
