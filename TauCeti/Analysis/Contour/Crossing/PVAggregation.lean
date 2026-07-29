/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import TauCeti.Analysis.Contour.Cauchy.PrincipalValue.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Sort

/-!
# Aggregating per-window principal values across finitely many crossings

If the `ε`-truncated integral of `g (γ t) * deriv γ t` converges on each crossing window
`[t_i - r, t_i + r]`, the windows are pairwise disjoint and interior to `[a, b]`, and the curve
keeps a positive distance from `s` off the windows, then the truncated integral over all of
`[a, b]` converges — the single-point principal value exists
(`cauchyPVExistsAt_of_perWindow_tendsto`). Off the windows the truncation is eventually
inactive and each between-piece integral is constant; the windows contribute their given
limits; the pieces concatenate (`HasCauchyPVAt.concat`) along the sorted crossing list.

The per-window limits are hypotheses, so one aggregation serves every integrand: the
simple-pole and higher-order per-window theorems both discharge them.

## Main results

* `Contour.cauchyPVExistsAt_of_perWindow_tendsto` — the single-point principal value on
  `[a, b]` from per-window convergence at finitely many crossings.
* `Contour.hasCauchyPVAt_of_perWindow_boundary_tendsto` — the telescoping form: when the
  integrand has a curve-antiderivative `Φ` off the pole and each window limit is the boundary
  difference of `Φ ∘ γ`, the principal value is `Φ (γ b) - Φ (γ a)` — zero around a closed
  curve.

## Provenance

Migrated from `cpv_tendsto_along_sorted_corner`, `cpv_higherOrder_tendsto_along_sorted_corner`
and the aggregation steps of `hasCauchyPV_inv_sub_multiCrossing_corner` and
`hasCauchyPVOn_multiCrossing_higherOrder_corner` of `MultiCrossingCPV.lean` in the AINTLIB
`LeanModularForms` development, restated for a raw curve on `[a, b]` with a generic integrand
and, in the telescoping form, a generic antiderivative (there the inductions are instantiated
separately for the simple-pole and higher-order integrands). See N. Hungerbühler, M. Wasem,
*Non-integer valued winding numbers and a generalized Residue Theorem*, arXiv:1808.00997, §3.
-/

public section

noncomputable section

namespace TauCeti.Contour

open Filter MeasureTheory Set Topology

/-- The truncated integrand is eventually interval-integrable on a crossing window interior to
`[a, b]`, by restriction. -/
private theorem eventually_intervalIntegrable_truncated_window {γ : ℝ → ℂ} {s : ℂ}
    {g : ℂ → ℂ} {a b r t : ℝ} (hab : a ≤ b) (h_lo : a < t - r) (h_hi : t + r ≤ b)
    (hr_pos : 0 < r)
    (h_int_tr : ∀ ε : ℝ, 0 < ε →
      IntervalIntegrable (fun u => if ‖γ u - s‖ > ε then g (γ u) * deriv γ u else 0)
        MeasureTheory.volume a b) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      IntervalIntegrable (fun u => if ‖γ u - s‖ > ε then g (γ u) * deriv γ u else 0)
        MeasureTheory.volume (t - r) (t + r) := by
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (h_int_tr ε hε).mono_set (by
    rw [uIcc_of_le (show t - r ≤ t + r by linarith), uIcc_of_le hab]
    exact Icc_subset_Icc (by linarith) h_hi)

/-- The between-piece principal value on a subinterval of `[a, b]` keeping distance `≥ m` from
`s`: the plain integral, with the truncated integrability restricted from `[a, b]`. Both public
aggregations discharge their piece hypothesis through this. -/
private theorem hasCauchyPVAt_plain_piece {γ : ℝ → ℂ} {s : ℂ} {g : ℂ → ℂ} {a b m : ℝ}
    (hab : a ≤ b) (hm_pos : 0 < m)
    (h_int_tr : ∀ ε : ℝ, 0 < ε →
      IntervalIntegrable (fun t => if ‖γ t - s‖ > ε then g (γ t) * deriv γ t else 0)
        MeasureTheory.volume a b)
    {l u : ℝ} (hA : a ≤ l) (hlu : l ≤ u) (hu : u ≤ b)
    (h_far : ∀ t ∈ Icc l u, m ≤ ‖γ t - s‖) :
    HasCauchyPVAt γ l u g s (∫ t in l..u, g (γ t) * deriv γ t) :=
  HasCauchyPVAt.of_dist_lower_bound hm_pos (by rwa [uIcc_of_le hlu]) <| by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (h_int_tr ε hε).mono_set (by
      rw [uIcc_of_le hlu, uIcc_of_le hab]
      exact Icc_subset_Icc hA hu)

/-- The aggregated value along a sorted crossing list: between-piece values `p` alternating
with window values `w`. -/
private def windowPieceSum (r : ℝ) (p : ℝ → ℝ → ℂ) (w : ℝ → ℂ) (b : ℝ) :
    List ℝ → ℝ → ℂ
  | [], a => p a b
  | t :: rest, a => p a (t - r) + w t + windowPieceSum r p w b rest (t + r)

/-- **The shared aggregation induction**: with pairwise-disjoint windows interior to `[a, b]`,
window principal values `w t`, and between-piece principal values `p l u` available on
intervals where the curve keeps distance `≥ m` from `s`, the principal value on `[a, b]` is
the alternating sum `windowPieceSum`. Both public aggregation theorems instantiate this. -/
private theorem hasCauchyPVAt_along_sorted {γ : ℝ → ℂ} {s : ℂ} {g : ℂ → ℂ}
    {p : ℝ → ℝ → ℂ} {w : ℝ → ℂ} {A b r m : ℝ} (hr_pos : 0 < r)
    (h_piece : ∀ l u : ℝ, A ≤ l → l ≤ u → u ≤ b → (∀ t ∈ Icc l u, m ≤ ‖γ t - s‖) →
      HasCauchyPVAt γ l u g s (p l u)) :
    ∀ (sorted : List ℝ), sorted.SortedLT →
    ∀ a : ℝ, A ≤ a → a ≤ b → (∀ t ∈ sorted, a < t - r) → (∀ t ∈ sorted, t + r ≤ b) →
      (∀ t ∈ sorted, ∀ t' ∈ sorted, t' ≠ t → 2 * r < |t - t'|) →
      (∀ t ∈ sorted, HasCauchyPVAt γ (t - r) (t + r) g s (w t)) →
      (∀ u ∈ Icc a b, (∀ t ∈ sorted, u ∉ Ioo (t - r) (t + r)) → m ≤ ‖γ u - s‖) →
      HasCauchyPVAt γ a b g s (windowPieceSum r p w b sorted a) := by
  intro sorted
  induction sorted with
  | nil =>
    intro _ a hA hab _ _ _ _ h_far
    exact h_piece a b hA hab le_rfl
      fun u hu => h_far u hu fun t ht => absurd ht (List.not_mem_nil)
  | cons t rest IH =>
    intro h_sorted a hA hab h_lo h_hi h_pair h_win h_far
    have h_head_lo : a < t - r := h_lo t List.mem_cons_self
    have h_head_hi : t + r ≤ b := h_hi t List.mem_cons_self
    have h_rest_above : ∀ t' ∈ rest, t + r < t' - r := fun t' ht' => by
      have h_lt : t < t' := (List.pairwise_cons.mp h_sorted.pairwise).1 t' ht'
      have h_sep := h_pair t List.mem_cons_self t' (List.mem_cons_of_mem t ht')
        (ne_of_gt h_lt)
      rw [abs_sub_comm, abs_of_pos (by linarith)] at h_sep
      linarith
    have h_left : HasCauchyPVAt γ a (t - r) g s (p a (t - r)) := by
      refine h_piece a (t - r) hA h_head_lo.le (by linarith) fun u hu => ?_
      refine h_far u ⟨hu.1, by linarith [hu.2]⟩ fun t' ht' h_in => ?_
      rcases List.mem_cons.mp ht' with rfl | h_rest
      · linarith [hu.2, h_in.1]
      · linarith [hu.2, h_in.1, h_rest_above t' h_rest]
    have h_rest : HasCauchyPVAt γ (t + r) b g s
        (windowPieceSum r p w b rest (t + r)) := IH
      ((List.pairwise_cons.mp h_sorted.pairwise).2).sortedLT (t + r)
      (by linarith) h_head_hi
      (fun t' ht' => h_rest_above t' ht')
      (fun t' ht' => h_hi t' (List.mem_cons_of_mem t ht'))
      (fun t' ht' t'' ht'' hne => h_pair t' (List.mem_cons_of_mem t ht')
        t'' (List.mem_cons_of_mem t ht'') hne)
      (fun t' ht' => h_win t' (List.mem_cons_of_mem t ht'))
      (fun u hu h_avoid => h_far u ⟨by linarith [hu.1], hu.2⟩ fun t' ht' => by
        rcases List.mem_cons.mp ht' with rfl | h_rest
        · exact fun h_in => absurd hu.1 (not_le.mpr h_in.2)
        · exact h_avoid t' h_rest)
    exact (h_left.concat (h_win t List.mem_cons_self)).concat h_rest

/-- **The single-point principal value from per-window convergence**: if the `ε`-truncated
integral of `g (γ t) * deriv γ t` converges on each crossing window (pairwise disjoint,
interior to `[a, b]`), the truncations are integrable on `[a, b]`, and the curve keeps a
positive distance from `s` off the windows, then the principal value at `s` exists on
`[a, b]`. The per-window limits are hypotheses, so both the simple-pole and higher-order
per-window theorems discharge them. -/
theorem cauchyPVExistsAt_of_perWindow_tendsto {γ : ℝ → ℂ} {s : ℂ} {g : ℂ → ℂ}
    {a b r : ℝ} (hr_pos : 0 < r) (hab : a ≤ b) (crossings : Finset ℝ)
    (h_lo : ∀ t ∈ crossings, a < t - r) (h_hi : ∀ t ∈ crossings, t + r ≤ b)
    (h_pair : ∀ t ∈ crossings, ∀ t' ∈ crossings, t' ≠ t → 2 * r < |t - t'|)
    (h_int_tr : ∀ ε : ℝ, 0 < ε →
      IntervalIntegrable (fun t => if ‖γ t - s‖ > ε then g (γ t) * deriv γ t else 0)
        MeasureTheory.volume a b)
    (h_win : ∀ t ∈ crossings, ∃ v : ℂ, Tendsto (fun ε : ℝ => ∫ u in (t - r)..(t + r),
        if ‖γ u - s‖ > ε then g (γ u) * deriv γ u else 0) (𝓝[>] (0 : ℝ)) (𝓝 v))
    (h_far : ∃ m : ℝ, 0 < m ∧ ∀ u ∈ Icc a b, (∀ t ∈ crossings, u ∉ Ioo (t - r) (t + r)) →
      m ≤ ‖γ u - s‖) :
    CauchyPVExistsAt γ a b g s := by
  classical
  obtain ⟨m, hm_pos, hm⟩ := h_far
  refine CauchyPVExistsAt.intro (hasCauchyPVAt_along_sorted hr_pos
    (p := fun l u => ∫ t in l..u, g (γ t) * deriv γ t)
    (w := fun t => if h : t ∈ crossings then (h_win t h).choose else 0)
    (fun l u hA hlu hu h_far' => hasCauchyPVAt_plain_piece hab hm_pos h_int_tr hA hlu hu h_far')
    (crossings.sort (· ≤ ·)) (Finset.sortedLT_sort crossings) a le_rfl hab
    (fun t ht => h_lo t ((Finset.mem_sort _).mp ht))
    (fun t ht => h_hi t ((Finset.mem_sort _).mp ht))
    (fun t ht t' ht' hne => h_pair t ((Finset.mem_sort _).mp ht)
      t' ((Finset.mem_sort _).mp ht') hne)
    (fun t ht => ?_)
    (fun u hu h_avoid => hm u hu fun t ht => h_avoid t ((Finset.mem_sort _).mpr ht)))
  have h_mem := (Finset.mem_sort (α := ℝ) (· ≤ ·)).mp ht
  refine hasCauchyPVAt_iff.mpr ⟨eventually_intervalIntegrable_truncated_window hab
    (h_lo t h_mem) (h_hi t h_mem) hr_pos h_int_tr, ?_⟩
  rw [dif_pos h_mem]
  exact (h_win t h_mem).choose_spec

/-- The alternating sum telescopes when both the piece and window values are boundary
differences of `Φ ∘ γ`. -/
private theorem windowPieceSum_boundary {γ : ℝ → ℂ} {Φ : ℂ → ℂ} {b r : ℝ} :
    ∀ (sorted : List ℝ) (a : ℝ),
      windowPieceSum r (fun l u => Φ (γ u) - Φ (γ l))
        (fun t => Φ (γ (t + r)) - Φ (γ (t - r))) b sorted a = Φ (γ b) - Φ (γ a)
  | [], a => rfl
  | t :: rest, a => by
    rw [windowPieceSum, windowPieceSum_boundary rest (t + r)]
    ring

/-- **Telescoping per-window aggregation**: when the plain integrand has a curve-antiderivative
`Φ` on pole-free pieces and each window limit is the boundary difference of `Φ ∘ γ`, the
principal value on `[a, b]` is `Φ (γ b) - Φ (γ a)` — in particular zero around a closed curve.
The higher-order per-window limits have exactly this boundary-difference shape. -/
theorem hasCauchyPVAt_of_perWindow_boundary_tendsto {γ : ℝ → ℂ} {s : ℂ} {g : ℂ → ℂ}
    {Φ : ℂ → ℂ} {a b r : ℝ} (hr_pos : 0 < r) (hab : a ≤ b) (crossings : Finset ℝ)
    (h_lo : ∀ t ∈ crossings, a < t - r) (h_hi : ∀ t ∈ crossings, t + r ≤ b)
    (h_pair : ∀ t ∈ crossings, ∀ t' ∈ crossings, t' ≠ t → 2 * r < |t - t'|)
    (h_int_tr : ∀ ε : ℝ, 0 < ε →
      IntervalIntegrable (fun t => if ‖γ t - s‖ > ε then g (γ t) * deriv γ t else 0)
        MeasureTheory.volume a b)
    (h_plain_eq : ∀ l u : ℝ, a ≤ l → l ≤ u → u ≤ b → (∀ t ∈ Icc l u, γ t ≠ s) →
      ∫ t in l..u, g (γ t) * deriv γ t = Φ (γ u) - Φ (γ l))
    (h_win : ∀ t ∈ crossings, Tendsto (fun ε : ℝ => ∫ u in (t - r)..(t + r),
        if ‖γ u - s‖ > ε then g (γ u) * deriv γ u else 0) (𝓝[>] (0 : ℝ))
        (𝓝 (Φ (γ (t + r)) - Φ (γ (t - r)))))
    (h_far : ∃ m : ℝ, 0 < m ∧ ∀ u ∈ Icc a b, (∀ t ∈ crossings, u ∉ Ioo (t - r) (t + r)) →
      m ≤ ‖γ u - s‖) :
    HasCauchyPVAt γ a b g s (Φ (γ b) - Φ (γ a)) := by
  classical
  obtain ⟨m, hm_pos, hm⟩ := h_far
  have h := hasCauchyPVAt_along_sorted hr_pos
    (p := fun l u => Φ (γ u) - Φ (γ l))
    (w := fun t => Φ (γ (t + r)) - Φ (γ (t - r)))
    (fun l u hA hlu hu h_far' => by
      have h_ne : ∀ t ∈ Icc l u, γ t ≠ s := fun t ht h_eq => by
        have h_bd := h_far' t ht
        rw [h_eq, sub_self, norm_zero] at h_bd
        linarith
      have h0 := hasCauchyPVAt_plain_piece hab hm_pos h_int_tr hA hlu hu h_far'
      rwa [h_plain_eq l u hA hlu hu h_ne] at h0)
    (crossings.sort (· ≤ ·)) (Finset.sortedLT_sort crossings) a le_rfl hab
    (fun t ht => h_lo t ((Finset.mem_sort _).mp ht))
    (fun t ht => h_hi t ((Finset.mem_sort _).mp ht))
    (fun t ht t' ht' hne => h_pair t ((Finset.mem_sort _).mp ht)
      t' ((Finset.mem_sort _).mp ht') hne)
    (fun t ht => by
      have h_mem := (Finset.mem_sort (α := ℝ) (· ≤ ·)).mp ht
      exact hasCauchyPVAt_iff.mpr ⟨eventually_intervalIntegrable_truncated_window hab
        (h_lo t h_mem) (h_hi t h_mem) hr_pos h_int_tr, h_win t h_mem⟩)
    (fun u hu h_avoid => hm u hu fun t ht => h_avoid t ((Finset.mem_sort _).mpr ht))
  rwa [windowPieceSum_boundary] at h

end TauCeti.Contour

end
