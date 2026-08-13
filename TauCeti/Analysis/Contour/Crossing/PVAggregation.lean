/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import TauCeti.Analysis.Contour.Cauchy.PrincipalValue.Basic
import Mathlib.Data.Finset.Sort
import TauCeti.Analysis.Contour.Crossing.Windows

/-!
# Aggregating per-window principal values across finitely many crossings

If the `ε`-truncated integral of `g (γ t) * deriv γ t` converges on each crossing window
`[t_i - r, t_i + r]`, the windows have disjoint interiors and lie in `[a, b]`, and the curve
keeps a positive distance from `s` off the windows, then the truncated integral over all of
`[a, b]` converges — the single-point principal value exists
(`cauchyPVExistsAt_of_perWindow_tendsto_of_interiorDisjoint`). Off the windows the truncation
is eventually
inactive and each between-piece integral is constant; the windows contribute their given
limits; the pieces concatenate (`HasCauchyPVAt.concat`) along the sorted crossing list.

The per-window limits are hypotheses, so one aggregation serves every integrand: the
simple-pole and higher-order per-window theorems both discharge them.

## Main results

* `Contour.cauchyPVExistsAt_of_perWindow_tendsto_of_interiorDisjoint` — the single-point
  principal value on `[a, b]` from per-window convergence at finitely many crossings. The
  windows need only have disjoint *interiors* and lie in `[a, b]`, so they may touch each
  other, or touch `a` or `b`; and the radius bound is required only when there is a window.
* `Contour.hasCauchyPVAt_of_perWindow_boundary_tendsto_of_interiorDisjoint` — the telescoping
  form: when the integrand has a curve-antiderivative `Φ` off the pole and each window limit is
  the boundary difference of `Φ ∘ γ`, the principal value is `Φ (γ b) - Φ (γ a)` — zero around
  a closed curve.
* `Contour.exists_hasCauchyPVAt_re_eq_of_perWindow_tendsto_of_interiorDisjoint` — like the first
  form above, but returns the aggregated value explicitly and pins its **real part** to the
  difference of a real boundary function `Ψ`, given only the real part of each piece and window
  value. Weaker than the telescoping form's shared complex antiderivative `Φ`, so it applies even
  when different windows need different branch choices for their imaginary part.
All three instantiate `Contour.sorted_crossing_gluing_induction` (`Crossing.Windows`), the
sorted-crossing-list geometry generalized to an arbitrary invariant `Q : ℝ → ℝ → Prop` closed
under concatenation, including the value-carrying instantiations here (existential `HasCauchyPVAt`
witnesses, or a known closed form) — so none needs its own copy of the recursion.

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

/-- The truncated integrand is eventually interval-integrable on a crossing window lying in
`[a, b]`, by restriction. -/
private theorem eventually_intervalIntegrable_truncated_window {γ : ℝ → ℂ} {s : ℂ}
    {g : ℂ → ℂ} {a b r t : ℝ} (hab : a ≤ b) (h_lo : a ≤ t - r) (h_hi : t + r ≤ b)
    (hr_nonneg : 0 ≤ r) (h_int_tr : ∀ ε : ℝ, 0 < ε →
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
    (hab : a ≤ b) (hm_pos : 0 < m) (h_int_tr : ∀ ε : ℝ, 0 < ε →
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

/-- **Real-part boundary aggregation**: like
`cauchyPVExistsAt_of_perWindow_tendsto_of_interiorDisjoint`, but each plain piece and each window
additionally has its **real part** pinned to the difference of a real boundary function `Ψ` —
weaker than sharing one complex antiderivative `Φ` across every window, as
`hasCauchyPVAt_of_perWindow_boundary_tendsto_of_interiorDisjoint` requires (different windows may
need different branch choices for their imaginary part, so no single `Φ` need exist). Returns the
aggregated principal value explicitly, together with the fact that its real part telescopes to
`Ψ b - Ψ a`. -/
theorem exists_hasCauchyPVAt_re_eq_of_perWindow_tendsto_of_interiorDisjoint
    {γ : ℝ → ℂ} {s : ℂ} {g : ℂ → ℂ} {Ψ : ℝ → ℝ} {a b r m : ℝ}
    (hab : a ≤ b) (crossings : Finset ℝ) (hr_nonneg : crossings.Nonempty → 0 ≤ r)
    (h_lo : ∀ t ∈ crossings, a ≤ t - r) (h_hi : ∀ t ∈ crossings, t + r ≤ b)
    (h_pair : ∀ t ∈ crossings, ∀ t' ∈ crossings, t' ≠ t → 2 * r ≤ |t - t'|)
    (h_int_tr : ∀ ε : ℝ, 0 < ε →
      IntervalIntegrable (fun t => if ‖γ t - s‖ > ε then g (γ t) * deriv γ t else 0)
        MeasureTheory.volume a b)
    (h_piece_re : ∀ l u : ℝ, a ≤ l → l ≤ u → u ≤ b → (∀ t ∈ Icc l u, m ≤ ‖γ t - s‖) →
      (∫ t in l..u, g (γ t) * deriv γ t).re = Ψ u - Ψ l)
    (h_win : ∀ t ∈ crossings, ∃ v : ℂ, v.re = Ψ (t + r) - Ψ (t - r) ∧
      Tendsto (fun ε : ℝ => ∫ u in (t - r)..(t + r),
        if ‖γ u - s‖ > ε then g (γ u) * deriv γ u else 0) (𝓝[>] (0 : ℝ)) (𝓝 v))
    (h_far : 0 < m ∧ ∀ u ∈ Icc a b, (∀ t ∈ crossings, u ∉ Ioo (t - r) (t + r)) → m ≤ ‖γ u - s‖) :
    ∃ L : ℂ, HasCauchyPVAt γ a b g s L ∧ L.re = Ψ b - Ψ a := by
  classical
  obtain ⟨hm_pos, hm⟩ := h_far
  exact sorted_crossing_gluing_induction
    (Q := fun l u => ∃ v : ℂ, HasCauchyPVAt γ l u g s v ∧ v.re = Ψ u - Ψ l)
    (fun l u hA hlu hu h_far' => ⟨_,
      hasCauchyPVAt_plain_piece hab hm_pos h_int_tr hA hlu hu h_far',
      h_piece_re l u hA hlu hu h_far'⟩)
    (fun _ _ _ _ _ ⟨v₁, h₁, r₁⟩ ⟨v₂, h₂, r₂⟩ =>
      ⟨v₁ + v₂, h₁.concat h₂, by rw [Complex.add_re, r₁, r₂]; ring⟩)
    (crossings.sort (· ≤ ·)) (Finset.sortedLT_sort crossings)
    (fun h => hr_nonneg (Finset.nonempty_iff_ne_empty.mpr fun he => h (by simp [he])))
    a le_rfl hab
    (fun t ht => h_lo t ((Finset.mem_sort _).mp ht))
    (fun t ht => h_hi t ((Finset.mem_sort _).mp ht))
    (fun t ht t' ht' hne => h_pair t ((Finset.mem_sort _).mp ht)
      t' ((Finset.mem_sort _).mp ht') hne)
    (fun t ht => by
      have h_mem := (Finset.mem_sort (α := ℝ) (· ≤ ·)).mp ht
      obtain ⟨v, hv_re, hv_tendsto⟩ := h_win t h_mem
      exact ⟨v, hasCauchyPVAt_iff.mpr ⟨eventually_intervalIntegrable_truncated_window hab
        (h_lo t h_mem) (h_hi t h_mem) (hr_nonneg ⟨t, h_mem⟩) h_int_tr, hv_tendsto⟩, hv_re⟩)
    (fun u hu h_avoid => hm u hu fun t ht => h_avoid t ((Finset.mem_sort _).mpr ht))

/-- **The single-point principal value from per-window convergence**: if the `ε`-truncated
integral of `g (γ t) * deriv γ t` converges on each crossing window (disjoint interiors,
lying in `[a, b]` — they may touch each other, or touch `a` or `b`), the truncations are
integrable on `[a, b]`, and the curve keeps a
positive distance from `s` off the windows, then the principal value at `s` exists on
`[a, b]`. The per-window limits are hypotheses, so both the simple-pole and higher-order
per-window theorems discharge them. -/
theorem cauchyPVExistsAt_of_perWindow_tendsto_of_interiorDisjoint {γ : ℝ → ℂ} {s : ℂ} {g : ℂ → ℂ}
    {a b r : ℝ} (hab : a ≤ b) (crossings : Finset ℝ) (hr_nonneg : crossings.Nonempty → 0 ≤ r)
    (h_lo : ∀ t ∈ crossings, a ≤ t - r) (h_hi : ∀ t ∈ crossings, t + r ≤ b)
    (h_pair : ∀ t ∈ crossings, ∀ t' ∈ crossings, t' ≠ t → 2 * r ≤ |t - t'|)
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
  obtain ⟨v, hv⟩ := sorted_crossing_gluing_induction
    (Q := fun l u => ∃ v : ℂ, HasCauchyPVAt γ l u g s v)
    (fun l u hA hlu hu h_far' =>
      ⟨_, hasCauchyPVAt_plain_piece hab hm_pos h_int_tr hA hlu hu h_far'⟩)
    (fun _ _ _ _ _ ⟨v₁, h₁⟩ ⟨v₂, h₂⟩ => ⟨v₁ + v₂, h₁.concat h₂⟩)
    (crossings.sort (· ≤ ·)) (Finset.sortedLT_sort crossings)
    (fun h => hr_nonneg (Finset.nonempty_iff_ne_empty.mpr fun he => h (by simp [he])))
    a le_rfl hab
    (fun t ht => h_lo t ((Finset.mem_sort _).mp ht))
    (fun t ht => h_hi t ((Finset.mem_sort _).mp ht))
    (fun t ht t' ht' hne => h_pair t ((Finset.mem_sort _).mp ht)
      t' ((Finset.mem_sort _).mp ht') hne)
    (fun t ht => by
      have h_mem := (Finset.mem_sort (α := ℝ) (· ≤ ·)).mp ht
      obtain ⟨v, hv⟩ := h_win t h_mem
      exact ⟨v, hasCauchyPVAt_iff.mpr ⟨eventually_intervalIntegrable_truncated_window hab
        (h_lo t h_mem) (h_hi t h_mem) (hr_nonneg ⟨t, h_mem⟩) h_int_tr, hv⟩⟩)
    (fun u hu h_avoid => hm u hu fun t ht => h_avoid t ((Finset.mem_sort _).mpr ht))
  exact CauchyPVExistsAt.intro hv

/-- **Telescoping per-window aggregation**: when the plain integrand has a curve-antiderivative
`Φ` on pole-free pieces and each window limit is the boundary difference of `Φ ∘ γ`, the
principal value on `[a, b]` is `Φ (γ b) - Φ (γ a)` — in particular zero around a closed curve.
The higher-order per-window limits have exactly this boundary-difference shape. -/
theorem hasCauchyPVAt_of_perWindow_boundary_tendsto_of_interiorDisjoint {γ : ℝ → ℂ} {s : ℂ}
    {g : ℂ → ℂ} {Φ : ℂ → ℂ} {a b r : ℝ} (hab : a ≤ b) (crossings : Finset ℝ)
    (hr_nonneg : crossings.Nonempty → 0 ≤ r)
    (h_lo : ∀ t ∈ crossings, a ≤ t - r) (h_hi : ∀ t ∈ crossings, t + r ≤ b)
    (h_pair : ∀ t ∈ crossings, ∀ t' ∈ crossings, t' ≠ t → 2 * r ≤ |t - t'|)
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
  exact sorted_crossing_gluing_induction
    (Q := fun l u => HasCauchyPVAt γ l u g s (Φ (γ u) - Φ (γ l)))
    (fun l u hA hlu hu h_far' => by
      have h_ne : ∀ t ∈ Icc l u, γ t ≠ s := fun t ht h_eq => by
        have h_bd := h_far' t ht
        rw [h_eq, sub_self, norm_zero] at h_bd
        linarith
      have h0 := hasCauchyPVAt_plain_piece hab hm_pos h_int_tr hA hlu hu h_far'
      rwa [h_plain_eq l u hA hlu hu h_ne] at h0)
    (fun l u₀ u _ _ h₁ h₂ => by
      have h0 := h₁.concat h₂
      have h_tel : (Φ (γ u₀) - Φ (γ l)) + (Φ (γ u) - Φ (γ u₀)) = Φ (γ u) - Φ (γ l) := by ring
      rwa [h_tel] at h0)
    (crossings.sort (· ≤ ·)) (Finset.sortedLT_sort crossings)
    (fun h => hr_nonneg (Finset.nonempty_iff_ne_empty.mpr fun he => h (by simp [he])))
    a le_rfl hab
    (fun t ht => h_lo t ((Finset.mem_sort _).mp ht))
    (fun t ht => h_hi t ((Finset.mem_sort _).mp ht))
    (fun t ht t' ht' hne => h_pair t ((Finset.mem_sort _).mp ht)
      t' ((Finset.mem_sort _).mp ht') hne)
    (fun t ht => by
      have h_mem := (Finset.mem_sort (α := ℝ) (· ≤ ·)).mp ht
      exact hasCauchyPVAt_iff.mpr ⟨eventually_intervalIntegrable_truncated_window hab
        (h_lo t h_mem) (h_hi t h_mem) (hr_nonneg ⟨t, h_mem⟩) h_int_tr, h_win t h_mem⟩)
    (fun u hu h_avoid => hm u hu fun t ht => h_avoid t ((Finset.mem_sort _).mpr ht))

end TauCeti.Contour

end
