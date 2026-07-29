/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import TauCeti.Analysis.Contour.Cauchy.PrincipalValue.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.BigOperators.Group.Finset.Gaps
import Mathlib.Data.List.Sort

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
* `Contour.cauchyPVExistsAt_of_perWindow_tendsto` and
  `Contour.hasCauchyPVAt_of_perWindow_boundary_tendsto` — the strict special cases of those
  two, for windows strictly separated from each other and starting strictly after `a` — their
  right edges may already reach `b`, since `h_hi` is `t + r ≤ b`. They cannot express windows
  that touch each other or that start at `a`; reach for the `_of_interiorDisjoint` forms above
  when either matters.

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

open scoped Fin.NatCast

/-- The truncated integrand is eventually interval-integrable on a crossing window lying in
`[a, b]`, by restriction. -/
private theorem eventually_intervalIntegrable_truncated_window {γ : ℝ → ℂ} {s : ℂ}
    {g : ℂ → ℂ} {a b r t : ℝ} (hab : a ≤ b) (h_lo : a ≤ t - r) (h_hi : t + r ≤ b)
    (hr_nonneg : 0 ≤ r)
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

/-- The aggregated value along a sorted crossing list: between-piece values `p` interleaved
with window values `w`. -/
private def windowPieceSum (r : ℝ) (p : ℝ → ℝ → ℂ) (w : ℝ → ℂ) (b : ℝ) :
    List ℝ → ℝ → ℂ
  | [], a => p a b
  | t :: rest, a => p a (t - r) + w t + windowPieceSum r p w b rest (t + r)

/-- **The shared aggregation induction**: with windows of disjoint interiors lying in `[a, b]`,
window principal values `w t`, and between-piece principal values `p l u` available on
intervals where the curve keeps distance `≥ m` from `s`, the principal value on `[a, b]` is
the interleaved sum `windowPieceSum`. Both public aggregation theorems instantiate this. -/
private theorem hasCauchyPVAt_along_sorted {γ : ℝ → ℂ} {s : ℂ} {g : ℂ → ℂ}
    {p : ℝ → ℝ → ℂ} {w : ℝ → ℂ} {A b r m : ℝ}
    (h_piece : ∀ l u : ℝ, A ≤ l → l ≤ u → u ≤ b → (∀ t ∈ Icc l u, m ≤ ‖γ t - s‖) →
      HasCauchyPVAt γ l u g s (p l u)) :
    ∀ (sorted : List ℝ), sorted.SortedLT → (sorted ≠ [] → 0 ≤ r) →
    ∀ a : ℝ, A ≤ a → a ≤ b → (∀ t ∈ sorted, a ≤ t - r) → (∀ t ∈ sorted, t + r ≤ b) →
      (∀ t ∈ sorted, ∀ t' ∈ sorted, t' ≠ t → 2 * r ≤ |t - t'|) →
      (∀ t ∈ sorted, HasCauchyPVAt γ (t - r) (t + r) g s (w t)) →
      (∀ u ∈ Icc a b, (∀ t ∈ sorted, u ∉ Ioo (t - r) (t + r)) → m ≤ ‖γ u - s‖) →
      HasCauchyPVAt γ a b g s (windowPieceSum r p w b sorted a) := by
  intro sorted
  induction sorted with
  | nil =>
    intro _ _ a hA hab _ _ _ _ h_far
    exact h_piece a b hA hab le_rfl
      fun u hu => h_far u hu fun t ht => absurd ht (List.not_mem_nil)
  | cons t rest IH =>
    intro h_sorted hr a hA hab h_lo h_hi h_pair h_win h_far
    have hr_nonneg : 0 ≤ r := hr (List.cons_ne_nil t rest)
    have h_head_lo : a ≤ t - r := h_lo t List.mem_cons_self
    have h_head_hi : t + r ≤ b := h_hi t List.mem_cons_self
    have h_rest_above : ∀ t' ∈ rest, t + r ≤ t' - r := fun t' ht' => by
      have h_lt : t < t' := (List.pairwise_cons.mp h_sorted.pairwise).1 t' ht'
      have h_sep := h_pair t List.mem_cons_self t' (List.mem_cons_of_mem t ht')
        (ne_of_gt h_lt)
      rw [abs_sub_comm, abs_of_pos (by linarith)] at h_sep
      linarith
    have h_left : HasCauchyPVAt γ a (t - r) g s (p a (t - r)) := by
      refine h_piece a (t - r) hA h_head_lo (by linarith) fun u hu => ?_
      refine h_far u ⟨hu.1, by linarith [hu.2]⟩ fun t' ht' h_in => ?_
      rcases List.mem_cons.mp ht' with rfl | h_rest
      · linarith [hu.2, h_in.1]
      · linarith [hu.2, h_in.1, h_rest_above t' h_rest]
    have h_rest : HasCauchyPVAt γ (t + r) b g s
        (windowPieceSum r p w b rest (t + r)) := IH
      ((List.pairwise_cons.mp h_sorted.pairwise).2).sortedLT (fun _ => hr_nonneg) (t + r)
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
integral of `g (γ t) * deriv γ t` converges on each crossing window (disjoint interiors,
lying in `[a, b]` — they may touch each other, or touch `a` or `b`), the truncations are
integrable on `[a, b]`, and the curve keeps a
positive distance from `s` off the windows, then the principal value at `s` exists on
`[a, b]`. The per-window limits are hypotheses, so both the simple-pole and higher-order
per-window theorems discharge them. -/
theorem cauchyPVExistsAt_of_perWindow_tendsto_of_interiorDisjoint {γ : ℝ → ℂ} {s : ℂ} {g : ℂ → ℂ}
    {a b r : ℝ} (hab : a ≤ b) (crossings : Finset ℝ)
    (hr_nonneg : crossings.Nonempty → 0 ≤ r)
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
  refine CauchyPVExistsAt.intro (hasCauchyPVAt_along_sorted
    (p := fun l u => ∫ t in l..u, g (γ t) * deriv γ t)
    (w := fun t => if h : t ∈ crossings then (h_win t h).choose else 0)
    (fun l u hA hlu hu h_far' => hasCauchyPVAt_plain_piece hab hm_pos h_int_tr hA hlu hu h_far')
    (crossings.sort (· ≤ ·)) (Finset.sortedLT_sort crossings)
    (fun h => hr_nonneg (Finset.nonempty_iff_ne_empty.mpr fun he => h (by simp [he])))
    a le_rfl hab
    (fun t ht => h_lo t ((Finset.mem_sort _).mp ht))
    (fun t ht => h_hi t ((Finset.mem_sort _).mp ht))
    (fun t ht t' ht' hne => h_pair t ((Finset.mem_sort _).mp ht)
      t' ((Finset.mem_sort _).mp ht') hne)
    (fun t ht => ?_)
    (fun u hu h_avoid => hm u hu fun t ht => h_avoid t ((Finset.mem_sort _).mpr ht)))
  have h_mem := (Finset.mem_sort (α := ℝ) (· ≤ ·)).mp ht
  refine hasCauchyPVAt_iff.mpr ⟨eventually_intervalIntegrable_truncated_window hab
    (h_lo t h_mem) (h_hi t h_mem) (hr_nonneg ⟨t, h_mem⟩) h_int_tr, ?_⟩
  rw [dif_pos h_mem]
  exact (h_win t h_mem).choose_spec

-- The two helpers below keep `hF : F.card = k` as an explicit hypothesis even though it is
-- derivable from `hc` and `hFdef`: it is not merely a side condition but an *argument* appearing
-- in their conclusions, since `Finset.orderEmbOfFin` and `Finset.intervalGapsWithin` both take the
-- cardinality proof explicitly. `windowPieceSum_boundary` below, whose conclusion mentions neither
-- `F` nor `hF`, takes none of them and derives everything internally.
/-- The window map `t ↦ (t - r, t + r)` into the lexicographic plane, as an order embedding:
`Prod.Lex` compares first coordinates first and `t ↦ t - r` is strictly monotone. -/
private def windowLexEmb (r : ℝ) : ℝ ↪o (ℝ ×ₗ ℝ) :=
  OrderEmbedding.ofStrictMono (fun t => toLex (t - r, t + r))
    fun _ _ h => Prod.Lex.left _ _ (by simpa using h)

/-- The two edges of window `i`, read off the order embedding of the pair set.

Sorting commutes with the strictly monotone window map — that is Mathlib's
`StrictMonoOn.map_finsetSort` — so the `i`-th sorted pair is the `i`-th sorted crossing
shifted by `±r`. -/
private theorem orderEmbOfFin_window_fst_snd {crossings : Finset ℝ} {r : ℝ} {k : ℕ}
    (hc : crossings.card = k) {F : Finset (ℝ × ℝ)}
    (hFdef : F = crossings.image fun t : ℝ => (t - r, t + r)) (hF : F.card = k) (i : Fin k) :
    ((Finset.orderEmbOfFin (α := ℝ ×ₗ ℝ) F hF) i).1 = crossings.orderEmbOfFin hc i - r
      ∧ ((Finset.orderEmbOfFin (α := ℝ ×ₗ ℝ) F hF) i).2 = crossings.orderEmbOfFin hc i + r := by
  have hFmap : crossings.map (windowLexEmb r).toEmbedding = F := by
    rw [hFdef, Finset.map_eq_image]; rfl
  have hmap : (crossings.sort (· ≤ ·)).map (windowLexEmb r).toEmbedding
      = Finset.sort (α := ℝ ×ₗ ℝ) F := by
    rw [← hFmap]
    exact ((windowLexEmb r).strictMono.strictMonoOn _).map_finsetSort
  have key : Finset.orderEmbOfFin (α := ℝ ×ₗ ℝ) F hF i
      = windowLexEmb r (crossings.orderEmbOfFin hc i) := by
    simp [Finset.orderEmbOfFin_apply, ← hmap]
  exact ⟨congrArg Prod.fst key, congrArg Prod.snd key⟩

/-- **The piece/window sum is Mathlib's interval-gap sum.** Along the suffix of the sorted
crossings from index `j`, the aggregated value splits into the gap pieces from `j` onwards and the
window values of that suffix. The `j = 0` case identifies `windowPieceSum` with
`Finset.intervalGapsWithin`. -/
private theorem windowPieceSum_eq_sum_intervalGapsWithin_add_sum {p : ℝ → ℝ → ℂ} {w : ℝ → ℂ}
    {a b r : ℝ} {k : ℕ} {crossings : Finset ℝ} (hc : crossings.card = k)
    {F : Finset (ℝ × ℝ)} (hFdef : F = crossings.image fun t : ℝ => (t - r, t + r))
    (hF : F.card = k) :
    ∀ j : ℕ, j ≤ k →
      windowPieceSum r p w b ((crossings.sort (· ≤ ·)).drop j)
          (F.intervalGapsWithin hF a b j).1
        = (∑ i ∈ Finset.Ico j (k + 1),
            p (F.intervalGapsWithin hF a b i).1 (F.intervalGapsWithin hF a b i).2)
          + (((crossings.sort (· ≤ ·)).drop j).map w).sum := by
  -- the induction runs on the fuel `k - j`, an implementation detail of the recursion rather
  -- than part of the statement, so it is introduced here instead of being exposed above
  suffices h : ∀ n j : ℕ, k - j = n → j ≤ k →
      windowPieceSum r p w b ((crossings.sort (· ≤ ·)).drop j)
          (F.intervalGapsWithin hF a b j).1
        = (∑ i ∈ Finset.Ico j (k + 1),
            p (F.intervalGapsWithin hF a b i).1 (F.intervalGapsWithin hF a b i).2)
          + (((crossings.sort (· ≤ ·)).drop j).map w).sum from
    fun j hj => h (k - j) j rfl hj
  intro n
  induction n with
  | zero =>
    intro j hn hj
    have hjk : j = k := le_antisymm hj (Nat.le_of_sub_eq_zero hn)
    subst hjk
    rw [List.drop_of_length_le (by simp [Finset.length_sort, hc]),
      Nat.Ico_succ_singleton, Finset.sum_singleton]
    simp [windowPieceSum, Finset.intervalGapsWithin_last_snd F hF a b]
  | succ n ih =>
    intro j hn hj
    have hjk : j < k := by omega
    have hlen : j < (crossings.sort (· ≤ ·)).length := by
      rw [Finset.length_sort, hc]; exact hjk
    obtain ⟨hfst, hsnd⟩ := orderEmbOfFin_window_fst_snd hc hFdef hF ⟨j, hjk⟩
    have hgj : (F.intervalGapsWithin hF a b j).2
        = (crossings.sort (· ≤ ·))[j]'hlen - r := by
      rw [Finset.intervalGapsWithin_snd_of_lt F hF a b j hjk, hfst,
        Finset.orderEmbOfFin_apply]
      rfl
    have hgj1 : (F.intervalGapsWithin hF a b (j + 1)).1
        = (crossings.sort (· ≤ ·))[j]'hlen + r := by
      have h := Finset.intervalGapsWithin_succ_fst_of_lt F hF a b j hjk
      rw [hsnd, Finset.orderEmbOfFin_apply] at h
      simpa using h
    rw [List.drop_eq_getElem_cons hlen, windowPieceSum,
      Finset.sum_eq_sum_Ico_succ_bot (Nat.lt_succ_of_le hj), hgj, ← hgj1,
      (Nat.cast_add_one (R := Fin (k + 1)) j).symm,
      ih (j + 1) (by omega) (by omega)]
    simp only [List.map_cons, List.sum_cons]
    ring

/-- **The window aggregation telescopes to the endpoint difference.** Reading the pieces as the
gaps of the window finset `F = {(t - r, t + r) : t ∈ crossings}` inside `[a, b]`, this is exactly
`Finset.sum_intervalGapsWithin_add_sum_eq_sub` for `g = Φ ∘ γ`. -/
private theorem windowPieceSum_boundary {γ : ℝ → ℂ} {Φ : ℂ → ℂ} {a b r : ℝ}
    {crossings : Finset ℝ} :
    windowPieceSum r (fun l u => Φ (γ u) - Φ (γ l))
        (fun t => Φ (γ (t + r)) - Φ (γ (t - r))) b (crossings.sort (· ≤ ·)) a
      = Φ (γ b) - Φ (γ a) := by
  set k := crossings.card with hc
  set F := crossings.image fun t : ℝ => (t - r, t + r) with hFdef
  have hF : F.card = k := Finset.card_image_of_injective _ fun x y hxy => by
    have : x - r = y - r := congrArg Prod.fst hxy
    linarith
  have hbridge := windowPieceSum_eq_sum_intervalGapsWithin_add_sum
    (p := fun l u => Φ (γ u) - Φ (γ l))
    (w := fun t => Φ (γ (t + r)) - Φ (γ (t - r))) (b := b) (a := a) hc.symm hFdef hF 0
    (Nat.zero_le k)
  rw [List.drop_zero, Nat.cast_zero, Finset.intervalGapsWithin_zero_fst] at hbridge
  rw [hbridge]
  have hsort : ∀ f : ℝ → ℂ,
      ((crossings.sort (· ≤ ·)).map f).sum = ∑ t ∈ crossings, f t := fun f => by
    rw [Finset.sum_eq_multiset_sum, ← Finset.sort_eq crossings (· ≤ ·), Multiset.map_coe,
      Multiset.sum_coe]
  have hw : (((crossings.sort (· ≤ ·)).map fun t => Φ (γ (t + r)) - Φ (γ (t - r))).sum)
      = ∑ z ∈ F, ((Φ ∘ γ) z.2 - (Φ ∘ γ) z.1) := by
    rw [hsort, hFdef, Finset.sum_image (by
      intro x _ y _ hxy
      have hx : x - r = y - r := congrArg Prod.fst hxy
      linarith)]
    rfl
  rw [hw, ← Finset.range_eq_Ico]
  simpa using Finset.sum_intervalGapsWithin_add_sum_eq_sub F hF (a := a) (b := b) (Φ ∘ γ)

/-- **Telescoping per-window aggregation**: when the plain integrand has a curve-antiderivative
`Φ` on pole-free pieces and each window limit is the boundary difference of `Φ ∘ γ`, the
principal value on `[a, b]` is `Φ (γ b) - Φ (γ a)` — in particular zero around a closed curve.
The higher-order per-window limits have exactly this boundary-difference shape. -/
theorem hasCauchyPVAt_of_perWindow_boundary_tendsto_of_interiorDisjoint {γ : ℝ → ℂ} {s : ℂ}
    {g : ℂ → ℂ}
    {Φ : ℂ → ℂ} {a b r : ℝ} (hab : a ≤ b) (crossings : Finset ℝ)
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
  have h := hasCauchyPVAt_along_sorted
    (p := fun l u => Φ (γ u) - Φ (γ l))
    (w := fun t => Φ (γ (t + r)) - Φ (γ (t - r)))
    (fun l u hA hlu hu h_far' => by
      have h_ne : ∀ t ∈ Icc l u, γ t ≠ s := fun t ht h_eq => by
        have h_bd := h_far' t ht
        rw [h_eq, sub_self, norm_zero] at h_bd
        linarith
      have h0 := hasCauchyPVAt_plain_piece hab hm_pos h_int_tr hA hlu hu h_far'
      rwa [h_plain_eq l u hA hlu hu h_ne] at h0)
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
  rwa [windowPieceSum_boundary] at h

/-- **Compatibility form of `cauchyPVExistsAt_of_perWindow_tendsto_of_interiorDisjoint`** with
windows strictly separated from each other and starting strictly after `a`; the right edges may
equal `b`, since `h_hi` is `t + r ≤ b`. Prefer the general form, which additionally admits windows
that touch each other or start at `a`. -/
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
    CauchyPVExistsAt γ a b g s :=
  cauchyPVExistsAt_of_perWindow_tendsto_of_interiorDisjoint hab crossings (fun _ => hr_pos.le)
    (fun t ht => (h_lo t ht).le) h_hi (fun t ht t' ht' hne => (h_pair t ht t' ht' hne).le)
    h_int_tr h_win h_far

/-- **Compatibility form of `hasCauchyPVAt_of_perWindow_boundary_tendsto_of_interiorDisjoint`**
with windows strictly separated from each other and starting strictly after `a`; the right edges
may equal `b`. Prefer the general form. -/
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
    HasCauchyPVAt γ a b g s (Φ (γ b) - Φ (γ a)) :=
  hasCauchyPVAt_of_perWindow_boundary_tendsto_of_interiorDisjoint hab crossings
    (fun _ => hr_pos.le) (fun t ht => (h_lo t ht).le) h_hi
    (fun t ht t' ht' hne => (h_pair t ht t' ht' hne).le) h_int_tr h_plain_eq h_win h_far


end TauCeti.Contour

end
