/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Exchangeability.PathSpace.Invariant.Tail
import Mathlib.MeasureTheory.MeasurableSpace.NCard

/-!
# The path tail is strictly smaller than the exchangeable sigma-algebra

For paths whose state-space σ-algebra is nontrivial, this file proves the strict comparison

`pathTail alpha < exchangeableSigma alpha`.

The witness is the event that a path visits a fixed measurable set at finitely many, evenly many
coordinates.  Every time permutation preserves the cardinality of that finite visit set, so the
event is exchangeable.  It is not a tail event: changing coordinate zero alone changes the parity
without changing any coordinate from time one onward.

This completes the strict comparison between the path tail and exchangeable sigma-algebras in
Layer 2 of the exchangeability roadmap.  Together with `invariants_shift_lt_pathTail`, it gives
the strict chain

`invariants (shift Bool) < pathTail Bool < exchangeableSigma Bool`

under the hypotheses of the two results.

## Main result

* `pathTail_lt_exchangeableSigma` -- the path tail is a proper sub-sigma-algebra of the
  exchangeable sigma-algebra.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {α : Type*} [MeasurableSpace α]

/-! ## An exchangeable parity event -/

/-- The event that a path visits `s` at an even finite number of coordinates.

The target of `Set.encard` is used rather than `Set.ncard`, because `encard` distinguishes
infinite visit sets from the empty visit set. -/
private def evenFiniteVisits (s : Set α) : Set (ℕ → α) :=
  {x | Set.encard {n | x n ∈ s} ∈ Set.range fun k : ℕ => ((2 * k : ℕ) : ℕ∞)}

omit [MeasurableSpace α] in
/-- The finite-even-visit event has its advertised membership characterization. -/
private theorem mem_evenFiniteVisits {s : Set α} {x : ℕ → α} :
    x ∈ evenFiniteVisits s ↔
      ∃ k : ℕ, Set.encard {n | x n ∈ s} = ((2 * k : ℕ) : ℕ∞) := by
  simp only [evenFiniteVisits, Set.mem_ofPred_eq, Set.mem_range]
  constructor <;> rintro ⟨k, hk⟩
  · exact ⟨k, hk.symm⟩
  · exact ⟨k, hk.symm⟩

/-- The visit set is a measurable function of the path. -/
private theorem measurable_visits {s : Set α} (hs : MeasurableSet s) :
    Measurable fun x : ℕ → α => {n | x n ∈ s} := by
  rw [measurable_set_iff]
  intro n
  exact hs.mem.comp (measurable_pi_apply n)

/-- The finite-even-visit event is ambient-measurable. -/
private theorem measurableSet_evenFiniteVisits {s : Set α} (hs : MeasurableSet s) :
    MeasurableSet (evenFiniteVisits s) := by
  exact (measurable_encard.comp (measurable_visits hs)) MeasurableSet.of_discrete

omit [MeasurableSpace α] in
/-- Reindexing a path by a permutation preserves the cardinality of its visit set. -/
private theorem encard_visits_permReindex (s : Set α) (π : Equiv.Perm ℕ) (x : ℕ → α) :
    Set.encard {n | permReindex π x n ∈ s} = Set.encard {n | x n ∈ s} := by
  have hset : {n | permReindex π x n ∈ s} = π ⁻¹' {n | x n ∈ s} := by
    ext n
    simp
  rw [hset, Set.encard_preimage_of_bijective π.bijective]

omit [MeasurableSpace α] in
/-- Every time permutation fixes the finite-even-visit event. -/
private theorem preimage_permReindex_evenFiniteVisits (s : Set α) (π : Equiv.Perm ℕ) :
    permReindex (α := α) π ⁻¹' evenFiniteVisits s = evenFiniteVisits s := by
  ext x
  simp only [Set.mem_preimage, mem_evenFiniteVisits]
  rw [encard_visits_permReindex]

/-- The finite-even-visit event belongs to the exchangeable sigma-algebra. -/
private theorem measurableSet_exchangeableSigma_evenFiniteVisits {s : Set α}
    (hs : MeasurableSet s) :
    MeasurableSet[exchangeableSigma α] (evenFiniteVisits s) :=
  measurableSet_exchangeableSigma_of_forall_permReindex
    (measurableSet_evenFiniteVisits hs) fun π _ => preimage_permReindex_evenFiniteVisits s π

/-! ## The parity event is not a tail event -/

/-- A set in the future sigma-algebra from time `r` onward cannot distinguish two paths which
agree from time `r` onward. -/
private theorem mem_iff_of_measurableSet_tailFamily_coord {s : Set (ℕ → α)} {x y : ℕ → α}
    {r : ℕ} (hs : MeasurableSet[tailFamily (fun k (z : ℕ → α) => z k) r] s)
    (hxy : ∀ n, r ≤ n → x n = y n) :
    x ∈ s ↔ y ∈ s := by
  rw [tailFamily_coord_eq_comap_shift_iterate] at hs
  obtain ⟨t, -, ht⟩ := hs
  have hshift : (shift α)^[r] x = (shift α)^[r] y := by
    funext n
    simp only [shift_iterate_apply]
    exact hxy (n + r) (Nat.le_add_left r n)
  rw [← ht, Set.mem_preimage, Set.mem_preimage, hshift]

omit [MeasurableSpace α] in
/-- The constant path outside `s` belongs to the finite-even-visit event. -/
private theorem const_mem_evenFiniteVisits {s : Set α} {a : α} (ha : a ∉ s) :
    (fun _ : ℕ => a) ∈ evenFiniteVisits s := by
  rw [mem_evenFiniteVisits]
  refine ⟨0, ?_⟩
  simp [ha]

omit [MeasurableSpace α] in
/-- Changing only coordinate zero to a value in `s` leaves the finite-even-visit event. -/
private theorem update_zero_notMem_evenFiniteVisits {s : Set α} {a b : α}
    (ha : a ∉ s) (hb : b ∈ s) :
    Function.update (fun _ : ℕ => a) 0 b ∉ evenFiniteVisits s := by
  rw [mem_evenFiniteVisits]
  simp only [not_exists]
  intro k
  have hsupport : {n | Function.update (fun _ : ℕ => a) 0 b n ∈ s} = {0} := by
    ext n
    by_cases hn : n = 0
    · subst n
      simp [hb]
    · simp [ha, hn]
  rw [hsupport, Set.encard_singleton]
  norm_cast
  omega

/-- The finite-even-visit event is not measurable for the path tail sigma-algebra. -/
private theorem not_measurableSet_pathTail_evenFiniteVisits {s : Set α} {a b : α}
    (ha : a ∉ s) (hb : b ∈ s) :
    ¬ MeasurableSet[pathTail α] (evenFiniteVisits s) := by
  intro hs
  have hs_future :
      MeasurableSet[tailFamily (fun k (z : ℕ → α) => z k) 1] (evenFiniteVisits s) :=
    pathTail_le_tailFamily (α := α) 1 _ hs
  have hmem := mem_iff_of_measurableSet_tailFamily_coord hs_future
    (x := fun _ : ℕ => a) (y := Function.update (fun _ : ℕ => a) 0 b) (r := 1)
    (fun n hn => by simp [Function.update_of_ne (by omega : n ≠ 0)])
  exact update_zero_notMem_evenFiniteVisits ha hb (hmem.mp (const_mem_evenFiniteVisits ha))

/-! ## Strictness -/

/-- **The path tail sigma-algebra is a proper sub-sigma-algebra of the exchangeable
sigma-algebra.**  This holds whenever the state-space σ-algebra is nontrivial.

The reverse inclusion fails because the exchangeable event that a path visits a proper measurable
set at finitely many, evenly many coordinates is sensitive to changing one coordinate, whereas
every tail event is insensitive to every finite prefix. -/
theorem pathTail_lt_exchangeableSigma
    (hα : ⊥ < (inferInstance : MeasurableSpace α)) :
    pathTail α < exchangeableSigma α := by
  refine lt_of_le_not_ge pathTail_le_exchangeableSigma ?_
  intro hle
  have hnot : ¬ (∀ s, MeasurableSet s → MeasurableSet[⊥] s) :=
    fun h ↦ (not_le_of_gt hα) (MeasurableSpace.le_def.mpr h)
  push Not at hnot
  obtain ⟨s, hs, hs_not_bot⟩ := hnot
  rw [MeasurableSpace.measurableSet_bot_iff] at hs_not_bot
  push Not at hs_not_bot
  obtain ⟨b, hb⟩ := hs_not_bot.1
  obtain ⟨a, ha⟩ := Set.nonempty_compl.mpr hs_not_bot.2
  simp only [Set.mem_compl_iff] at ha
  exact not_measurableSet_pathTail_evenFiniteVisits ha hb
    (hle _ (measurableSet_exchangeableSigma_evenFiniteVisits hs))

end Probability

end TauCeti
