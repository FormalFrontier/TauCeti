/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Probability.Exchangeability.PathSpace.InvariantTail
public import Mathlib.MeasureTheory.MeasurableSpace.NCard

/-!
# The path tail is strictly smaller than the exchangeable sigma-algebra

For paths in a nontrivial space with measurable singletons, this file proves the strict
comparison

`pathTail alpha < exchangeableSigma alpha`.

The witness is the event that a path differs from a fixed value at finitely many, evenly many
coordinates.  Every time permutation preserves the cardinality of that finite deviation set, so
the event is exchangeable.  It is not a tail event: changing coordinate zero alone changes the
parity without changing any coordinate from time one onward.

This completes the strict comparison between the path tail and exchangeable sigma-algebras in
Layer 2 of the exchangeability roadmap.  Together with `invariants_shift_lt_pathTail`, it gives
the strict chain

`invariants (shift alpha) < pathTail alpha < exchangeableSigma alpha`

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

/-- The event that a path differs from `a` at an even finite number of coordinates.

The target of `Set.encard` is used rather than `Set.ncard`, because `encard` distinguishes
infinite deviation sets from the empty deviation set. -/
private def evenFiniteDeviation (a : α) : Set (ℕ → α) :=
  {x | Set.encard {n | x n ≠ a} ∈ Set.range fun k : ℕ => ((2 * k : ℕ) : ℕ∞)}

omit [MeasurableSpace α] in
/-- The finite-even-deviation event has its advertised membership characterization. -/
private theorem mem_evenFiniteDeviation {a : α} {x : ℕ → α} :
    x ∈ evenFiniteDeviation a ↔
      ∃ k : ℕ, Set.encard {n | x n ≠ a} = ((2 * k : ℕ) : ℕ∞) := by
  simp only [evenFiniteDeviation, Set.mem_ofPred_eq, Set.mem_range]
  constructor <;> rintro ⟨k, hk⟩
  · exact ⟨k, hk.symm⟩
  · exact ⟨k, hk.symm⟩

/-- The deviation set is a measurable function of the path. -/
private theorem measurable_deviation [MeasurableSingletonClass α] (a : α) :
    Measurable fun x : ℕ → α => {n | x n ≠ a} := by
  rw [measurable_set_iff]
  intro n
  have hn : Measurable (fun x : ℕ → α => x n) := measurable_pi_apply n
  exact (hn.eq_const a).not

/-- The finite-even-deviation event is ambient-measurable. -/
private theorem measurableSet_evenFiniteDeviation [MeasurableSingletonClass α] (a : α) :
    MeasurableSet (evenFiniteDeviation a) := by
  exact (measurable_encard.comp (measurable_deviation a)) MeasurableSet.of_discrete

omit [MeasurableSpace α] in
/-- Reindexing a path by a permutation preserves the cardinality of its deviation set. -/
private theorem encard_deviation_permReindex (a : α) (π : Equiv.Perm ℕ) (x : ℕ → α) :
    Set.encard {n | permReindex π x n ≠ a} = Set.encard {n | x n ≠ a} := by
  have hset : {n | permReindex π x n ≠ a} = π ⁻¹' {n | x n ≠ a} := by
    ext n
    simp
  rw [hset, Set.encard_preimage_of_bijective π.bijective]

omit [MeasurableSpace α] in
/-- Every time permutation fixes the finite-even-deviation event. -/
private theorem preimage_permReindex_evenFiniteDeviation (a : α) (π : Equiv.Perm ℕ) :
    permReindex (α := α) π ⁻¹' evenFiniteDeviation a = evenFiniteDeviation a := by
  ext x
  simp only [Set.mem_preimage, mem_evenFiniteDeviation]
  rw [encard_deviation_permReindex]

/-- The finite-even-deviation event belongs to the exchangeable sigma-algebra. -/
private theorem measurableSet_exchangeableSigma_evenFiniteDeviation
    [MeasurableSingletonClass α] (a : α) :
    MeasurableSet[exchangeableSigma α] (evenFiniteDeviation a) :=
  measurableSet_exchangeableSigma_of_forall_permReindex
    (measurableSet_evenFiniteDeviation a) fun π _ =>
      preimage_permReindex_evenFiniteDeviation a π

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
/-- The constant path belongs to the finite-even-deviation event. -/
private theorem const_mem_evenFiniteDeviation (a : α) :
    (fun _ : ℕ => a) ∈ evenFiniteDeviation a := by
  rw [mem_evenFiniteDeviation]
  refine ⟨0, ?_⟩
  simp

omit [MeasurableSpace α] in
/-- Changing only coordinate zero to a different value leaves the finite-even-deviation event. -/
private theorem update_zero_notMem_evenFiniteDeviation {a b : α} (hab : b ≠ a) :
    Function.update (fun _ : ℕ => a) 0 b ∉ evenFiniteDeviation a := by
  rw [mem_evenFiniteDeviation]
  simp only [not_exists]
  intro k
  have hsupport : {n | Function.update (fun _ : ℕ => a) 0 b n ≠ a} = {0} := by
    ext n
    by_cases hn : n = 0
    · subst n
      simp [hab]
    · simpa [Function.update_of_ne hn] using hn
  rw [hsupport, Set.encard_singleton]
  norm_cast
  omega

/-- The finite-even-deviation event is not measurable for the path tail sigma-algebra. -/
private theorem not_measurableSet_pathTail_evenFiniteDeviation [MeasurableSingletonClass α]
    {a b : α} (hab : b ≠ a) :
    ¬ MeasurableSet[pathTail α] (evenFiniteDeviation a) := by
  intro hs
  have hs_future :
      MeasurableSet[tailFamily (fun k (z : ℕ → α) => z k) 1] (evenFiniteDeviation a) :=
    pathTail_le_tailFamily (α := α) 1 _ hs
  have hmem := mem_iff_of_measurableSet_tailFamily_coord hs_future
    (x := fun _ : ℕ => a) (y := Function.update (fun _ : ℕ => a) 0 b) (r := 1)
    (fun n hn => by simp [Function.update_of_ne (by omega : n ≠ 0)])
  exact update_zero_notMem_evenFiniteDeviation hab (hmem.mp (const_mem_evenFiniteDeviation a))

/-! ## Strictness -/

/-- **The path tail sigma-algebra is a proper sub-sigma-algebra of the exchangeable
sigma-algebra.**  This holds for every nontrivial state space with measurable singletons.

The reverse inclusion fails because the exchangeable event that a path has finite even deviation
from a fixed value is sensitive to changing one coordinate, whereas every tail event is
insensitive to every finite prefix. -/
theorem pathTail_lt_exchangeableSigma [MeasurableSingletonClass α] [Nontrivial α] :
    pathTail α < exchangeableSigma α := by
  refine lt_of_le_not_ge pathTail_le_exchangeableSigma ?_
  intro hle
  obtain ⟨a, b, hab⟩ := exists_pair_ne α
  exact not_measurableSet_pathTail_evenFiniteDeviation (a := a) (b := b) hab.symm
    (hle _ (measurableSet_exchangeableSigma_evenFiniteDeviation a))

end Probability

end TauCeti
