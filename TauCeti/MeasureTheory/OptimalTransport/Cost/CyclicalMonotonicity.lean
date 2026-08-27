/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Cost.Basic

/-!
# Cyclical monotonicity for transport costs

This file defines finite `c`-cyclical monotonicity for an extended-nonnegative transport cost.
The definition is purely cost-theoretic: it does not require a measure, topology, or duality
theory. A certified plan is almost-everywhere concentrated on a cyclically monotone set, and
that set can be taken measurable as soon as the cost and both potentials are measurable; the
converse and statements about topological support require additional hypotheses.

This is Layer 2, item 7 of the optimal-transport roadmap.
-/

public section

noncomputable section

open Set

open scoped ENNReal

namespace TauCeti

universe u v

variable {X : Type u} {Y : Type v} {c : X × Y → ℝ≥0∞}

/-- A set of pairs is `c`-*cyclically monotone* when no finite family of its points can be
improved by permuting the targets: for every finite family `(x i, y i)` in the set and every
permutation `σ`, the diagonal total cost `∑ i, c (x i, y i)` is at most the rearranged total
cost `∑ i, c (x i, y (σ i))`.

This is Villani's finite-family form of the condition. A certified plan is almost-everywhere
concentrated on a `c`-cyclically monotone set — measurably so when the cost and both potentials
are measurable; the converse and any statement about topological support need additional
hypotheses. Infinite costs allow forbidden rearrangements. -/
def IsCyclicallyMonotone (c : X × Y → ℝ≥0∞) (S : Set (X × Y)) : Prop :=
  ∀ (n : ℕ) (x : Fin n → X) (y : Fin n → Y), (∀ i, (x i, y i) ∈ S) →
    ∀ σ : Equiv.Perm (Fin n), ∑ i, c (x i, y i) ≤ ∑ i, c (x i, y (σ i))

/-- The defining finite-family inequality for `c`-cyclical monotonicity. -/
theorem isCyclicallyMonotone_iff {S : Set (X × Y)} :
    IsCyclicallyMonotone c S ↔
      ∀ (n : ℕ) (x : Fin n → X) (y : Fin n → Y), (∀ i, (x i, y i) ∈ S) →
        ∀ σ : Equiv.Perm (Fin n), ∑ i, c (x i, y i) ≤ ∑ i, c (x i, y (σ i)) :=
  Iff.rfl

namespace IsCyclicallyMonotone

/-- Apply cyclical monotonicity to a finite family and a permutation. -/
theorem sum_le {S : Set (X × Y)} (h : IsCyclicallyMonotone c S) (n : ℕ) (x : Fin n → X)
    (y : Fin n → Y) (hmem : ∀ i, (x i, y i) ∈ S) (σ : Equiv.Perm (Fin n)) :
    ∑ i, c (x i, y i) ≤ ∑ i, c (x i, y (σ i)) :=
  isCyclicallyMonotone_iff.1 h n x y hmem σ

/-- Cyclical monotonicity passes to subsets. -/
theorem mono {S S' : Set (X × Y)} (h : IsCyclicallyMonotone c S') (hSS' : S ⊆ S') :
    IsCyclicallyMonotone c S :=
  isCyclicallyMonotone_iff.2 fun n x y hmem σ ↦
    h.sum_le n x y (fun i ↦ hSS' (hmem i)) σ

/-- **The two-point form of cyclical monotonicity.** Swapping the targets of two points of a
`c`-cyclically monotone set does not lower the total cost. -/
theorem add_le_add_swap {S : Set (X × Y)} (h : IsCyclicallyMonotone c S)
    {x₁ x₂ : X} {y₁ y₂ : Y} (h₁ : (x₁, y₁) ∈ S) (h₂ : (x₂, y₂) ∈ S) :
    c (x₁, y₁) + c (x₂, y₂) ≤ c (x₁, y₂) + c (x₂, y₁) := by
  have hmem : ∀ i, (![x₁, x₂] i, ![y₁, y₂] i) ∈ S := by
    intro i
    fin_cases i
    · simpa using h₁
    · simpa using h₂
  have := h.sum_le 2 ![x₁, x₂] ![y₁, y₂] hmem (Equiv.swap 0 1)
  simpa [Fin.sum_univ_two, Equiv.swap_apply_left, Equiv.swap_apply_right] using this

end IsCyclicallyMonotone

/-- The empty set is cyclically monotone for every cost. -/
@[simp]
theorem isCyclicallyMonotone_empty (c : X × Y → ℝ≥0∞) :
    IsCyclicallyMonotone c (∅ : Set (X × Y)) :=
  isCyclicallyMonotone_iff.2 fun n x y hmem σ ↦ by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · exact absurd (hmem ⟨0, hn⟩) (Set.notMem_empty _)

end TauCeti
