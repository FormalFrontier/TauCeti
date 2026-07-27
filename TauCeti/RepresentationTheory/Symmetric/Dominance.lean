module

public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Data.List.Lex
import Mathlib.Tactic.Order

/-!
# Dominance order on partitions

This file defines dominance of partitions of a fixed natural number by comparing all partial
sums of their decreasingly sorted parts. It proves that dominance is a partial order and that
strict dominance implies the corresponding strict lexicographic comparison.

The dominance order is the triangular order governing Kostka numbers and the occurrence of
Specht modules in permutation modules. It is the “Orders on partitions” target in Layer 0 of
the symmetric-group and Schur–Weyl roadmap.
-/

public section

namespace TauCeti

private abbrev sortedParts {n : ℕ} (μ : n.Partition) : List ℕ :=
  μ.parts.sort (· ≥ ·)

private theorem sortedParts_sum {n : ℕ} (μ : n.Partition) :
    (sortedParts μ).sum = n := by
  calc
    (sortedParts μ).sum = (↑(sortedParts μ) : Multiset ℕ).sum :=
      (Multiset.sum_coe _).symm
    _ = μ.parts.sum := congrArg Multiset.sum (Multiset.sort_eq μ.parts (· ≥ ·))
    _ = n := μ.parts_sum

private theorem sortedParts_length_le {n : ℕ} (μ : n.Partition) :
    (sortedParts μ).length ≤ n := by
  calc
    (sortedParts μ).length ≤ (sortedParts μ).sum :=
      List.length_le_sum_of_one_le _ fun i hi =>
        μ.parts_pos ((Multiset.mem_sort (· ≥ ·)).mp hi)
    _ = n := sortedParts_sum μ

/-- A partition `μ` dominates a partition `ν` when every partial sum of the decreasingly
sorted parts of `μ` is at least the corresponding partial sum of `ν`. -/
def Dominates {n : ℕ} (μ ν : n.Partition) : Prop :=
  ∀ k : Fin (n + 1),
    ((sortedParts ν).take k).sum ≤ ((sortedParts μ).take k).sum

/-- Dominance can be checked on the first `n + 1` partial sums. -/
theorem dominates_fin_iff {n : ℕ} {μ ν : n.Partition} :
    Dominates μ ν ↔
      ∀ k : Fin (n + 1),
        ((ν.parts.sort (· ≥ ·)).take k).sum ≤
          ((μ.parts.sort (· ≥ ·)).take k).sum :=
  (Iff.rfl)

/-- The defining partial-sum characterization of dominance. -/
theorem dominates_iff {n : ℕ} {μ ν : n.Partition} :
    Dominates μ ν ↔
      ∀ k : ℕ,
        ((ν.parts.sort (· ≥ ·)).take k).sum ≤
          ((μ.parts.sort (· ≥ ·)).take k).sum := by
  constructor
  · intro h k
    by_cases hk : k ≤ n
    · exact h ⟨k, Nat.lt_succ_iff.mpr hk⟩
    · have hn_lt_k : n < k := Nat.lt_of_not_ge hk
      rw [List.take_of_length_le ((sortedParts_length_le ν).trans hn_lt_k.le),
        List.take_of_length_le ((sortedParts_length_le μ).trans hn_lt_k.le),
        sortedParts_sum, sortedParts_sum]
  · intro h k
    exact h k

instance {n : ℕ} (μ ν : n.Partition) : Decidable (Dominates μ ν) := by
  exact decidable_of_iff
    (∀ k : Fin (n + 1),
      ((ν.parts.sort (· ≥ ·)).take k).sum ≤
        ((μ.parts.sort (· ≥ ·)).take k).sum) dominates_fin_iff.symm

/-- Every partition dominates itself. -/
@[refl]
theorem dominates_refl {n : ℕ} (μ : n.Partition) : Dominates μ μ :=
  (dominates_iff.mpr fun _ => le_rfl)

/-- Dominance is transitive. -/
@[trans]
theorem Dominates.trans {n : ℕ} {μ ν ξ : n.Partition}
    (hμν : Dominates μ ν) (hνξ : Dominates ν ξ) : Dominates μ ξ :=
  dominates_iff.mpr fun k => (dominates_iff.mp hνξ k).trans (dominates_iff.mp hμν k)

/-- Strict dominance is dominance between unequal partitions. -/
def StrictlyDominates {n : ℕ} (μ ν : n.Partition) : Prop :=
  Dominates μ ν ∧ μ ≠ ν

/-- The defining characterization of strict dominance. -/
theorem strictlyDominates_iff {n : ℕ} {μ ν : n.Partition} :
    StrictlyDominates μ ν ↔ Dominates μ ν ∧ μ ≠ ν :=
  Iff.rfl

instance {n : ℕ} (μ ν : n.Partition) : Decidable (StrictlyDominates μ ν) := by
  exact decidable_of_iff (Dominates μ ν ∧ μ ≠ ν) strictlyDominates_iff.symm

private theorem lex_lt_of_prefix_sum_le {l₁ l₂ : List ℕ}
    (hsum : l₁.sum = l₂.sum)
    (hpos₁ : ∀ i ∈ l₁, 0 < i) (hpos₂ : ∀ i ∈ l₂, 0 < i)
    (hle : ∀ k : ℕ, (l₂.take k).sum ≤ (l₁.take k).sum)
    (hne : l₁ ≠ l₂) : l₂ < l₁ := by
  induction l₁ generalizing l₂ with
  | nil =>
      cases l₂ with
      | nil => exact (hne rfl).elim
      | cons b l₂ =>
          have hb : 0 < b := hpos₂ b (by simp)
          simp only [List.sum_nil, List.sum_cons] at hsum
          omega
  | cons a l₁ ih =>
      cases l₂ with
      | nil =>
          have ha : 0 < a := hpos₁ a (by simp)
          simp only [List.sum_cons, List.sum_nil] at hsum
          omega
      | cons b l₂ =>
          have hba : b ≤ a := by
            simpa only [List.take_succ_cons, List.take_zero, List.sum_cons, List.sum_nil,
              add_zero] using hle 1
          rcases hba.eq_or_lt with hba | hba
          · subst b
            apply List.Lex.cons
            apply ih
            · simpa only [List.sum_cons, Nat.add_left_cancel_iff] using hsum
            · intro i hi
              exact hpos₁ i (by simp [hi])
            · intro i hi
              exact hpos₂ i (by simp [hi])
            · intro k
              simpa only [List.take_succ_cons, List.sum_cons, Nat.add_le_add_iff_left] using
                hle (k + 1)
            · intro h
              exact hne (congrArg (List.cons a) h)
          · exact List.Lex.rel hba

/-- Strict dominance refines the decreasing lexicographic order on sorted parts. -/
theorem sortedParts_lt_of_strictlyDominates {n : ℕ} {μ ν : n.Partition}
    (h : StrictlyDominates μ ν) :
    ν.parts.sort (· ≥ ·) < μ.parts.sort (· ≥ ·) := by
  apply lex_lt_of_prefix_sum_le (sortedParts_sum μ |>.trans (sortedParts_sum ν).symm)
  · intro i hi
    exact μ.parts_pos ((Multiset.mem_sort (· ≥ ·)).mp hi)
  · intro i hi
    exact ν.parts_pos ((Multiset.mem_sort (· ≥ ·)).mp hi)
  · exact dominates_iff.mp h.1
  · intro hs
    apply h.2
    apply Nat.Partition.ext
    calc
      μ.parts = ↑(μ.parts.sort (· ≥ ·)) :=
        (Multiset.sort_eq μ.parts (· ≥ ·)).symm
      _ = ↑(ν.parts.sort (· ≥ ·)) := congrArg (fun l : List ℕ => (l : Multiset ℕ)) hs
      _ = ν.parts := Multiset.sort_eq ν.parts (· ≥ ·)

/-- Dominance is antisymmetric. -/
theorem Dominates.antisymm {n : ℕ} {μ ν : n.Partition}
    (hμν : Dominates μ ν) (hνμ : Dominates ν μ) : μ = ν := by
  by_contra hne
  have hν_lt_μ := sortedParts_lt_of_strictlyDominates
    (show StrictlyDominates μ ν from ⟨hμν, hne⟩)
  have hμ_lt_ν := sortedParts_lt_of_strictlyDominates
    (show StrictlyDominates ν μ from ⟨hνμ, Ne.symm hne⟩)
  exact hν_lt_μ.asymm hμ_lt_ν

/-- A dominance comparison is either equality or strict dominance. -/
theorem dominates_iff_eq_or_strictlyDominates {n : ℕ} {μ ν : n.Partition} :
    Dominates μ ν ↔ μ = ν ∨ StrictlyDominates μ ν := by
  constructor
  · intro h
    rcases eq_or_ne μ ν with rfl | hne
    · exact Or.inl rfl
    · exact Or.inr ⟨h, hne⟩
  · rintro (rfl | h)
    · exact dominates_refl _
    · exact h.1

/-- Strict dominance is irreflexive. -/
theorem strictlyDominates_irrefl {n : ℕ} (μ : n.Partition) :
    ¬StrictlyDominates μ μ :=
  fun h => h.2 rfl

/-- Strict dominance is transitive. -/
theorem StrictlyDominates.trans {n : ℕ} {μ ν ξ : n.Partition}
    (hμν : StrictlyDominates μ ν) (hνξ : StrictlyDominates ν ξ) :
    StrictlyDominates μ ξ := by
  refine ⟨hμν.1.trans hνξ.1, ?_⟩
  intro hμξ
  apply hμν.2
  exact hμν.1.antisymm (hμξ ▸ hνξ.1)

/-- Strict dominance is asymmetric. -/
theorem StrictlyDominates.asymm {n : ℕ} {μ ν : n.Partition}
    (hμν : StrictlyDominates μ ν) : ¬StrictlyDominates ν μ :=
  fun hνμ => hμν.2 (hμν.1.antisymm hνμ.1)

/-- The one-part partition dominates every partition of the same natural number. -/
theorem indiscrete_dominates {n : ℕ} (μ : n.Partition) :
    Dominates (Nat.Partition.indiscrete n) μ := by
  rw [dominates_iff]
  intro k
  rcases k with _ | k
  · simp
  by_cases hn : n = 0
  · subst n
    simp
  · rw [Nat.Partition.indiscrete_parts hn]
    simp only [Multiset.sort_singleton, List.take_succ_cons, List.sum_cons]
    have hsplit := congrArg List.sum
      (List.take_append_drop (k + 1) (μ.parts.sort (· ≥ ·)))
    rw [List.sum_append, sortedParts_sum] at hsplit
    omega

/-- A partition dominates the one-part partition only when it is that partition. -/
theorem dominates_indiscrete_iff {n : ℕ} {μ : n.Partition} :
    Dominates μ (Nat.Partition.indiscrete n) ↔ μ = Nat.Partition.indiscrete n := by
  constructor
  · intro h
    exact h.antisymm (indiscrete_dominates μ)
  · rintro rfl
    exact dominates_refl _

end TauCeti
