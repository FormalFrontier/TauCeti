module

public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Data.List.Lex

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

namespace PartitionLex

/-- The lexicographic linear order on partitions, obtained from their decreasingly sorted parts.
Activate it with `open scoped TauCeti.PartitionLex`. -/
scoped instance partitionLinearOrder {n : ℕ} : LinearOrder n.Partition :=
  LinearOrder.lift' (fun μ => μ.parts.sort (· ≥ ·)) (by
    intro μ ν h
    apply Nat.Partition.ext
    calc
      μ.parts = ↑(μ.parts.sort (· ≥ ·)) := (Multiset.sort_eq μ.parts (· ≥ ·)).symm
      _ = ↑(ν.parts.sort (· ≥ ·)) := congrArg (fun l : List ℕ => (l : Multiset ℕ)) h
      _ = ν.parts := Multiset.sort_eq ν.parts (· ≥ ·))

/-- Partition comparison in the lexicographic order is comparison of the decreasingly sorted
parts. -/
@[simp]
theorem partition_lt_iff {n : ℕ} {μ ν : n.Partition} :
    @LT.lt n.Partition partitionLinearOrder.toLT μ ν ↔
      μ.parts.sort (· ≥ ·) < ν.parts.sort (· ≥ ·) :=
  Iff.rfl

/-- Partition comparison in the non-strict lexicographic order is comparison of the decreasingly
sorted parts. -/
@[simp]
theorem partition_le_iff {n : ℕ} {μ ν : n.Partition} :
    @LE.le n.Partition partitionLinearOrder.toLE μ ν ↔
      μ.parts.sort (· ≥ ·) ≤ ν.parts.sort (· ≥ ·) :=
  Iff.rfl

end PartitionLex

/-- A partition `μ` dominates a partition `ν` when every partial sum of the decreasingly
sorted parts of `μ` is at least the corresponding partial sum of `ν`. -/
def Dominates {n : ℕ} (μ ν : n.Partition) : Prop :=
  ∀ k : Fin (n + 1),
    ((ν.parts.sort (· ≥ ·)).take k).sum ≤ ((μ.parts.sort (· ≥ ·)).take k).sum

/-- By definition, dominance compares the first `n + 1` partial sums. -/
theorem dominates_def {n : ℕ} {μ ν : n.Partition} :
    Dominates μ ν ↔
      ∀ k : Fin (n + 1),
        ((ν.parts.sort (· ≥ ·)).take k).sum ≤
          ((μ.parts.sort (· ≥ ·)).take k).sum :=
  Iff.rfl

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
        ((μ.parts.sort (· ≥ ·)).take k).sum) dominates_def.symm

/-- Every partition dominates itself. -/
@[simp, refl]
theorem dominates_refl {n : ℕ} (μ : n.Partition) : Dominates μ μ :=
  (dominates_iff.mpr fun _ => le_rfl)

/-- Dominance is transitive. -/
@[trans]
theorem Dominates.trans {n : ℕ} {μ ν ξ : n.Partition}
    (hμν : Dominates μ ν) (hνξ : Dominates ν ξ) : Dominates μ ξ :=
  dominates_iff.mpr fun k => (dominates_iff.mp hνξ k).trans (dominates_iff.mp hμν k)

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

private theorem lex_lt_of_dominates_of_ne {n : ℕ} {μ ν : n.Partition}
    (hdom : Dominates μ ν) (hne : μ ≠ ν) :
    sortedParts ν < sortedParts μ := by
  apply lex_lt_of_prefix_sum_le (sortedParts_sum μ |>.trans (sortedParts_sum ν).symm)
  · intro i hi
    exact μ.parts_pos ((Multiset.mem_sort (· ≥ ·)).mp hi)
  · intro i hi
    exact ν.parts_pos ((Multiset.mem_sort (· ≥ ·)).mp hi)
  · exact dominates_iff.mp hdom
  · intro h
    apply hne
    apply Nat.Partition.ext
    calc
      μ.parts = ↑(sortedParts μ) := (Multiset.sort_eq μ.parts (· ≥ ·)).symm
      _ = ↑(sortedParts ν) := congrArg (fun l : List ℕ => (l : Multiset ℕ)) h
      _ = ν.parts := Multiset.sort_eq ν.parts (· ≥ ·)

/-- Dominance is antisymmetric. -/
theorem Dominates.antisymm {n : ℕ} {μ ν : n.Partition}
    (hμν : Dominates μ ν) (hνμ : Dominates ν μ) : μ = ν := by
  by_contra hne
  have hν_lt_μ := lex_lt_of_dominates_of_ne hμν hne
  have hμ_lt_ν := lex_lt_of_dominates_of_ne hνμ (Ne.symm hne)
  exact hν_lt_μ.asymm hμ_lt_ν

namespace DominanceOrder

/-- The dominance partial order on partitions, oriented so that `ν ≤ μ` means that `μ`
dominates `ν`. Activate it with `open scoped TauCeti.DominanceOrder`. -/
scoped instance partitionPartialOrder {n : ℕ} : PartialOrder n.Partition where
  le μ ν := Dominates ν μ
  le_refl μ := dominates_refl μ
  le_trans _ _ _ hμν hνξ := hνξ.trans hμν
  le_antisymm _ _ hμν hνμ := hνμ.antisymm hμν

/-- Partition comparison in the dominance order is dominance in the reverse direction. -/
@[simp]
theorem partition_le_iff {n : ℕ} {μ ν : n.Partition} :
    @LE.le n.Partition partitionPartialOrder.toLE μ ν ↔ Dominates ν μ :=
  Iff.rfl

/-- Strict partition comparison in the dominance order is strict dominance in the reverse
direction. -/
@[simp]
theorem partition_lt_iff {n : ℕ} {μ ν : n.Partition} :
    @LT.lt n.Partition partitionPartialOrder.toLT μ ν ↔ Dominates ν μ ∧ μ ≠ ν := by
  letI := partitionPartialOrder (n := n)
  exact lt_iff_le_and_ne.trans (and_congr partition_le_iff Iff.rfl)

end DominanceOrder

/-- Strict dominance is the strict relation of the dominance partial order. -/
def StrictlyDominates {n : ℕ} (μ ν : n.Partition) : Prop :=
  DominanceOrder.partitionPartialOrder.lt ν μ

/-- Strict dominance is dominance between unequal partitions. -/
@[simp]
theorem strictlyDominates_iff {n : ℕ} {μ ν : n.Partition} :
    StrictlyDominates μ ν ↔ Dominates μ ν ∧ μ ≠ ν := by
  exact DominanceOrder.partition_lt_iff.trans (and_congr Iff.rfl ne_comm)

/-- Strict dominance is a strict order on partitions, inherited from the dominance partial
order. -/
instance {n : ℕ} : IsStrictOrder n.Partition StrictlyDominates :=
  letI := DominanceOrder.partitionPartialOrder (n := n)
  inferInstanceAs (IsStrictOrder n.Partition (Function.swap (· < ·)))

instance {n : ℕ} (μ ν : n.Partition) : Decidable (StrictlyDominates μ ν) := by
  rw [strictlyDominates_iff]
  infer_instance

open scoped PartitionLex

/-- Strict dominance refines the lexicographic linear order on partitions. -/
theorem lex_lt_of_strictlyDominates {n : ℕ} {μ ν : n.Partition}
    (h : StrictlyDominates μ ν) : ν < μ := by
  rw [PartitionLex.partition_lt_iff]
  rw [strictlyDominates_iff] at h
  exact lex_lt_of_dominates_of_ne h.1 h.2

/-- The one-part partition dominates every partition of the same natural number. -/
@[simp]
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
@[simp]
theorem dominates_indiscrete_iff {n : ℕ} {μ : n.Partition} :
    Dominates μ (Nat.Partition.indiscrete n) ↔ μ = Nat.Partition.indiscrete n := by
  constructor
  · intro h
    exact h.antisymm (indiscrete_dominates μ)
  · rintro rfl
    exact dominates_refl _

end TauCeti
