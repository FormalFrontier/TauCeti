/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Partition.Finpartition

/-!
# Finite partition helpers

This file contains general-purpose constructions and facts about finite partitions: the partition
of a set into a chosen subset and its complement, cardinality bounds for common refinements, and
the behavior of intersections of parts under refinement.
-/

public section

namespace Finpartition

variable {Ω : Type*} {u : Set Ω}

/-- The finite partition of the whole space into a set and its complement, omitting either part
when it is empty. -/
noncomputable def bipartition (s : Set Ω) : Finpartition (Set.univ : Set Ω) :=
  (Finpartition.ofPairwiseDisjoint {s, sᶜ} (by
    simp [Set.pairwiseDisjoint_insert, disjoint_compl_right])).copy (by simp)

@[simp]
theorem parts_bipartition (s : Set Ω) :
    (bipartition s).parts = ({s, sᶜ} : Finset (Set Ω)).erase ∅ :=
  by simp [bipartition]

/-- A bipartition has at most two parts. -/
theorem card_parts_bipartition_le (s : Set Ω) : (bipartition s).parts.card ≤ 2 := by
  rw [parts_bipartition]
  exact Finset.card_erase_le.trans (Finset.card_insert_le _ _ |>.trans_eq (by simp))

/-- A nonempty set is one of the two parts of its bipartition. -/
theorem mem_bipartition_of_ne_empty {s : Set Ω} (hs : s ≠ ∅) :
    s ∈ (bipartition s).parts := by
  simp [parts_bipartition, hs]

/-- The number of parts in a common refinement is at most the product of the two part counts. -/
theorem card_parts_inf_le_mul (P Q : Finpartition u) :
    (P ⊓ Q).parts.card ≤ P.parts.card * Q.parts.card := by
  rw [Finpartition.parts_inf]
  exact Finset.card_erase_le.trans
    (Finset.card_image_le.trans_eq (Finset.card_product _ _))

/-- Under refinement, a part of the finer partition is either contained in a given part of the
coarser one or disjoint from it. -/
theorem inter_part_eq_self_or_eq_empty_of_le {P Q : Finpartition u} (href : Q ≤ P)
    {r : Set Ω} (hr : r ∈ Q.parts) {p : Set Ω} (hp : p ∈ P.parts) :
    r ∩ p = r ∨ r ∩ p = ∅ := by
  obtain ⟨p', hp', hrp'⟩ := href hr
  by_cases h : p' = p
  · exact Or.inl (Set.inter_eq_self_of_subset_left (h ▸ hrp'))
  · refine Or.inr (Set.eq_empty_of_subset_empty fun x hx => ?_)
    exact absurd hx.2 (Set.disjoint_left.mp (P.disjoint hp' hp h) (hrp' hx.1))

end Finpartition
