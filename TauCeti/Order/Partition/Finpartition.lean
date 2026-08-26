/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Partition.Finpartition

/-!
# Finite partition helpers

This file contains general-purpose facts about refinements of finite partitions.
-/

public section

namespace Finpartition

variable {Ω : Type*} {u : Set Ω}

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
