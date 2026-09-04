/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.MeasurableSpace.Basic
public import TauCeti.Order.Partition.Finpartition

/-!
# Measurable finite partitions

This file records elementary ways to construct measurable finite partitions and shows that
measurability passes from a finer finite partition to a coarser one.
-/

public section

open Set

namespace Finpartition

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Every part of a bipartition along a measurable set is measurable. -/
theorem measurableSet_of_mem_bipartition {s p : Set Ω} (hs : MeasurableSet s)
    (hp : p ∈ (bipartition s).parts) : MeasurableSet p := by
  rw [parts_bipartition, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp.2 with rfl | rfl
  · exact hs
  · exact hs.compl

/-- The common refinement of two measurable finite partitions is measurable. -/
theorem measurableSet_of_mem_inf {u : Set Ω} {P Q : Finpartition u}
    (hP : ∀ p ∈ P.parts, MeasurableSet p) (hQ : ∀ q ∈ Q.parts, MeasurableSet q)
    {r : Set Ω} (hr : r ∈ (P ⊓ Q).parts) : MeasurableSet r := by
  rw [Finpartition.parts_inf, Finset.mem_erase, Finset.mem_image] at hr
  obtain ⟨_, pq, hpq, rfl⟩ := hr
  rw [Finset.mem_product] at hpq
  exact (hP pq.1 hpq.1).inter (hQ pq.2 hpq.2)

/-- A part of a finite partition is measurable when it is a union of parts of a measurable
refinement. -/
theorem measurableSet_of_mem_of_le {u : Set Ω} {P Q : Finpartition u}
    (hQ : ∀ q ∈ Q.parts, MeasurableSet q) (href : Q ≤ P) {p : Set Ω} (hp : p ∈ P.parts) :
    MeasurableSet p := by
  classical
  let parts := Q.parts.filter fun q => q ⊆ p
  have hp_eq : p = ⋃₀ (parts : Set (Set Ω)) := by
    ext x
    constructor
    · intro hx
      have hx_parts : x ∈ ⋃₀ (Q.parts : Set (Set Ω)) := by
        rw [← Finset.sup_id_set_eq_sUnion, Q.sup_parts]
        exact P.le hp hx
      obtain ⟨q, hq, hxq⟩ := Set.mem_sUnion.1 hx_parts
      obtain ⟨p', hp', hqp'⟩ := href hq
      have hp'p : p' = p := P.disjoint.elim hp' hp <|
        Set.not_disjoint_iff.2 ⟨x, hqp' hxq, hx⟩
      exact Set.mem_sUnion.2 ⟨q, Finset.mem_filter.2 ⟨hq, hp'p ▸ hqp'⟩, hxq⟩
    · intro hx
      obtain ⟨q, hq, hxq⟩ := Set.mem_sUnion.1 hx
      exact (Finset.mem_filter.1 hq).2 hxq
  rw [hp_eq]
  exact parts.finite_toSet.measurableSet_sUnion fun q hq =>
    hQ q (Finset.mem_filter.1 hq).1

end Finpartition
