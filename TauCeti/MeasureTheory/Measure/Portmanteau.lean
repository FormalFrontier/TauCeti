/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.Topology.Bases

/-!
# Weak convergence tested on a countable basis

Mathlib's portmanteau theorem turns a `liminf` inequality *for every open set* into weak
convergence of probability measures.  When the topology has a countable basis, every open set is
an increasing union of finite unions of basis sets, so the countably many finite unions already
carry the information: if their masses converge, the measures converge weakly.

The point of the reduction is the order of quantifiers.  A limit theorem that produces
convergence one measurable set at a time — an almost-sure limit theorem, say, whose exceptional
null set depends on the set tested — can be upgraded to convergence in the weak topology when a
countable determining test class is available, since its exceptional sets can then be collected
into one.

## Main results

* `MeasureTheory.tendsto_of_forall_tendsto_measure_biUnion_basis` — probability measures converge
  weakly along a countably generated filter as soon as, for every finite subfamily of a fixed
  countably indexed topological basis, the masses of its union converge.

## References

* Roadmap: `TauCetiRoadmap/Exchangeability/README.md`, Layer 6, weak empirical-measure
  convergence.  This file is the measure-theoretic half of that milestone, with no
  exchangeability in its statements.
-/

public section

open Filter Set TopologicalSpace

open scoped ENNReal Topology

namespace MeasureTheory

variable {Ω ι γ : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω] [OpensMeasurableSpace Ω]

/-- **Weak convergence is tested on the finite unions of a countable basis.** Let `B` be a
countably indexed topological basis of `Ω`.  If, for every finite set `s` of indices, the mass of
`⋃ i ∈ s, B i` under `μs c` converges to its mass under `μ`, then `μs` converges weakly to `μ`.

Finite unions are needed, not just the individual basis sets: an open set is covered by basis
sets, and only their finite unions approximate its mass from below in a directed way.

Convergence is stated because that is what a limit theorem delivers; the proof consumes it only
through the lower bound `μ (⋃ i ∈ s, B i) ≤ liminf …`. When just such a bound is available, use
Mathlib's `MeasureTheory.tendsto_of_forall_isOpen_le_liminf'` directly. -/
theorem tendsto_of_forall_tendsto_measure_biUnion_basis [Countable ι] {B : ι → Set Ω}
    (hB : IsTopologicalBasis (range B)) {μ : ProbabilityMeasure Ω}
    {μs : γ → ProbabilityMeasure Ω} {L : Filter γ} [L.IsCountablyGenerated]
    (h : ∀ s : Finset ι, Tendsto (fun c => (μs c : Measure Ω) (⋃ i ∈ s, B i)) L
      (𝓝 ((μ : Measure Ω) (⋃ i ∈ s, B i)))) :
    Tendsto μs L (𝓝 μ) := by
  classical
  rcases L.eq_or_neBot with rfl | hL
  · simp
  refine tendsto_of_forall_isOpen_le_liminf' fun G hG => ?_
  -- The finite unions of the basis sets contained in `G` exhaust `G` from below.
  have hsub : ∀ s : Finset ι, (⋃ i ∈ s.filter fun i => B i ⊆ G, B i) ⊆ G := fun s =>
    iUnion₂_subset fun _ hi => (Finset.mem_filter.1 hi).2
  have hmono : ∀ s t : Finset ι, s ⊆ t →
      (⋃ i ∈ s.filter fun i => B i ⊆ G, B i) ⊆ ⋃ i ∈ t.filter fun i => B i ⊆ G, B i :=
    fun _ _ hst => iUnion₂_subset fun _ hi =>
      Finset.subset_set_biUnion_of_mem (Finset.filter_subset_filter _ hst hi)
  have hdir : Directed (· ⊆ ·) fun s : Finset ι => ⋃ i ∈ s.filter fun i => B i ⊆ G, B i :=
    fun s t => ⟨s ∪ t, hmono _ _ Finset.subset_union_left, hmono _ _ Finset.subset_union_right⟩
  have hcover : ⋃ s : Finset ι, (⋃ i ∈ s.filter fun i => B i ⊆ G, B i) = G := by
    refine Subset.antisymm (iUnion_subset hsub) fun x hx => ?_
    obtain ⟨-, ⟨i, rfl⟩, hxi, hiG⟩ := hB.exists_subset_of_mem_open hx hG
    exact mem_iUnion.2 ⟨{i}, subset_iUnion₂ i (by simp [hiG]) hxi⟩
  calc (μ : Measure Ω) G
      = ⨆ s : Finset ι, (μ : Measure Ω) (⋃ i ∈ s.filter fun i => B i ⊆ G, B i) := by
        conv_lhs => rw [← hcover]
        exact hdir.measure_iUnion
    _ ≤ L.liminf fun c => (μs c : Measure Ω) G := by
        refine iSup_le fun s => ?_
        rw [← (h (s.filter fun i => B i ⊆ G)).liminf_eq]
        exact liminf_le_liminf (.of_forall fun c => measure_mono (hsub s))

end MeasureTheory
