/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.OpenMapping.Sequence
public import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean

/-!
# Removing the closure from Henkel's approximation

The Baire step of Henkel's open mapping theorem produces a point of `closure (f '' U)`, not of
`f '' U`, and every step after it inherits that closure. This file removes it: over a complete
source with a basis of open subgroups at zero, a point of `closure (f '' V 0)` really is the
image of a point of `V 0`.

Three ingredients meet here, and each supplies exactly one thing.

* The approximating sequence of `TauCeti/Topology/Algebra/OpenMapping/Sequence.lean` gives
  errors `x n ∈ V n` whose partial sums leave a residual in `closure (f '' V (n + 1))`.
* Completeness turns those errors into an actual sum: they tend to zero along the basis, and a
  null sequence in a complete nonarchimedean group is summable.
* Regularity of the target sends the residuals to zero. Continuity controls `f '' V (n + 1)`
  and never its closure, so it cannot do this alone; what does it is that a neighbourhood of
  zero in `N` contains the closure of a neighbourhood (`hasBasis_nhds_closure`).

The subgroups do the rest of the work: the sum of the errors stays inside `V 0` because `V 0` is
a subgroup and, being a neighbourhood of zero, is closed.

## Main results

* `TauCeti.mem_image_of_mem_closure_image`: `closure (f '' V 0) ⊆ f '' V 0`, in the presence of
  a basis of subgroups, completeness, and the neighbourhood hypothesis the Baire step supplies.

## References

* L. Henkel, *An Open Mapping Theorem for rings which have a zero sequence of units*,
  [arXiv:1407.5647](https://arxiv.org/abs/1407.5647).
-/

public section

open Filter Topology

namespace TauCeti

variable {M N : Type*} [AddCommGroup M] [UniformSpace M] [IsUniformAddGroup M] [CompleteSpace M]
  [AddGroup N] [TopologicalSpace N] [IsTopologicalAddGroup N] [T0Space N]

/-- **Henkel's approximation converges.** Let `V` be an antitone basis of subgroups at zero in a
complete group `M`, let `f : M → N` be an additive map continuous at zero, and suppose each
`closure (f '' V (n + 1))` is a neighbourhood of zero — which is what the Baire step of Henkel's
theorem provides. Then every point of `closure (f '' V 0)` is already the image of a point of
`V 0`.

`M` is not assumed nonarchimedean: a basis of subgroups at zero is exactly that condition, and
the proof reconstructs the instance from `hV`. `N` need not be commutative, and separation of it
is used only to identify the two limits of the partial sums. -/
theorem mem_image_of_mem_closure_image {F : Type*} [FunLike F M N] [AddMonoidHomClass F M N]
    (f : F) (hf : ContinuousAt (f : M → N) 0) {V : ℕ → AddSubgroup M}
    (hV : (𝓝 (0 : M)).HasAntitoneBasis fun n ↦ (V n : Set M))
    (hVN : ∀ n, closure ((f : M → N) '' (V (n + 1) : Set M)) ∈ 𝓝 (0 : N))
    {y : N} (hy : y ∈ closure ((f : M → N) '' (V 0 : Set M))) :
    y ∈ (f : M → N) '' (V 0 : Set M) := by
  have hf' : Continuous (f : M → N) := continuous_of_continuousAt_zero f hf
  obtain ⟨x, hxV, hxres⟩ :=
    exists_seq_mem_and_sub_sum_mem f (fun n ↦ (V n : Set M)) hVN hy
  -- A basis of subgroups at zero *is* nonarchimedeanness, so the instance need not be assumed.
  have : NonarchimedeanAddGroup M :=
    ⟨fun U hU ↦ by
      obtain ⟨n, -, hn⟩ := hV.toHasBasis.mem_iff.mp hU
      exact ⟨⟨V n, (V n).isOpen_of_mem_nhds (hV.toHasBasis.mem_of_mem trivial)⟩, hn⟩⟩
  -- The errors tend to zero along the basis, so in a complete group they are summable.
  have hsummable : Summable x :=
    NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
      (by rw [Nat.cofinite_eq_atTop]; exact hV.tendsto hxV)
  -- Their sum stays in `V 0`: an open subgroup is closed, and every error lies in it.
  refine ⟨∑' n, x n, tsum_mem ((V 0).isClosed_of_isOpen
    ((V 0).isOpen_of_mem_nhds (hV.toHasBasis.mem_of_mem trivial)))
    (fun n ↦ hV.antitone (Nat.zero_le n) (hxV n)), ?_⟩
  -- The partial sums have two limits under `f`: its value at the sum, and `y`.
  have hpart : Tendsto (fun n ↦ (f : M → N) (∑ i ∈ Finset.range (n + 1), x i)) atTop
      (𝓝 ((f : M → N) (∑' n, x n))) :=
    ((hf'.tendsto _).comp hsummable.hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)
  refine tendsto_nhds_unique hpart ?_
  -- The residuals tend to zero: the sets holding them shrink because `N` is regular.
  have hres : Tendsto (fun n ↦ y - (f : M → N) (∑ i ∈ Finset.range (n + 1), x i)) atTop
      (𝓝 (0 : N)) := by
    refine (hasBasis_nhds_closure (0 : N)).tendsto_right_iff.mpr fun U hU ↦ ?_
    have hpre : (f : M → N) ⁻¹' U ∈ 𝓝 (0 : M) :=
      hf (by rw [map_zero]; exact hU)
    obtain ⟨n₀, -, hn₀⟩ := hV.toHasBasis.mem_iff.mp hpre
    filter_upwards [eventually_ge_atTop n₀] with n hn
    exact closure_mono ((Set.image_mono
      ((hV.antitone (hn.trans (Nat.le_succ n))).trans hn₀)).trans
      (Set.image_preimage_subset _ _)) (hxres n)
  -- `-(y - f s) + y = f s` reassociates without commuting anything in `N`.
  simpa using hres.neg.add_const y

end TauCeti

end
