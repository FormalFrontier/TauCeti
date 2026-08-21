/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Closure

import Mathlib.Topology.ClusterPt

/-!
# Shrinking an open set to separate part of a non-accumulating set

If every point of `K ⊆ V` avoids the closure of `Z \ K`, the open ambient set `V`
shrinks to an open neighbourhood of `K` meeting `Z` in exactly `K ∩ Z`. This is the
localization step for residue computations — a contour region is
shrunk until the only singularities it contains are the intended ones.

## Main declarations

* `TauCeti.exists_isOpen_inter_eq_of_notMem_closure` (with the accumulation-hypothesis
  corollary `TauCeti.exists_isOpen_inter_eq_of_not_accPt`).
-/

public section

namespace TauCeti

/-- A set `K ⊆ V` whose points avoid the closure of `Z \ K` shrinks the open ambient `V`
to an open neighbourhood meeting `Z` exactly in `K ∩ Z`: remove that closure. -/
theorem exists_isOpen_inter_eq_of_notMem_closure {X : Type*} [TopologicalSpace X]
    {V Z K : Set X} (hV : IsOpen V) (hKV : K ⊆ V)
    (hK : ∀ x ∈ K, x ∉ closure (Z \ K)) :
    ∃ U : Set X, IsOpen U ∧ K ⊆ U ∧ U ⊆ V ∧ U ∩ Z = K ∩ Z := by
  refine ⟨V \ closure (Z \ K), hV.sdiff isClosed_closure,
    fun x hx => ⟨hKV hx, hK x hx⟩, Set.sdiff_subset, ?_⟩
  refine Set.Subset.antisymm ?_ fun z hz => ⟨⟨hKV hz.1, hK z hz.1⟩, hz.2⟩
  rintro z ⟨⟨hzV, hznc⟩, hzZ⟩
  refine ⟨?_, hzZ⟩
  by_contra hzK
  exact hznc (subset_closure ⟨hzZ, hzK⟩)

/-- The separation under the stronger hypothesis that no point of `K` is an accumulation
point of `Z` at all. -/
theorem exists_isOpen_inter_eq_of_not_accPt {X : Type*} [TopologicalSpace X] {V Z K : Set X}
    (hV : IsOpen V) (hKV : K ⊆ V)
    (hacc : ∀ x ∈ K, ¬AccPt x (Filter.principal Z)) :
    ∃ U : Set X, IsOpen U ∧ K ⊆ U ∧ U ⊆ V ∧ U ∩ Z = K ∩ Z := by
  refine exists_isOpen_inter_eq_of_notMem_closure hV hKV fun x hx hxc => ?_
  have hx_notin : x ∉ Z \ K := fun h => h.2 hx
  have hcl : ClusterPt x (Filter.principal ((Z \ K) \ {x})) := by
    rwa [Set.sdiff_singleton_eq_self hx_notin, ← mem_closure_iff_clusterPt]
  exact hacc x hx ((accPt_principal_iff_clusterPt.mpr hcl).mono
    (Filter.principal_mono.mpr Set.sdiff_subset))

end TauCeti

end
