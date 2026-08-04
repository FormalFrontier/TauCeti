/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.GroupTheory.DoubleCoset

/-!
# Double cosets: the left-coset decomposition

A double coset `HaK` decomposes as the union of the left cosets `(h * a) • K`, where `h`
ranges over representatives of the quotient of `H` by the stabiliser `H ∩ aKa⁻¹`. The
decomposition indexes the left cosets
inside a double coset and underlies the finiteness of Hecke coset decompositions in
`TauCeti.NumberTheory.HeckeRing.Basic`.

Vendored from the in-review mathlib4 PR
[#41253](https://github.com/leanprover-community/mathlib4/pull/41253) (Chris Birkbeck), per the
ModularForms roadmap's dependency policy; migrate to Mathlib and delete this file when that
stack merges.
-/

public section

open scoped Pointwise

namespace DoubleCoset

variable {G : Type*} [Group G]

/-- A double coset `HaK` is the union of the left cosets `(h * a) • K` where `h` ranges over
representatives of the quotient of `H` by the stabiliser `H ∩ aKa⁻¹`, with no repeated cosets;
compare `DoubleCoset.doubleCoset_union_leftCoset`, which is indexed by all of `H`. -/
lemma doubleCoset_eq_iUnion_leftCosets (H K : Subgroup G) (a : G) :
    doubleCoset a H K =
      ⋃ i : H ⧸ (ConjAct.toConjAct a • K).subgroupOf H, ((i.out : G) * a) • (K : Set G) := by
  rw [← doubleCoset_union_leftCoset]
  refine le_antisymm (Set.iUnion_subset fun h ↦ ?_) (Set.iUnion_subset fun i ↦
    Set.subset_iUnion (fun h : H ↦ ((h : G) * a) • (K : Set G)) i.out)
  obtain ⟨n, hn⟩ := QuotientGroup.mk_out_eq_mul ((ConjAct.toConjAct a • K).subgroupOf H) h
  have hK : a⁻¹ * ((n : H) : G) * a ∈ K := by
    have hmem := Subgroup.mem_subgroupOf.mp n.2
    rwa [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv,
      ConjAct.smul_def, ConjAct.ofConjAct_toConjAct, inv_inv] at hmem
  refine Set.subset_iUnion_of_subset (QuotientGroup.mk h) (le_of_eq ?_)
  rw [hn, leftCoset_eq_iff]
  simpa [mul_assoc] using hK

end DoubleCoset
