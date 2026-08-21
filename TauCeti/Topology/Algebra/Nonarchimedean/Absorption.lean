/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Nonarchimedean.Basic

/-!
# Absorption of fixed elements in a nonarchimedean ring

In a nonarchimedean ring multiplication by a fixed element `a` is continuous, so every
neighbourhood `V` of zero absorbs `a`: some open additive subgroup `Z` satisfies `a * Z ⊆ V`.
That single-element fact is Mathlib's `NonarchimedeanRing.left_mul_subset`. This file adds the
one thing Mathlib does not have: the finite-family form, that one open subgroup absorbs each of
finitely many fixed elements into its own target.

It mentions no weight family, power series or Huber ring, so it is stated here rather than
alongside the theory that uses it.

## Main results

* `NonarchimedeanRing.exists_openAddSubgroup_forall_mul_subset`: finitely many fixed elements
  are absorbed into their own targets by a single open subgroup.

## References

* Mathlib's `Mathlib/Topology/Algebra/Nonarchimedean/Basic.lean`, whose
  `NonarchimedeanRing.left_mul_subset` the proof below runs on.
-/

public section

namespace NonarchimedeanRing

variable {A : Type*} [Ring A] [TopologicalSpace A] [NonarchimedeanRing A]

/-- **The finite-family absorption lemma**: one open subgroup absorbs each of finitely many fixed
elements into its own target.

The single-element case is Mathlib's `NonarchimedeanRing.left_mul_subset`, used directly in the
induction below; only the target has to be unbundled, since a subgroup that is a neighbourhood of
zero is open. -/
theorem exists_openAddSubgroup_forall_mul_subset {ι : Type*} (s : Finset ι) (a : ι → A)
    (V : ι → AddSubgroup A) (hV : ∀ i ∈ s, (V i : Set A) ∈ nhds (0 : A)) :
    ∃ Z : OpenAddSubgroup A, ∀ i ∈ s, ∀ z ∈ Z, a i * z ∈ V i := by
  classical
  induction s using Finset.induction with
  | empty => exact ⟨⊤, by simp⟩
  | insert i s' hi ih =>
      obtain ⟨Z', hZ'⟩ := ih fun j hj ↦ hV j (Finset.mem_insert_of_mem hj)
      obtain ⟨Z, hZ⟩ := left_mul_subset
        ⟨V i, (V i).isOpen_of_mem_nhds (hV i (Finset.mem_insert_self i s'))⟩ (a i)
      refine ⟨Z ⊓ Z', fun j hj z hz ↦ ?_⟩
      rcases Finset.mem_insert.mp hj with rfl | hj'
      · exact hZ ⟨z, hz.1, rfl⟩
      · exact hZ' j hj' z hz.2

end NonarchimedeanRing
