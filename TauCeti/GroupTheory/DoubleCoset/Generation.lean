/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Solvable
public import Mathlib.GroupTheory.DoubleCoset

/-!
# Generation from two double cosets

If every element outside a subgroup `B` lies in one double coset `B w B`, then `B` and `w`
generate the ambient group. When that group is nonsolvable, every solvable subgroup containing
`B` is therefore equal to `B`.

## Main statements

* `Subgroup.closure_insert_eq_top_of_notMem_imp_mem_doubleCoset`: a subgroup and a representative
  generate the ambient group when their two double cosets cover it.
* `Subgroup.le_of_isSolvable_of_not_isSolvable_of_notMem_imp_mem_doubleCoset`: in a nonsolvable
  group, that subgroup contains every solvable overgroup.
-/

public section

namespace Subgroup

variable {G : Type*} [Group G]

/-- If every element outside a subgroup `B` belongs to the double coset `B w B`, then `B` and
`w` generate the ambient group. -/
theorem closure_insert_eq_top_of_notMem_imp_mem_doubleCoset (B : Subgroup G) (w : G)
    (hcell : ∀ {g : G}, g ∉ B →
      g ∈ DoubleCoset.doubleCoset w (B : Set G) (B : Set G)) :
    Subgroup.closure (insert w (B : Set G)) = ⊤ := by
  refine eq_top_iff.mpr fun g _ ↦ ?_
  by_cases hg : g ∈ B
  · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ hg)
  · obtain ⟨x, hx, y, hy, rfl⟩ := DoubleCoset.mem_doubleCoset.mp (hcell hg)
    exact mul_mem
      (mul_mem (Subgroup.subset_closure (Set.mem_insert_of_mem _ hx))
        (Subgroup.subset_closure (Set.mem_insert _ _)))
      (Subgroup.subset_closure (Set.mem_insert_of_mem _ hy))

/-- Suppose every element outside `B` belongs to `B w B`. If the ambient group is not solvable,
then every solvable subgroup containing `B` is contained in `B`. -/
theorem le_of_isSolvable_of_not_isSolvable_of_notMem_imp_mem_doubleCoset
    (B P : Subgroup G) (w : G) [Group.IsSolvable P] (hG : ¬ Group.IsSolvable G)
    (hcell : ∀ {g : G}, g ∉ B →
      g ∈ DoubleCoset.doubleCoset w (B : Set G) (B : Set G))
    (hBP : B ≤ P) : P ≤ B := by
  by_contra hPB
  obtain ⟨g, hgP, hgB⟩ := SetLike.not_le_iff_exists.mp hPB
  obtain ⟨x, hx, y, hy, hxy⟩ := DoubleCoset.mem_doubleCoset.mp (hcell hgB)
  have hwP : w ∈ P := by
    have hxP := hBP hx
    have hyP := hBP hy
    have hprod : x⁻¹ * g * y⁻¹ ∈ P := mul_mem (mul_mem (inv_mem hxP) hgP) (inv_mem hyP)
    convert hprod using 1
    rw [hxy]
    simp [mul_assoc]
  have hclosure : Subgroup.closure (insert w (B : Set G)) ≤ P :=
    (Subgroup.closure_le P).mpr (Set.insert_subset_iff.mpr ⟨hwP, hBP⟩)
  rw [closure_insert_eq_top_of_notMem_imp_mem_doubleCoset B w hcell] at hclosure
  have hPtop : P = ⊤ := top_unique hclosure
  apply hG
  apply Group.isSolvable_of_surjective (f := P.subtype)
  intro g
  refine ⟨⟨g, ?_⟩, rfl⟩
  rw [hPtop]
  exact Subgroup.mem_top g

end Subgroup
