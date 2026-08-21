/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.FixingSubgroup

/-!
# Pointwise fixing subgroups

This file records small generic additions to Mathlib's `fixingSubgroup` API.
-/

public section

namespace TauCeti

/-- For a faithful action, the subgroup fixing the whole space pointwise is trivial. -/
@[simp]
theorem fixingSubgroup_univ {G α : Type*} [Group G] [MulAction G α] [FaithfulSMul G α] :
    _root_.fixingSubgroup G (Set.univ : Set α) = ⊥ := by
  ext g
  rw [_root_.mem_fixingSubgroup_iff, Subgroup.mem_bot]
  refine ⟨fun hg => ?_, fun hg x _ => by rw [hg, one_smul]⟩
  exact FaithfulSMul.eq_of_smul_eq_smul fun x =>
    (hg x (Set.mem_univ x)).trans (one_smul G x).symm

end TauCeti
