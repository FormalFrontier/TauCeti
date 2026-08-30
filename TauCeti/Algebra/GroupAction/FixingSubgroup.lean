/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Action.End
public import Mathlib.Data.Finset.Basic
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup
public import Mathlib.Logic.Equiv.Basic

/-!
# Pointwise fixing subgroups

This file records small generic additions to Mathlib's `fixingSubgroup` API, including the
permutations of a type that fix everything outside a finite set: the subgroup they form is the
one the signed sums of the Garnir relations range over.
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

/-- A permutation fixes the complement of a finite set `X` pointwise exactly when it moves no
point outside `X`. -/
theorem mem_fixingSubgroup_compl_coe_iff {α : Type*} {X : Finset α} {σ : Equiv.Perm α} :
    σ ∈ _root_.fixingSubgroup (Equiv.Perm α) ((X : Set α)ᶜ) ↔ ∀ k ∉ X, σ k = k := by
  simp [_root_.mem_fixingSubgroup_iff]

/-- The transposition of two points of `X` fixes the complement of `X` pointwise. -/
theorem swap_mem_fixingSubgroup_compl_coe {α : Type*} [DecidableEq α] {X : Finset α} {x y : α}
    (hx : x ∈ X) (hy : y ∈ X) :
    Equiv.swap x y ∈ _root_.fixingSubgroup (Equiv.Perm α) ((X : Set α)ᶜ) :=
  mem_fixingSubgroup_compl_coe_iff.mpr fun _ hk =>
    Equiv.swap_apply_of_ne_of_ne (fun h => hk (h ▸ hx)) fun h => hk (h ▸ hy)

end TauCeti
