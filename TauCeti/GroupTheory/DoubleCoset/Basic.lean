/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.GroupTheory.DoubleCoset

import Mathlib.Tactic.Group

/-!
# Double cosets: the left-coset decomposition

A double coset `HaK` decomposes as the union of the left cosets `(h * a) • K`, where `h`
ranges over representatives of the quotient of `H` by the stabiliser `H ∩ aKa⁻¹`. The
decomposition indexes the left cosets
inside a double coset and underlies the finiteness of Hecke coset decompositions in
`TauCeti.NumberTheory.HeckeRing.Basic`.

This file also records how the stabiliser `(gKg⁻¹).subgroupOf H` responds to moving the base
point `g`: right multiplication by anything normalising `K` leaves it alone, and left
multiplication by anything normalising `H` conjugates it. `TauCeti.NumberTheory.HeckeRing.
StabConjugation` turns those into equivalences of decomposition quotients.

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

/-- Conjugation only sees `g` modulo the normalizer on the right: `(gh)Γ(gh)⁻¹ = gΓg⁻¹`
whenever `h` normalizes `Γ`. Membership in `Γ` itself is the special case
`Subgroup.le_normalizer`. -/
lemma conjAct_smul_mul_right_of_mem_normalizer (Γ : Subgroup G) (g : G) {h : G}
    (hh : h ∈ Subgroup.normalizer Γ) :
    ConjAct.toConjAct (g * h) • Γ = ConjAct.toConjAct g • Γ := by
  rw [map_mul, ← smul_smul, Subgroup.conjAct_pointwise_smul_eq_self hh]

/-- The stabilizer cut out inside `Γ₁` is unchanged by right multiplication of the base point
by anything normalizing `Γ₂`. -/
lemma subgroupOf_conjAct_smul_mul_right_of_mem_normalizer (Γ₁ Γ₂ : Subgroup G) (g : G) {h : G}
    (hh : h ∈ Subgroup.normalizer Γ₂) :
    (ConjAct.toConjAct (g * h) • Γ₂).subgroupOf Γ₁ =
      (ConjAct.toConjAct g • Γ₂).subgroupOf Γ₁ := by
  rw [conjAct_smul_mul_right_of_mem_normalizer Γ₂ g hh]

/-- Left multiplication of the base point by anything normalizing `Γ₁` conjugates the
stabilizer by it: `x` stabilizes `hg` exactly when `h⁻¹xh` stabilizes `g`. Membership in `Γ₁`
itself is the special case `Subgroup.le_normalizer`.

The conjugating automorphism of `↥Γ₁` is `Subgroup.normalizerMonoidHom`, which is defined for
exactly this: `MulAut.conj h` would need `h` to be an element of `Γ₁`. -/
lemma subgroupOf_conjAct_smul_mul_left_of_mem_normalizer (Γ₁ Γ₂ : Subgroup G) (g : G)
    (h : Subgroup.normalizer (Γ₁ : Set G)) :
    (ConjAct.toConjAct ((h : G) * g) • Γ₂).subgroupOf Γ₁ =
      ((ConjAct.toConjAct g • Γ₂).subgroupOf Γ₁).map
        (Γ₁.normalizerMonoidHom h).toMonoidHom := by
  ext x
  rw [Subgroup.mem_map_equiv]
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    ConjAct.smul_def, map_inv, ConjAct.ofConjAct_toConjAct, inv_inv,
    Subgroup.normalizerMonoidHom_apply_symm_apply_coe]
  -- Both sides are membership of the *same* element of `Γ₂`, written with different
  -- bracketing: `(hg)⁻¹x(hg)` versus `g⁻¹(h⁻¹xh)g`. `group` proves that identity; the `iff`
  -- is then congruence along it, so no rewriting has to find a redex.
  exact iff_of_eq (congrArg (· ∈ Γ₂) (by group))

end DoubleCoset
