/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.DoubleCoset.Basic

/-!
# Inverting a double coset

Inversion is an anti-automorphism of a group, so it carries the double coset `Γ₁ g Γ₂` to
`Γ₂ g⁻¹ Γ₁`: the flanking subgroups are exchanged and the element is inverted. This file records
that, as a set identity and in membership form.

Exchanging the flanking subgroups is what makes inversion useful for comparing the two sides of a
double coset: it turns a right-coset decomposition into a left-coset one, which is how a count
indexed by right cosets is matched with one indexed by left cosets.

## Main results

* `DoubleCoset.doubleCoset_inv`: as sets, `(Γ₁ g Γ₂)⁻¹ = Γ₂ g⁻¹ Γ₁`.
* `DoubleCoset.inv_mem_doubleCoset_inv_iff`: its membership form.
-/

public section

open Subgroup

open scoped Pointwise

namespace DoubleCoset

variable {G : Type*} [Group G]

/-- **Inverting a double coset exchanges its flanking subgroups.** As sets,
`(Γ₁ g Γ₂)⁻¹ = Γ₂ g⁻¹ Γ₁`. -/
@[simp]
lemma doubleCoset_inv (Γ₁ Γ₂ : Subgroup G) (g : G) :
    (doubleCoset g (Γ₁ : Set G) Γ₂)⁻¹ = doubleCoset g⁻¹ (Γ₂ : Set G) Γ₁ := by
  rw [doubleCoset, doubleCoset, mul_inv_rev, mul_inv_rev, Set.inv_singleton, inv_coe_set,
    inv_coe_set, ← mul_assoc]

/-- **Inverting a double coset exchanges its flanking subgroups**: `x ∈ Γ₁ g Γ₂` if and only if
`x⁻¹ ∈ Γ₂ g⁻¹ Γ₁`. The membership form of `doubleCoset_inv`.

Not `@[simp]`, unlike `doubleCoset_inv`: `mem_doubleCoset_iff_mk_mem_orbit` already rewrites
membership in a double coset to membership in a `MulAction.orbit`, so this left-hand side is not
in simp normal form and `simpNF` rejects it. Apply it by name. -/
lemma inv_mem_doubleCoset_inv_iff {Γ₁ Γ₂ : Subgroup G} {g x : G} :
    x⁻¹ ∈ doubleCoset g⁻¹ (Γ₂ : Set G) Γ₁ ↔ x ∈ doubleCoset g (Γ₁ : Set G) Γ₂ := by
  rw [← doubleCoset_inv, Set.mem_inv, inv_inv]

end DoubleCoset
