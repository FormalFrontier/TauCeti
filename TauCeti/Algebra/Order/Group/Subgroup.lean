/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice

/-!
# Separating subgroups of a linearly ordered group

A subgroup strictly contained in another is separated from it by an element of prescribed sign:
`Δ < Γ'` admits a member of `Γ'` outside `Δ` that exceeds `1`, and dually one below `1`. Nothing
beyond a group, a linear order and inversion reversing strict order is assumed.

That the witness has a *strict* sign is what these are for. A monotone map out of `Γ` carries a
bound only to `≤`; a witness of this shape is what upgrades such a bound to the strict inequality
a cofinality argument needs.

## Main results

* `Subgroup.exists_one_lt_of_lt` and `Subgroup.exists_lt_one_of_lt` : the two orientations of the
  separation statement.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, §1.4 — the convex-subgroup and cofinality
  material these lemmas serve, in particular Definition 1.16 and Corollary 1.21.

Adapted from the AINTLIB development (Apache 2.0), file
`projects/AdicSpaces/Adic spaces/OrderedGroupConvex.lean`.
-/

public section

variable {Γ : Type*} [Group Γ] [LinearOrder Γ] [MulLeftStrictMono Γ]

/-- **A strictly smaller subgroup is separated from the larger one by an element above `1`**:
`Δ < Γ'` admits a member of `Γ'` outside `Δ` that exceeds `1`. -/
theorem Subgroup.exists_one_lt_of_lt {Γ' Δ : Subgroup Γ} (hlt : Δ < Γ') :
    ∃ z, z ∈ Γ' ∧ z ∉ Δ ∧ 1 < z := by
  obtain ⟨x, hxQ, hxD⟩ := SetLike.exists_of_lt hlt
  rcases lt_trichotomy x 1 with hl | he | hg
  · exact ⟨x⁻¹, inv_mem hxQ, fun e ↦ hxD (by simpa using inv_mem e), one_lt_inv'.mpr hl⟩
  · exact absurd (he ▸ one_mem Δ) hxD
  · exact ⟨x, hxQ, hxD, hg⟩

/-- **A strictly smaller subgroup is separated from the larger one by an element below `1`**, the
order dual of `Subgroup.exists_one_lt_of_lt`. -/
theorem Subgroup.exists_lt_one_of_lt {Γ' Δ : Subgroup Γ} (hlt : Δ < Γ') :
    ∃ z, z ∈ Γ' ∧ z ∉ Δ ∧ z < 1 := by
  obtain ⟨z, hzΓ', hzΔ, hz⟩ := Subgroup.exists_one_lt_of_lt hlt
  exact ⟨z⁻¹, inv_mem hzΓ', fun e ↦ hzΔ (by simpa using inv_mem e), inv_lt_one'.mpr hz⟩

end
