/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.RingTheory.Valuation.Basic

/-!
# The sublevel sets of a valuation, as additive subgroups

For `γ ≠ 0` the set `{a | v a < γ}` is an additive subgroup: closure under addition is the strict
triangle inequality `v (x + y) ≤ max (v x) (v y)`, closure under negation is `v (-x) = v x`, and
`γ ≠ 0` is exactly what puts `0` in it.

Mathlib's `Valuation.ltAddSubgroup` is the same construction indexed by `Γ₀ˣ`, which forces a
`LinearOrderedCommGroupWithZero` codomain. Much of this repository's valuation theory — continuity
in particular — is stated over a `LinearOrderedCommMonoidWithZero`, where that version is
unavailable, and the construction was being repeated by hand at each site. This file states it once
at the weaker codomain; no inverses are used, only the strict triangle inequality.

Nothing here mentions a topology. It is deliberately separated from
`Valuation/Continuous/Basic.lean`, whose consumers happened to be the first to need it.

## Main definitions

* `Valuation.ltAddSubgroupOfNeZero` : the sublevel set `{a | v a < γ}` as an additive subgroup.

## References

* Mathlib's `Valuation.ltAddSubgroup`, the same construction over a value *group*.
-/

public section

namespace Valuation

variable {A : Type*} [Ring A] {Γ₀ : Type*} [LinearOrderedCommMonoidWithZero Γ₀]

/-- **A sublevel set of a valuation, as an additive subgroup.** For `γ ≠ 0` the set
`{a | v a < γ}` is an additive subgroup, by the strict triangle inequality and `v (-x) = v x`;
`γ ≠ 0` is what puts `0` in it.

The characteristic lemmas `Valuation.mem_ltAddSubgroupOfNeZero` and
`Valuation.coe_ltAddSubgroupOfNeZero` are the intended interface: the definition itself is sealed,
so downstream code does not depend on how the subgroup is packaged. -/
def ltAddSubgroupOfNeZero (v : Valuation A Γ₀) {γ : Γ₀} (hγ : γ ≠ 0) : AddSubgroup A where
  carrier := {a : A | v a < γ}
  add_mem' ha hb := lt_of_le_of_lt (v.map_add _ _) (max_lt ha hb)
  zero_mem' := by simpa using zero_lt_iff.mpr hγ
  neg_mem' hx := by simpa [v.map_neg] using hx

@[simp]
theorem mem_ltAddSubgroupOfNeZero {v : Valuation A Γ₀} {γ : Γ₀} (hγ : γ ≠ 0) {a : A} :
    a ∈ v.ltAddSubgroupOfNeZero hγ ↔ v a < γ := Iff.rfl

@[simp]
theorem coe_ltAddSubgroupOfNeZero {v : Valuation A Γ₀} {γ : Γ₀} (hγ : γ ≠ 0) :
    (v.ltAddSubgroupOfNeZero hγ : Set A) = {a : A | v a < γ} :=
  Set.ext fun _ ↦ mem_ltAddSubgroupOfNeZero hγ

end Valuation
