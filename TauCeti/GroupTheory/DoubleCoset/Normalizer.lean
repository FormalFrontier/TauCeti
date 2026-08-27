/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.DoubleCoset

import Mathlib.Tactic.Group

/-!
# Double cosets at a normalizing element

A double coset `ΓgΓ` is in general a union of several cosets on either side. When `g`
normalizes `Γ` it is a *single* coset, and the two sides agree:

`ΓgΓ = Γ(gΓg⁻¹)g = ΓΓg = Γg`.

This file records that collapse, together with the observation that a double coset at a
normalizing element consists of normalizing elements. Both are used wherever a Hecke double
coset attached to an element of the normalizer has to be recognised as a single coset — for
`Γ₁(N) ⊴ Γ₀(N)`, this is what makes the diamond operators double-coset operators.

## Main results

* `DoubleCoset.doubleCoset_eq_rightCoset_of_mem_normalizer`: `ΓgΓ = Γg` for `g` normalizing `Γ`.
* `DoubleCoset.mem_normalizer_of_mem_doubleCoset`: every element of such a `ΓgΓ` again
  normalizes `Γ`, so the collapse propagates to any representative of the double coset.
-/

public section

open MulOpposite

open scoped Pointwise

namespace DoubleCoset

variable {G : Type*} [Group G] {Γ : Subgroup G} {g : G}

/-- **A double coset at a normalizing element is a single right coset.** For `g` in the
normalizer of `Γ` the two flanking copies of `Γ` merge: the right-hand factor `b` of
`a * g * b` is absorbed by rewriting `g * b = (g * b * g⁻¹) * g`.

The left-coset form is the same statement, `Γ g Γ = g Γ`, read through `gΓ = Γg`; only the
right-coset form is stated, because that is the handedness in which Hecke operators decompose
a double coset. -/
theorem doubleCoset_eq_rightCoset_of_mem_normalizer (hg : g ∈ Subgroup.normalizer (Γ : Set G)) :
    doubleCoset g Γ Γ = op g • (Γ : Set G) := by
  ext x
  rw [mem_doubleCoset, mem_rightCoset_iff]
  refine ⟨?_, fun hx ↦ ⟨x * g⁻¹, hx, 1, Γ.one_mem, by simp⟩⟩
  rintro ⟨a, ha, b, hb, rfl⟩
  have hconj : g * b * g⁻¹ ∈ Γ := (Subgroup.mem_normalizer_iff.mp hg b).mp hb
  have hrw : a * g * b * g⁻¹ = a * (g * b * g⁻¹) := by group
  exact hrw ▸ Γ.mul_mem ha hconj

/-- **A double coset at a normalizing element consists of normalizing elements.** Every
`a * g * b` with `a, b ∈ Γ` lies in the normalizer of `Γ`, which contains both `Γ` and `g`.
Consequently `doubleCoset_eq_rightCoset_of_mem_normalizer` applies to *any* representative of
the double coset, not only to the chosen `g`. -/
theorem mem_normalizer_of_mem_doubleCoset (hg : g ∈ Subgroup.normalizer (Γ : Set G)) {x : G}
    (hx : x ∈ doubleCoset g Γ Γ) : x ∈ Subgroup.normalizer (Γ : Set G) := by
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_doubleCoset.mp hx
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.le_normalizer ha) hg)
    (Subgroup.le_normalizer hb)

end DoubleCoset
