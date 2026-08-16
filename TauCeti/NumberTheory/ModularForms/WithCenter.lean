/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.GroupTheory.Index
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic

/-!
# Adjoining the centre to a subgroup of `SL(2, ℤ)`

`Subgroup.withCenter` adjoins the centre of the ambient group. For `Γ ≤ SL(2, ℤ)` that centre is
`{±I}`, so the general characterisation `Subgroup.mem_withCenter_iff` — an element of `Γ·Z(G)` is
one of `Γ` times a central one — sharpens to the concrete reading recorded here: `Γ·{±I}` is
exactly `Γ` together with its negatives.

This is the form every `SL(2, ℤ)` consumer wants, and it depends on nothing beyond the general
`withCenter` API and the description of the centre of `SpecialLinearGroup`, so it sits here rather
than inside any one consumer.

## Main results

* `Subgroup.mem_withCenter_iff_exists_eq_or_eq_neg`: membership in `Γ·{±I}` is being `±` an
  element of `Γ`.
-/

public section

namespace TauCeti.ModularForm

open Matrix

open scoped MatrixGroups

variable {Γ : Subgroup SL(2, ℤ)}

/-- Membership in `Γ·{±I}`: its elements are exactly `±` the elements of `Γ`. The adjoined
centre of `SL₂(ℤ)` is `{±I}`, so the supremum only adds the negatives. -/
@[simp]
theorem _root_.Subgroup.mem_withCenter_iff_exists_eq_or_eq_neg {γ : SL(2, ℤ)} :
    γ ∈ Γ.withCenter ↔ ∃ γ' ∈ Γ, γ = γ' ∨ γ = -γ' := by
  refine ⟨fun hγ ↦ ?_, ?_⟩
  · obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_withCenter_iff.mp hγ
    obtain ⟨r, hr, hscal⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hb
    have hb1 : b = 1 ∨ b = -1 := by
      have hr1 : r = 1 ∨ r = -1 :=
        Int.isUnit_iff.mp (IsUnit.of_mul_eq_one r (by simpa [pow_two] using hr))
      rcases hr1 with rfl | rfl <;> [left; right] <;> exact Subtype.ext (by simpa using hscal.symm)
    exact ⟨a, ha, by rcases hb1 with rfl | rfl <;> simp⟩
  · rintro ⟨γ', hγ', rfl | rfl⟩
    · exact Subgroup.mem_withCenter_iff.mpr ⟨_, hγ', 1, Subgroup.one_mem _, mul_one _⟩
    · exact Subgroup.mem_withCenter_iff.mpr ⟨_, hγ', -1,
        Subgroup.mem_center_iff.mpr fun g ↦ by rw [neg_one_mul, mul_neg_one], mul_neg_one _⟩

end TauCeti.ModularForm

end
