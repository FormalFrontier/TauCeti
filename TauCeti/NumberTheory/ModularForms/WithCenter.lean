/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Index
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic
public import TauCeti.NumberTheory.Modular

/-!
# Adjoining the centre to a subgroup of `SL(2, ℤ)`

`Subgroup.withCenter` adjoins the centre of the ambient group. For `Γ ≤ SL(2, ℤ)` that centre is
`{±I}`, by `Matrix.SpecialLinearGroup.mem_center_iff_eq_one_or_eq_neg_one`, so the general
characterisation `Subgroup.mem_withCenter_iff` — an element of `Γ·Z(G)` is one of `Γ` times a
central one — sharpens to the concrete reading recorded here: `Γ·{±I}` is exactly `Γ` together
with its negatives.

This is the form every `SL(2, ℤ)` consumer wants, and it depends on nothing beyond the general
`withCenter` API and the description of the centre of `SpecialLinearGroup`, so it sits here rather
than inside any one consumer.

The last section records the geometric counterpart: because `Γ·{±I}` contains both `1` and `-1`,
the translates of the open fundamental domain `𝒟ᵒ` indexed by the cosets of `Γ·{±I}` are pairwise
disjoint. This needs no more about `Γ` than the membership description above, so it sits here too.

## Main results

* `Subgroup.mem_withCenter_iff_exists_eq_or_eq_neg`: membership in `Γ·{±I}` is being `±` an
  element of `Γ`.
* `TauCeti.ModularForm.index_eq_two_mul_index_withCenter_of_neg_one_notMem` and
  `TauCeti.ModularForm.relIndex_withCenter_eq_two_of_neg_one_notMem`: when `-I ∉ Γ`,
  `[SL₂(ℤ) : Γ] = 2 · [SL₂(ℤ) : ±Γ]`.
* `ModularGroup.pairwise_disjoint_smul_fdo_out_withCenter`: the translates of `𝒟ᵒ` indexed by
  the cosets of `Γ·{±I}` are pairwise disjoint.
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
    exact ⟨a, ha, by
      rcases Matrix.SpecialLinearGroup.mem_center_iff_eq_one_or_eq_neg_one.mp hb with rfl | rfl <;>
        simp⟩
  · rintro ⟨γ', hγ', rfl | rfl⟩
    · exact Subgroup.mem_withCenter_iff.mpr ⟨_, hγ', 1, Subgroup.one_mem _, mul_one _⟩
    · exact Subgroup.mem_withCenter_iff.mpr ⟨_, hγ', -1,
        Matrix.SpecialLinearGroup.mem_center_iff_eq_one_or_eq_neg_one.mpr (Or.inr rfl),
        mul_neg_one _⟩

/-- **The `±Γ` factor of two, index form**: when `-I ∉ Γ`, the index of `Γ` in `SL(2, ℤ)` is
twice the projective index `[SL₂(ℤ) : ±Γ]`.

This is the conversion the general-level valence formula and the Sturm bound are stated
against: both read `k · [SL₂(ℤ) : ±Γ] / 12`, while a full-coset norm product is computed over
`Γ`-cosets, which is twice as many. -/
theorem index_eq_two_mul_index_withCenter_of_neg_one_notMem (h : (-1 : SL(2, ℤ)) ∉ Γ) :
    Γ.index = 2 * Γ.withCenter.index :=
  Subgroup.index_eq_two_mul_index_withCenter
    (Matrix.SpecialLinearGroup.mem_center_iff_eq_one_or_eq_neg_one.mpr (Or.inr rfl)) h
    fun _ hc ↦ Matrix.SpecialLinearGroup.mem_center_iff_eq_one_or_eq_neg_one.mp hc

/-- **The `±Γ` factor of two, relative-index form**: `Γ` has index `2` inside `Γ·{±I}` when
`-I ∉ Γ`. The geometric reading of
`index_eq_two_mul_index_withCenter_of_neg_one_notMem`: adjoining `-I` exactly halves the
number of cosets. -/
theorem relIndex_withCenter_eq_two_of_neg_one_notMem (h : (-1 : SL(2, ℤ)) ∉ Γ) :
    Γ.relIndex Γ.withCenter = 2 :=
  Subgroup.relIndex_withCenter_eq_two
    (Matrix.SpecialLinearGroup.mem_center_iff_eq_one_or_eq_neg_one.mpr (Or.inr rfl)) h
    fun _ hc ↦ Matrix.SpecialLinearGroup.mem_center_iff_eq_one_or_eq_neg_one.mp hc

end TauCeti.ModularForm

namespace ModularGroup

open scoped MatrixGroups Pointwise

/-- **The translates of `𝒟ᵒ` indexed by the cosets of `Γ·{±I}` are pairwise disjoint.** By
`ModularGroup.disjoint_smul_fdo` it suffices that the chosen representatives of two distinct
cosets differ neither by `1` nor by `−1`; and both `1` and `−1` lie in `Γ·{±I}`, so either
coincidence would identify the two cosets. -/
theorem pairwise_disjoint_smul_fdo_out_withCenter (Γ : Subgroup SL(2, ℤ)) :
    Pairwise (Function.onFun Disjoint
      fun q : SL(2, ℤ) ⧸ Γ.withCenter ↦ ((q.out)⁻¹ • fdo)) := by
  intro q₁ q₂ hq
  refine disjoint_smul_fdo ?_ ?_ <;> rw [inv_inv] <;> intro h <;> apply hq
  · rw [← Quotient.out_eq q₁, ← Quotient.out_eq q₂, mul_inv_eq_one.mp h]
  · have hneg : q₁.out = -q₂.out := by
      rw [mul_inv_eq_iff_eq_mul] at h
      simpa using h
    rw [← Quotient.out_eq q₁, ← Quotient.out_eq q₂, hneg]
    refine QuotientGroup.eq.mpr ?_
    have hcalc : (-q₂.out)⁻¹ * q₂.out = -1 := by rw [← neg_inv, neg_mul, inv_mul_cancel]
    rw [hcalc]
    exact Γ.center_le_withCenter
      (Matrix.SpecialLinearGroup.mem_center_iff_eq_one_or_eq_neg_one.mpr (Or.inr rfl))

end ModularGroup

end
