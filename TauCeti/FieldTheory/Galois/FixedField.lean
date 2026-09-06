/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.Basic

/-!
# Fixed fields and fixing subgroups

Three complements to Mathlib's Galois correspondence.

For a finite Galois extension `M / K`, a subgroup `H ≤ Gal(M/K)` and an intermediate field `E`,
the fixed field of `H` and `E` generate `M` exactly when `H` meets the fixers of `E` trivially.

The correspondence is equivariant for conjugation: the fixed field of a conjugate subgroup is the
image of the fixed field under the conjugating automorphism.

The correspondence between subgroups and their fixed fields also holds with no hypothesis on
`M / K` at all, provided the subgroup is finite: Artin's theorem makes `M` finite Galois over the
fixed field of a finite `H`, and the fixers of that field are then exactly `H`. This is how a
subgroup of the automorphism group of an infinite extension is recovered from the field it cuts
out; the fixing subgroup of a subfield of finite degree is finite for the same reason.

## Main results

* `Subgroup.fixedField_sup_eq_top_iff`
* `IntermediateField.fixedField_map_conj`
* `IntermediateField.fixingSubgroup_fixedField_of_finite`
* `IntermediateField.finite_of_finiteDimensional_fixedField`
* `IntermediateField.card_fixingSubgroup_le`
-/

public section

open IntermediateField

namespace Subgroup

variable {K M : Type*} [Field K] [Field M] [Algebra K M] [FiniteDimensional K M] [IsGalois K M]

/-- **A trivial meet of subgroups is a full join of fields.** `M ^ H` and `E` generate `M` exactly
when `H ⊓ Gal(M/E)` is trivial.

This is the Galois correspondence read in both directions: `fixingSubgroup` turns a join of fields
into a meet of subgroups, and `fixedField` turns the trivial subgroup back into `⊤`.

Stated in the `Subgroup` namespace rather than `IntermediateField`, so that `H` — the first
explicit argument, and the one `fixedField` is applied to — carries the dot notation: a consumer
writes `H.fixedField_sup_eq_top_iff E`. -/
theorem fixedField_sup_eq_top_iff (H : Subgroup (M ≃ₐ[K] M)) (E : IntermediateField K M) :
    fixedField H ⊔ E = ⊤ ↔ H ⊓ E.fixingSubgroup = ⊥ := by
  constructor
  · intro h
    have := congrArg IntermediateField.fixingSubgroup h
    rwa [fixingSubgroup_sup, fixingSubgroup_fixedField, fixingSubgroup_top] at this
  · intro h
    have hbot : (fixedField H ⊔ E).fixingSubgroup = ⊥ := by
      rw [fixingSubgroup_sup, fixingSubgroup_fixedField, h]
    have := congrArg fixedField hbot
    rwa [IsGalois.fixedField_fixingSubgroup, fixedField_bot] at this

end Subgroup

namespace IntermediateField

variable {K M : Type*} [Field K] [Field M] [Algebra K M]

/-- **A finite group of automorphisms is the whole fixing subgroup of its fixed field.** Every
`K`-automorphism of `M` that fixes `M ^ H` pointwise already lies in `H`.

Mathlib's `IntermediateField.fixingSubgroup_fixedField` is the same conclusion under
`[FiniteDimensional K M]`, which is the stronger hypothesis: a finite-dimensional `M / K` has a
finite automorphism group, so every subgroup of it is finite. Finiteness of `H` is what an
infinite extension `M / K` can still supply. -/
theorem fixingSubgroup_fixedField_of_finite (H : Subgroup (M ≃ₐ[K] M)) [Finite H] :
    fixingSubgroup (fixedField H) = H := by
  refine le_antisymm (fun σ hσ ↦ ?_) ((le_iff_le _ _).mp le_rfl)
  rw [mem_fixingSubgroup_iff] at hσ
  obtain ⟨g, hg⟩ := FixedPoints.toAlgAut_surjective H M
    (AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) fun x ↦ hσ x x.2)
  have hgσ : (g : M ≃ₐ[K] M) = σ := AlgEquiv.ext fun z ↦ congrArg (fun τ ↦ τ z) hg
  exact hgσ ▸ g.2

/-- **An intermediate field of finite degree has a finite fixing subgroup**, being a copy of the
automorphism group of a finite extension. -/
instance finite_fixingSubgroup (E : IntermediateField K M) [FiniteDimensional E M] :
    Finite (fixingSubgroup E) :=
  .of_equiv _ (fixingSubgroupEquiv E).symm.toEquiv

/-- **A group of automorphisms whose fixed field has finite degree is finite.** Thus a subgroup of
`K`-automorphisms cannot be infinite when its fixed field has finite degree in `M`. -/
theorem finite_of_finiteDimensional_fixedField (H : Subgroup (M ≃ₐ[K] M))
    [FiniteDimensional (fixedField H) M] : Finite H :=
  letI := finite_fixingSubgroup (fixedField H)
  have hH : H ≤ fixingSubgroup (fixedField H) := (le_iff_le _ _).mp le_rfl
  .of_injective (Set.inclusion hH) (Set.inclusion_injective hH)

/-- **The fixing subgroup of an intermediate field of finite degree is no larger than that
degree**, the bound on the automorphisms of a finite extension. -/
theorem card_fixingSubgroup_le (E : IntermediateField K M) [FiniteDimensional E M] :
    Nat.card (fixingSubgroup E) ≤ Module.finrank E M := by
  rw [Nat.card_congr (fixingSubgroupEquiv E).toEquiv, Nat.card_eq_fintype_card]
  exact AlgEquiv.card_le

/-- **The Galois correspondence is conjugation-equivariant.** The fixed field of the conjugate
subgroup `σ H σ⁻¹` is the image under `σ` of the fixed field of `H`. -/
theorem fixedField_map_conj (H : Subgroup (M ≃ₐ[K] M)) (σ : M ≃ₐ[K] M) :
    fixedField (H.map (MulAut.conj σ).toMonoidHom) = (fixedField H).map σ.toAlgHom := by
  ext x
  simp only [mem_fixedField_iff, mem_map]
  constructor
  · intro h
    refine ⟨σ.symm x, fun g hg ↦ ?_, by simp⟩
    have hx := h (MulAut.conj σ g) (Subgroup.mem_map_of_mem _ hg)
    exact σ.injective (by simpa using hx)
  · rintro ⟨y, hy, rfl⟩ g ⟨h, hh, rfl⟩
    simpa using congrArg σ (hy h hh)

end IntermediateField
