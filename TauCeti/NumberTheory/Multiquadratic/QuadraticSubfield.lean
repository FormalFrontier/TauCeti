/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.FieldTheory.IntermediateField.Quadratic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Quadratic subfields of a multiquadratic field from subset products

For square roots `root i` of radicands `d i ∈ K` over a field `K` with `2 ≠ 0`, the subset-product
root `∏_{i ∈ S} root i` squares into `K`: its square is the subset product `∏_{i ∈ S} d i` of the
radicands. Each subset therefore names a simple subfield `K(∏_{i ∈ S} root i)` of the
multiquadratic field `M = K(rootᵢ : i)`, and under square-class independence the nonempty ones are
genuinely quadratic and pairwise distinct: the assignment `S ↦ K(∏_{i ∈ S} root i)` from the
nonempty subsets of the index type is injective. This gives a concrete, arithmetic family of
quadratic subfields that the genus-field constructions consume, complementing the abstract
subfield/subspace dictionary of `TauCeti.NumberTheory.Multiquadratic.Subfield.Lattice` and
`TauCeti.NumberTheory.Multiquadratic.Subfield.Degree` (where a quadratic subfield is characterised
as a hyperplane of `𝔽₂ⁿ`).

The engine for distinctness is the standalone same-square-class criterion for simple quadratic
extensions, `TauCeti.IntermediateField.isSquare_mul_of_adjoin_simple_eq`: two square roots generate
the same simple extension only when their radicands lie in the same square class.

## Main results

* `TauCeti.Multiquadratic.prod_root_sq`: `(∏_{i ∈ S} root i)² = ∏_{i ∈ S} d i`.
* `TauCeti.Multiquadratic.prod_root_mem_adjoin`: the subset-product root lies in `M`.
* `TauCeti.Multiquadratic.finrank_adjoin_prod_root`: under square-class independence a nonempty
  subset-product root generates a quadratic subfield, `[K(∏_{i ∈ S} root i) : K] = 2`.
* `TauCeti.Multiquadratic.adjoin_prod_root_le`: that subfield sits inside `M`.
* `TauCeti.Multiquadratic.eq_of_adjoin_prod_root_eq`: distinct nonempty subsets give distinct
  quadratic subfields.

## Provenance

The one-step quadratic normal form this rests on (`mem_sup_adjoin_sq`,
`finrank_sup_adjoin_simple_eq_mul_two`) is migrated, with the rest of the multiquadratic Layer 0,
from [kim-em/erdos-unit-distance](https://github.com/kim-em/erdos-unit-distance), the formalization
of L. Alpöge's disproof of the uniform-constant Erdős unit-distance conjecture. The subset-product
description of the quadratic subfields is assembled here from that normal form.
-/

public section

open IntermediateField TauCeti.IntermediateField

namespace TauCeti.Multiquadratic

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {ι : Type*}
  {d : ι → K} {root : ι → L}

/-- **The square of a subset-product root.** The product `∏_{i ∈ S} root i` of the chosen roots
over a finite subset `S` squares to the subset product `∏_{i ∈ S} d i` of the radicands. -/
theorem prod_root_sq (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i)) (S : Finset ι) :
    (∏ i ∈ S, root i) ^ 2 = algebraMap K L (∏ i ∈ S, d i) := by
  rw [← Finset.prod_pow, map_prod]
  exact Finset.prod_congr rfl fun i _ => hroot i

/-- **A subset-product root lies in the multiquadratic field.** Each `∏_{i ∈ S} root i` is a
product of generators of `M = K(rootᵢ : i)`, hence a member of `M`. -/
theorem prod_root_mem_adjoin (S : Finset ι) :
    (∏ i ∈ S, root i) ∈ IntermediateField.adjoin K (Set.range root) :=
  prod_mem fun i _ => IntermediateField.subset_adjoin K _ ⟨i, rfl⟩

/-- **A subset-product root whose radicand product is not a square lies outside `K`.** If
`∏_{i ∈ S} root i` were in `⊥`, its square `∏_{i ∈ S} d i` would be a square in `K`. -/
private theorem prod_root_notMem_bot (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i))
    {S : Finset ι} (hSsq : ¬ IsSquare (∏ i ∈ S, d i)) :
    (∏ i ∈ S, root i) ∉ (⊥ : IntermediateField K L) := by
  rw [IntermediateField.mem_bot]
  rintro ⟨t, ht⟩
  refine hSsq ⟨t, ?_⟩
  have hsq : algebraMap K L (∏ i ∈ S, d i) = algebraMap K L (t * t) := by
    rw [map_mul, ht, ← prod_root_sq hroot, sq]
  exact FaithfulSMul.algebraMap_injective K L hsq

/-- **A nonempty subset-product root generates a quadratic subfield.** When the subset product
`∏_{i ∈ S} d i` of the radicands is not a square, the subset-product root of `S` lies outside `K`
yet squares into `K`, so `[K(∏_{i ∈ S} root i) : K] = 2`. -/
theorem finrank_adjoin_prod_root [NeZero (2 : K)] (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i))
    {S : Finset ι} (hSsq : ¬ IsSquare (∏ i ∈ S, d i)) :
    Module.finrank K (IntermediateField.adjoin K {∏ i ∈ S, root i}) = 2 := by
  have hx2 : (∏ i ∈ S, root i) ^ 2 ∈ (⊥ : IntermediateField K L) := by
    rw [prod_root_sq hroot]; exact IntermediateField.algebraMap_mem _ _
  have hxb := prod_root_notMem_bot hroot hSsq
  have h := finrank_sup_adjoin_simple_eq_mul_two (⊥ : IntermediateField K L) hx2 hxb
  rwa [bot_sup_eq, IntermediateField.finrank_bot, one_mul] at h

/-- **A subset-product subfield sits inside the multiquadratic field.** For any subset `S`, the
simple extension generated by `∏_{i ∈ S} root i` is contained in `M = K(rootᵢ : i)`. -/
theorem adjoin_prod_root_le (S : Finset ι) :
    IntermediateField.adjoin K {∏ i ∈ S, root i} ≤
      IntermediateField.adjoin K (Set.range root) :=
  IntermediateField.adjoin_simple_le_iff.mpr (prod_root_mem_adjoin S)

/-- **Distinct subsets give distinct quadratic subfields.** Under square-class independence the map
`S ↦ K(∏_{i ∈ S} root i)` from the nonempty subsets of the index type to the quadratic subfields of
`M` is injective: if two nonempty subsets generate the same subfield, they are equal. -/
theorem eq_of_adjoin_prod_root_eq [NeZero (2 : K)] (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i))
    (hindep : ∀ S : Finset ι, S.Nonempty → ¬ IsSquare (∏ i ∈ S, d i))
    {S T : Finset ι} (hS : S.Nonempty) (hST : IntermediateField.adjoin K {∏ i ∈ S, root i}
        = IntermediateField.adjoin K {∏ i ∈ T, root i}) :
    S = T := by
  classical
  -- The subset-product root of `S` lies outside `K`, else its square `∏_{i ∈ S} d i` would be one.
  have hxb := prod_root_notMem_bot hroot (hindep S hS)
  -- Sharing a quadratic field puts the two subset products in one square class.
  have hsq : IsSquare ((∏ i ∈ S, d i) * (∏ i ∈ T, d i)) :=
    isSquare_mul_of_adjoin_simple_eq (prod_root_sq hroot S) (prod_root_sq hroot T)
      hxb hST
  set E : Finset ι := (S ∪ T) \ (S ∩ T) with hE
  -- Factor the product of the two subset products through the symmetric difference `E`.
  have hfact : (∏ i ∈ S, d i) * (∏ i ∈ T, d i)
      = (∏ i ∈ E, d i) * (∏ i ∈ S ∩ T, d i) ^ 2 := by
    have h1 : (∏ i ∈ S, d i) * (∏ i ∈ T, d i)
        = (∏ i ∈ S ∪ T, d i) * (∏ i ∈ S ∩ T, d i) := Finset.prod_union_inter.symm
    have h2 : (∏ i ∈ E, d i) * (∏ i ∈ S ∩ T, d i) = ∏ i ∈ S ∪ T, d i :=
      Finset.prod_sdiff Finset.inter_subset_union
    rw [h1, ← h2]; ring
  -- Every radicand is nonzero, so the intersection product is nonzero.
  have hd_ne : ∀ i, d i ≠ 0 := fun i h =>
    hindep {i} (Finset.singleton_nonempty i) (by rw [Finset.prod_singleton, h]; exact ⟨0, by ring⟩)
  have hb_ne : (∏ i ∈ S ∩ T, d i) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hd_ne i
  -- Dividing out the square factor, the product over `E` is itself a square.
  have hEsq : IsSquare (∏ i ∈ E, d i) := by
    obtain ⟨r, hr⟩ := hsq
    refine ⟨r / (∏ i ∈ S ∩ T, d i), ?_⟩
    rw [div_mul_div_comm, ← hr, hfact, sq, mul_div_assoc,
      div_self (mul_ne_zero hb_ne hb_ne), mul_one]
  -- A nonempty `E` is a nonempty subset product that is a square, impossible; so `E` is empty.
  by_contra hne
  refine hindep E ?_ hEsq
  rw [hE, Finset.sdiff_nonempty]
  intro hsub
  apply hne
  have h3 : S ∪ T = S ∩ T := Finset.Subset.antisymm hsub Finset.inter_subset_union
  refine Finset.Subset.antisymm ?_ ?_
  · calc S ⊆ S ∪ T := Finset.subset_union_left
      _ = S ∩ T := h3
      _ ⊆ T := Finset.inter_subset_right
  · calc T ⊆ S ∪ T := Finset.subset_union_right
      _ = S ∩ T := h3
      _ ⊆ S := Finset.inter_subset_left

end TauCeti.Multiquadratic
