/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.Basic

/-!
# The degree of a fixed field is the index of the subgroup

For a finite Galois extension `L / K` and a subgroup `H` of `Gal(L/K)`, Mathlib computes the degree
of `L` over the fixed field of `H` as the order of `H`
(`IntermediateField.finrank_fixedField_eq_card`). This file records the complementary reading, the
one the Galois correspondence is usually quoted in: the degree of the fixed field **over the base**
is the *index* of `H`.

It is a division in the tower `K ⊆ L^H ⊆ L`, using that the order of `Gal(L/K)` is the degree
`[L : K]` (`IsGalois.card_aut_eq_finrank`) and that the order of `H` times its index is the order
of the group (`Subgroup.card_mul_index`).

## Main result

* `TauCeti.IntermediateField.finrank_fixedField_eq_index`: `[L^H : K] = [Gal(L/K) : H]`.
-/

public section

open Module

namespace TauCeti.IntermediateField

/-- **The degree of a fixed field over the base is the index of the subgroup.** For a finite Galois
extension `L / K` and `H ≤ Gal(L/K)`, the fixed field `L^H` has degree `[Gal(L/K) : H]` over `K`.
In particular an index-two subgroup cuts out a quadratic subfield. -/
theorem finrank_fixedField_eq_index {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] (H : Subgroup (L ≃ₐ[K] L)) :
    finrank K (IntermediateField.fixedField H) = H.index := by
  have hcard : Nat.card H * H.index = finrank K L := by
    rw [Subgroup.card_mul_index, IsGalois.card_aut_eq_finrank]
  have htower : finrank K (IntermediateField.fixedField H) * Nat.card H = finrank K L := by
    rw [← IntermediateField.finrank_fixedField_eq_card H]
    exact finrank_mul_finrank K (IntermediateField.fixedField H) L
  refine Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := H)) ?_
  rw [htower, ← hcard, mul_comm]

end TauCeti.IntermediateField
