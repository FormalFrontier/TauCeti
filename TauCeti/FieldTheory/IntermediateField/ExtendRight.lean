/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.FieldTheory.IntermediateField.ExtendRight

/-!
# Membership and order for `IntermediateField.extendRight`

For a tower `K ⊆ L ⊆ M`, `IntermediateField.extendRight F M` is the copy of an intermediate
field `F` of `L / K` inside `M`. Mathlib defines it and transfers algebra structure along it,
but records nothing about how it sits in the order on intermediate fields of `M / K`. This file
adds that, together with the universal property of the copy of a simple extension `K⟮g⟯`: it is
the smallest intermediate field of `M / K` containing the image of `g`.

## Main results

* `IntermediateField.extendRight_eq_map`: the copy, as an `IntermediateField.map`.
* `IntermediateField.extendRight_le_iff`: the copy of `F` lies below an intermediate
  field exactly when that field contains every image from `F`.
* `IntermediateField.extendRight_adjoin_simple_le_iff`: the copy of `K⟮g⟯` lies inside an
  intermediate field exactly when that field contains the image of `g`.
-/

public section

namespace IntermediateField

variable {K L M : Type*} [Field K] [Field L] [Field M] [Algebra K L] [Algebra K M] [Algebra L M]
  [IsScalarTower K L M]

/-- `F.extendRight M` as an `IntermediateField.map`, spelled with `IsScalarTower.toAlgHom`. -/
-- Load-bearing rather than a cosmetic unfolding: `extendRight` is defined through
-- `Algebra.algHom`, while the `map` lemmas that meet it here are stated with
-- `IsScalarTower.toAlgHom`. The two are one term but not one piece of syntax, and
-- `relfinrank_map_map` will not unify across them.
theorem extendRight_eq_map (F : IntermediateField K L) :
    F.extendRight M = F.map (IsScalarTower.toAlgHom K L M) := rfl

/-- **The copy of `F` is below an intermediate field exactly when that field contains every
image from `F`.** This decides an inclusion pointwise, with no `comap`. -/
-- Not `@[simp]`: it and `extendRight_adjoin_simple_le_iff` below cannot both be, since this
-- rewrites that one's left-hand side and `simpNF` rejects the pair. The simple-extension form
-- is the one worth reaching automatically, so it keeps the attribute and this is used by name.
theorem extendRight_le_iff {F : IntermediateField K L} {E : IntermediateField K M} :
    F.extendRight M ≤ E ↔ ∀ x ∈ F, algebraMap L M x ∈ E := by
  rw [extendRight_eq_map]
  simp only [SetLike.le_def, mem_map, forall_exists_index, and_imp]
  exact ⟨fun h x hx => h x hx (congrFun (IsScalarTower.coe_toAlgHom' K L M) x),
    fun h _ x hx hxz => hxz ▸ h x hx⟩

/-- **The universal property of the copy of an adjoin**: the copy of `K⟮s⟯` inside `M` lies in an
intermediate field exactly when that field contains the image of every element of `s`. -/
theorem extendRight_adjoin_le_iff {s : Set L} {E : IntermediateField K M} :
    (adjoin K s).extendRight M ≤ E ↔ ∀ x ∈ s, algebraMap L M x ∈ E := by
  rw [extendRight_le_iff]
  refine ⟨fun h x hx => h x (subset_adjoin K s hx), fun h x hx => ?_⟩
  -- `K⟮s⟯` is the smallest intermediate field containing `s`, so it lies in the preimage of `E`
  -- as soon as every element of `s` does; `x` is then carried along.
  have hsub : adjoin K s ≤ E.comap (IsScalarTower.toAlgHom K L M) :=
    adjoin_le_iff.mpr h
  exact hsub hx

/-- **The universal property of the copy of a simple extension**: the copy of `K⟮g⟯` inside `M`
lies in an intermediate field exactly when that field contains the image of `g`. -/
@[simp]
theorem extendRight_adjoin_simple_le_iff {g : L} {E : IntermediateField K M} :
    (adjoin K {g}).extendRight M ≤ E ↔ algebraMap L M g ∈ E := by
  rw [extendRight_adjoin_le_iff, Set.forall_mem_singleton]

end IntermediateField

end
