/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Extending a submodule basis by a quotient basis, indexed by `Fin (m + n)`

`Module.Basis.sumQuot` combines a basis of a submodule `p` of `V` with a basis of `V ⧸ p` into a
basis of `V` indexed by a sum type. An induction on `Module.finrank` wants that basis indexed by
`Fin (m + n)` instead, so that the two blocks are picked out by `Fin.castAdd` and `Fin.natAdd` and
the resulting matrices are visibly block triangular.

This file records that reindexing together with the six equations locating the blocks: what the
basis is on each block, what the coordinates of a vector are there, and the two `_of_mem` variants
stated for an ambient vector known to lie in the submodule.

## Main definitions

* `TauCeti.extensionBasis`: the `Fin (m + n)`-indexed basis of `V` built from a basis of `p` and a
  basis of `V ⧸ p`.

## Main results

* `TauCeti.extensionBasis_castAdd` and `TauCeti.extensionBasis_natAdd_mkQ`: the basis vectors on
  the two blocks.
* `TauCeti.extensionBasis_repr_castAdd` and `TauCeti.extensionBasis_repr_natAdd`: the coordinates
  of a vector on the two blocks.
* `TauCeti.extensionBasis_repr_castAdd_of_mem` and `TauCeti.extensionBasis_repr_natAdd_of_mem`: the
  same for an ambient vector known to lie in the submodule, whose second-block coordinates vanish.
-/

public section

namespace TauCeti

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] {m n : ℕ}

open Module

/-- Extend bases of a submodule and of its quotient to a basis of the ambient module, indexed by
`Fin (m + n)`. -/
noncomputable def extensionBasis (p : Submodule R V) (bp : Basis (Fin m) R p)
    (bq : Basis (Fin n) R (V ⧸ p)) : Basis (Fin (m + n)) R V :=
  (bp.sumQuot bq).reindex finSumFinEquiv

/-- On the first block, `extensionBasis` is the given basis of the submodule. -/
@[simp]
theorem extensionBasis_castAdd (p : Submodule R V) (bp : Basis (Fin m) R p)
    (bq : Basis (Fin n) R (V ⧸ p)) (i : Fin m) :
    extensionBasis p bp bq (Fin.castAdd n i) = bp i := by
  rw [extensionBasis, Basis.reindex_apply, finSumFinEquiv_symm_apply_castAdd,
    Basis.sumQuot_inl]

/-- On the second block, `extensionBasis` lifts the given basis of the quotient. -/
@[simp]
theorem extensionBasis_natAdd_mkQ (p : Submodule R V) (bp : Basis (Fin m) R p)
    (bq : Basis (Fin n) R (V ⧸ p)) (j : Fin n) :
    Submodule.Quotient.mk (extensionBasis p bp bq (Fin.natAdd m j)) = bq j := by
  rw [extensionBasis, Basis.reindex_apply, finSumFinEquiv_symm_apply_natAdd,
    Basis.sumQuot_inr]

/-- The first-block coordinates of a vector of the submodule are its coordinates there.

Not a `simp` lemma: `extensionBasis_repr_castAdd_of_mem` is the `simp` normal form, matching how
Mathlib annotates `Module.Basis.sumQuot_repr_inl` and `sumQuot_repr_inl_of_mem`. -/
theorem extensionBasis_repr_castAdd (p : Submodule R V) (bp : Basis (Fin m) R p)
    (bq : Basis (Fin n) R (V ⧸ p)) (x : p) (i : Fin m) :
    (extensionBasis p bp bq).repr x (Fin.castAdd n i) = bp.repr x i := by
  rw [extensionBasis, Basis.repr_reindex_apply, finSumFinEquiv_symm_apply_castAdd,
    Basis.sumQuot_repr_inl]

/-- The second-block coordinates of a vector are the coordinates of its quotient class. -/
@[simp]
theorem extensionBasis_repr_natAdd (p : Submodule R V) (bp : Basis (Fin m) R p)
    (bq : Basis (Fin n) R (V ⧸ p)) (x : V) (j : Fin n) :
    (extensionBasis p bp bq).repr x (Fin.natAdd m j) = bq.repr (p.mkQ x) j := by
  rw [extensionBasis, Basis.repr_reindex_apply, finSumFinEquiv_symm_apply_natAdd,
    Basis.sumQuot_repr_inr]

/-- The first-block coordinates of an ambient vector lying in the submodule are its coordinates
there. -/
@[simp]
theorem extensionBasis_repr_castAdd_of_mem (p : Submodule R V) (bp : Basis (Fin m) R p)
    (bq : Basis (Fin n) R (V ⧸ p)) (x : V) (hx : x ∈ p) (i : Fin m) :
    (extensionBasis p bp bq).repr x (Fin.castAdd n i) = bp.repr ⟨x, hx⟩ i :=
  extensionBasis_repr_castAdd p bp bq ⟨x, hx⟩ i

/-- A vector of the submodule has no second-block coordinates: this is the vanishing of the
off-diagonal block.

Not a `simp` lemma: `extensionBasis_repr_natAdd` above already is, so this left-hand side is not in
`simp` normal form and marking it trips `simpNF`. Mathlib annotates its `sumQuot` counterparts the
same way — `sumQuot_repr_inr` is `simp` and `sumQuot_repr_inr_of_mem` is not. -/
theorem extensionBasis_repr_natAdd_of_mem (p : Submodule R V) (bp : Basis (Fin m) R p)
    (bq : Basis (Fin n) R (V ⧸ p)) (x : V) (hx : x ∈ p) (j : Fin n) :
    (extensionBasis p bp bq).repr x (Fin.natAdd m j) = 0 := by
  rw [extensionBasis_repr_natAdd, Submodule.mkQ_apply,
    (Submodule.Quotient.mk_eq_zero p).mpr hx, map_zero, Finsupp.coe_zero, Pi.zero_apply]

end TauCeti
