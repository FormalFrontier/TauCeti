/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Left translation on a coset space

A group `G` acts on the quotient `G ⧸ H` by translation.  This file records the stabilizer of a
coset for that action, and, for the trivial subgroup, the compatibility of the identification
`QuotientGroup.quotientBot : G ⧸ ⊥ ≃* G` with translation.

The stabilizer of the coset `sH` is the conjugate subgroup `sHs⁻¹`
(`TauCeti.stabilizer_quotientGroup_mk`); this is Mathlib's `MulAction.stabilizer_quotient`, which
covers the trivial coset, transported along `MulAction.stabilizer_smul_eq_stabilizer_map_conj`.

The cosets of `⊥` in a group `G` are the elements of `G`, and Mathlib's
`QuotientGroup.quotientBot` is that identification.  The identification is equivariant for left
translation, and the only element of `G` fixing a coset of `⊥` is the identity.

## Main statements

* `TauCeti.stabilizer_quotientGroup_mk`: the stabilizer of `sH` in `G` is `sHs⁻¹`.
* `TauCeti.quotientBot_equivariant`: `QuotientGroup.quotientBot` intertwines left translation on
  `G ⧸ ⊥` with left translation in `G`.
* `TauCeti.quotientBot_smul_eq_self_iff`: a group element fixes a coset of the trivial subgroup
  only when it is the identity.
-/

public section

open MulAction
open scoped Pointwise

namespace TauCeti

variable {G : Type*} [Group G]

/-- The stabilizer of the coset `sH`, for the translation action of `G` on `G ⧸ H`, is the
conjugate subgroup `sHs⁻¹`.  This is Mathlib's `MulAction.stabilizer_quotient` transported off the
trivial coset along `MulAction.stabilizer_smul_eq_stabilizer_map_conj`. -/
@[simp]
theorem stabilizer_quotientGroup_mk (H : Subgroup G) (s : G) :
    stabilizer G ((s : G ⧸ H)) = MulAut.conj s • H := by
  have hs : ((s : G) : G ⧸ H) = s • ((1 : G) : G ⧸ H) := by
    rw [Quotient.smul_coe, smul_eq_mul, mul_one]
  rw [hs, stabilizer_smul_eq_stabilizer_map_conj, stabilizer_quotient]
  -- `stabilizer_smul_eq_stabilizer_map_conj` leaves the conjugate as `H.map (MulAut.conj s)`,
  -- so the two descriptions are compared on elements rather than as subgroup maps.
  ext x
  rw [Subgroup.mem_map_equiv, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv,
    MulAut.smul_def, MulAut.conj_symm_apply, MulAut.conj_apply, inv_inv]

/-- Left translation on the cosets of the trivial subgroup is left translation in the group.

Not a `simp` lemma: `simp` rewrites the left-hand side further, to
`QuotientGroup.quotientBot (↑g * ↑x)`. -/
theorem quotientBot_smul (g x : G) :
    QuotientGroup.quotientBot (g • (x : G ⧸ (⊥ : Subgroup G))) =
      g * QuotientGroup.quotientBot (x : G ⧸ (⊥ : Subgroup G)) :=
  rfl

/-- Identifying the cosets of the trivial subgroup with the group is equivariant for left
translation.

Not a `simp` lemma: `simp` rewrites `MulEquiv.toEquiv` away in the left-hand side. -/
theorem quotientBot_equivariant (g : G) (q : G ⧸ (⊥ : Subgroup G)) :
    QuotientGroup.quotientBot.toEquiv (g • q) =
      g • QuotientGroup.quotientBot.toEquiv q := by
  induction q using QuotientGroup.induction_on with
  | H x => exact quotientBot_smul g x

/-- A group element fixes a coset of the trivial subgroup exactly when it is the identity. -/
@[simp]
theorem quotientBot_smul_eq_self_iff (g : G) (q : G ⧸ (⊥ : Subgroup G)) :
    g • q = q ↔ g = 1 := by
  constructor
  · intro h
    have := congrArg QuotientGroup.quotientBot h
    induction q using QuotientGroup.induction_on with
    | H x => simpa [quotientBot_smul] using this
  · rintro rfl
    exact one_smul _ _

end TauCeti
