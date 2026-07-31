/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Left translation on the cosets of the trivial subgroup

The cosets of `⊥` in a group `G` are the elements of `G`, and Mathlib's
`QuotientGroup.quotientBot` is that identification.  This file records that the identification is
equivariant for left translation, and that the only element of `G` fixing a coset of `⊥` is the
identity.

## Main statements

* `TauCeti.quotientBot_equivariant`: `QuotientGroup.quotientBot` intertwines left translation on
  `G ⧸ ⊥` with left translation in `G`.
* `TauCeti.quotientBot_smul_eq_self_iff`: a group element fixes a coset of the trivial subgroup
  only when it is the identity.
-/

public section

namespace TauCeti

variable {G : Type*} [Group G]

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
