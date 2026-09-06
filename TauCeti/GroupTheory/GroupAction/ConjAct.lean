/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# Conjugation by an element of a normal subgroup, seen through a commutative target

A normal subgroup `N` of `G` carries the conjugation action `MulAut.conjNormal` of the whole of
`G`. Conjugation by an element of `N` itself is inner, so a homomorphism `ψ : N →* M` to a
*commutative* group cannot see it: conjugating the argument conjugates the value, and in a
commutative group that is the value again.

## Main statements

* `TauCeti.map_conjNormal_val`: a homomorphism from a normal subgroup to a commutative group is
  unchanged by conjugation by an element of that subgroup.
-/

public section

namespace TauCeti

variable {G M : Type*} [Group G] [CommGroup M] {N : Subgroup G} [N.Normal]

/-- **Conjugation by an element of a normal subgroup does not move a homomorphism from that
subgroup to a commutative group**: it conjugates the value, which is the value. -/
theorem map_conjNormal_val (ψ : N →* M) (a x : N) : ψ (MulAut.conjNormal (a : G) x) = ψ x := by
  simp [MulAut.conjNormal_val, MulAut.conj_apply]

end TauCeti
