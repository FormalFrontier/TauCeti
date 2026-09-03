/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Two submodules meeting in zero inside a third

Mathlib's `Submodule.finrank_add_finrank_le_of_disjoint` bounds the dimensions of two disjoint
submodules by the dimension of the *ambient* module. `TauCeti.finrank_add_finrank_le_of_inf_eq_bot`
is the relative form: the bound holds inside any submodule containing them both, which is what a
counting argument that produces its two subspaces inside a third one needs.
-/

public section

namespace TauCeti

open Module (finrank)

/-
The lemma is stated for an abstract module `W`, and every call site supplies `W` explicitly.
Leaving `W` to unification makes the elaborator look for an `AddCommGroup` structure on a space --
of linear maps, of tensors -- whose `AddCommMonoid` structure is already fixed, which it does not
find quickly.
-/

/-- Two submodules meeting only in `0` have dimensions adding to at most that of any submodule
containing them both. -/
theorem finrank_add_finrank_le_of_inf_eq_bot {K W : Type*} [DivisionRing K] [AddCommGroup W]
    [Module K W] [FiniteDimensional K W]
    {S T U : Submodule K W} (hS : S ≤ U) (hT : T ≤ U) (h : S ⊓ T = ⊥) :
    finrank K S + finrank K T ≤ finrank K U := by
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq S T
  rw [h, finrank_bot, add_zero] at hsup
  rw [← hsup]
  exact Submodule.finrank_mono (sup_le hS hT)

end TauCeti
