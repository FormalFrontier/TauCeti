/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Coalgebra.GroupLike

/-!
# Transport of group-like elements along coalgebra equivalences

A coalgebra equivalence preserves the group-like equations in both directions and therefore
induces an equivalence of group-like elements.

## Main declarations

* `TauCeti.GroupLike.equivOfCoalgEquiv`: the equivalence induced by a coalgebra equivalence.
-/

public section

namespace TauCeti

universe u v w

namespace GroupLike

variable {R : Type u} {A : Type v} {B : Type w}
variable [CommSemiring R]
variable [AddCommMonoid A] [AddCommMonoid B] [Module R A] [Module R B]
variable [Coalgebra R A] [Coalgebra R B]

/-- A coalgebra equivalence induces an equivalence of group-like elements. -/
def equivOfCoalgEquiv (e : A ≃ₗc[R] B) :
    _root_.GroupLike R A ≃ _root_.GroupLike R B where
  toFun x := ⟨e x.val, x.isGroupLikeElem_val.map e⟩
  invFun x := ⟨e.symm x.val, x.isGroupLikeElem_val.map e.symm⟩
  left_inv x := _root_.GroupLike.val_injective (e.symm_apply_apply x.val)
  right_inv x := _root_.GroupLike.val_injective (e.apply_symm_apply x.val)

/-- The value of the transported group-like element is the image under the coalgebra
equivalence. -/
@[simp]
theorem val_equivOfCoalgEquiv (e : A ≃ₗc[R] B) (x : _root_.GroupLike R A) :
    (equivOfCoalgEquiv e x).val = e x.val :=
  (rfl)

/-- Transport along the identity coalgebra equivalence is the identity equivalence. -/
@[simp]
theorem equivOfCoalgEquiv_refl :
    equivOfCoalgEquiv (_root_.CoalgEquiv.refl R A) = Equiv.refl _ := by
  ext x
  rfl

/-- Transport along a composite coalgebra equivalence is the composite transport. -/
@[simp]
theorem equivOfCoalgEquiv_trans {C : Type*} [AddCommMonoid C] [Module R C] [Coalgebra R C]
    (e : A ≃ₗc[R] B) (f : B ≃ₗc[R] C) :
    equivOfCoalgEquiv (e.trans f) = (equivOfCoalgEquiv e).trans (equivOfCoalgEquiv f) := by
  ext x
  rfl

/-- Inverting transport is transport along the inverse coalgebra equivalence. -/
@[simp]
theorem equivOfCoalgEquiv_symm (e : A ≃ₗc[R] B) :
    (equivOfCoalgEquiv e).symm = equivOfCoalgEquiv e.symm := by
  ext x
  rfl

end GroupLike

end TauCeti
