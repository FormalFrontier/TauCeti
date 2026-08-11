/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic.Group

/-!
# Square roots in a group

The **square roots** of an element `x` of a group `G` are the `g` with `g * g = x`. Conjugation
carries them bijectively onto the square roots of a conjugate of `x`
(`TauCeti.squareRootConjEquiv`), so their number depends only on the conjugacy class of `x`
(`TauCeti.card_squareRoot_conj`). That is what makes the square-root count a class function, and
hence expandable in the basis of irreducible characters.

## Main statements

* `TauCeti.squareRootConjEquiv`: conjugation is a bijection between the square roots of `x` and
  those of `h * x * h⁻¹`.
* `TauCeti.card_squareRoot_conj`: conjugate elements have equally many square roots.

## Implementation notes

`Nat.card` is used for the count, so no finiteness or decidability assumption is needed to state
the result.
-/

public section

namespace TauCeti

variable {G : Type*} [Group G]

/-- **Conjugation permutes square roots**: `g ↦ h * g * h⁻¹` is a bijection from the square roots
of `x` onto the square roots of `h * x * h⁻¹`. -/
def squareRootConjEquiv (x h : G) :
    {g : G // g * g = x} ≃ {g : G // g * g = h * x * h⁻¹} where
  toFun g := ⟨h * g.1 * h⁻¹, by
    have hexp : h * g.1 * h⁻¹ * (h * g.1 * h⁻¹) = h * (g.1 * g.1) * h⁻¹ := by group
    rw [hexp, g.2]⟩
  invFun g := ⟨h⁻¹ * g.1 * h, by
    have hexp : h⁻¹ * g.1 * h * (h⁻¹ * g.1 * h) = h⁻¹ * (g.1 * g.1) * h := by group
    rw [hexp, g.2]
    group⟩
  left_inv _ := Subtype.ext (by group)
  right_inv _ := Subtype.ext (by group)

/-- Conjugation of square roots is conjugation of group elements. -/
@[simp]
theorem squareRootConjEquiv_apply_coe (x h : G) (g : {g : G // g * g = x}) :
    (squareRootConjEquiv x h g : G) = h * (g : G) * h⁻¹ :=
  (rfl)

/-- The inverse of `TauCeti.squareRootConjEquiv` is conjugation by `h⁻¹`. -/
@[simp]
theorem squareRootConjEquiv_symm_apply_coe (x h : G) (g : {g : G // g * g = h * x * h⁻¹}) :
    ((squareRootConjEquiv x h).symm g : G) = h⁻¹ * (g : G) * h :=
  (rfl)

/-- **The number of square roots is a class function of the group element**: `x` and its
conjugate `h * x * h⁻¹` have equally many square roots. -/
theorem card_squareRoot_conj (x h : G) :
    Nat.card {g : G // g * g = h * x * h⁻¹} = Nat.card {g : G // g * g = x} :=
  Nat.card_congr (squareRootConjEquiv x h).symm

end TauCeti
