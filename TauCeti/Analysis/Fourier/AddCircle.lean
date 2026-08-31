/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.AddCircle

/-!
# The Fourier monomials as characters of the additive circle

Mathlib's `fourier n : C(AddCircle T, ℂ)` is developed as a family of `L²` monomials: the lemmas
about it record how it behaves in the *index* `n` (`fourier_add`, `fourier_neg`) and what it
contributes to the Fourier basis. This file records the two facts about the family that read it in
the other direction, as a family of group homomorphisms `AddCircle T → ℂˣ` indexed by `n`:

* each `fourier n` is multiplicative in its circle argument, so `x ↦ fourier n x` is a character of
  `AddCircle T`;
* distinct indices give distinct characters.

Both are immediate from Mathlib — the first from `AddCircle.toCircle_add`, the second from
`fourierCoeff_fourier` — but neither is stated there, and the character-theoretic reading is what a
representation-theoretic consumer needs.

## Main statements

* `TauCeti.fourier_apply_add`: `fourier n (x + y) = fourier n x * fourier n y`.
* `TauCeti.fourier_injective`: `n ↦ fourier n` is injective, so distinct indices give distinct
  characters.

## Tags

Fourier, additive circle, character
-/

public section

namespace TauCeti

variable {T : ℝ}

/-- **The Fourier monomial is multiplicative in its circle argument.** Together with
`AddCircle.fourier_eval_zero` this says that `x ↦ fourier n x` is a homomorphism from
`AddCircle T` to the unit circle of `ℂ`, i.e. a character of the circle group; Mathlib's
`fourier_add` is the companion additivity in the *index*. -/
theorem fourier_apply_add (n : ℤ) (x y : AddCircle T) :
    fourier n (x + y) = fourier n x * fourier n y := by
  simp [fourier_apply, smul_add, AddCircle.toCircle_add]

variable [hT : Fact (0 < T)]

/-- **Distinct indices give distinct Fourier monomials.** The `m`-th Fourier coefficient of
`fourier n` is `1` when `m = n` and `0` otherwise, so the coefficient functions of two monomials
with different indices already differ. -/
theorem fourier_injective : Function.Injective (fourier (T := T)) := by
  intro m n hmn
  by_contra hne
  have h : fourierCoeff (T := T) (fourier m) m = fourierCoeff (T := T) (fourier n) m :=
    congrFun (congrArg (fun f : C(AddCircle T, ℂ) => fourierCoeff (⇑f)) hmn) m
  rw [fourierCoeff_fourier, fourierCoeff_fourier] at h
  simp [hne] at h

end TauCeti
