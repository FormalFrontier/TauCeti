/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Basic
public import TauCeti.NumberTheory.RamificationInertia.Tower

/-!
# Ramification indices in an extension of number fields

A consequence of the general ramification bounds for the rings of integers of number fields.
`TauCeti.NumberTheory.RamificationInertia.Tower` states it for a finite flat extension of
domains; here it is transported to the fields themselves, so the bound is `[F : K]` rather than
the rank of `𝓞 F` over `𝓞 K`.

## Main results

* `Ideal.ramificationIdx_le_finrank_numberField`: for a prime `𝔔` of `𝓞 F` in an extension
  `F / K` of number fields, `e(𝔔 / 𝓞 K) ≤ [F : K]`.
* `TauCeti.NumberField.finrank_eq_one_of_ramificationIdx_eq_finrank`: in a tower `K ≤ E ≤ B`, a
  prime of `𝓞 B` as ramified over `𝓞 E` as `[B : K]` allows forces `[E : K] = 1`.
-/

public section

open scoped NumberField

namespace TauCeti.NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- **A relative ramification index is at most the degree of the extension.** For a prime `𝔔` of
`𝓞 F` in an extension `F / K` of number fields, `e(𝔔 / 𝓞 K) ≤ [F : K]`.

This is `TauCeti.RamificationInertia.ramificationIdx_le_finrank` for the rings of integers,
transported along `IsFractionRing.finrank_eq` so that the bound is the degree of the field
extension rather than the rank of `𝓞 F` over `𝓞 K`. -/
theorem _root_.Ideal.ramificationIdx_le_finrank_numberField {F : Type*} [Field F]
    [NumberField F] [Algebra K F] (𝔔 : Ideal (𝓞 F)) [𝔔.IsPrime] :
    𝔔.ramificationIdx (𝓞 K) ≤ Module.finrank K F :=
  -- The fundamental identity `∑ eᵢ fᵢ = [F : K]` bounds each `eᵢ`, and `[𝓞 F : 𝓞 K] = [F : K]`.
  (TauCeti.RamificationInertia.ramificationIdx_le_finrank (𝔔.under (𝓞 K)) 𝔔).trans_eq
    (IsFractionRing.finrank_eq (𝓞 K) K (𝓞 F) F).symm

/-- **A totally ramified prime leaves no room for an intermediate field.** In a tower `K ≤ E ≤ B`
of number fields, if a prime of `𝓞 B` is already as ramified over `𝓞 E` as the whole degree
`[B : K]` allows, then `[E : K] = 1`.

The ramification index over `𝓞 E` is bounded by `[B : E]`, so `[B : K] ≤ [B : E]`; against
`[E : K] * [B : E] = [B : K]` that forces `[E : K] = 1`. -/
theorem finrank_eq_one_of_ramificationIdx_eq_finrank {E B : Type*} [Field E] [NumberField E]
    [Field B] [NumberField B] [Algebra K E] [Algebra K B] [Algebra E B] [IsScalarTower K E B]
    (𝔔 : Ideal (𝓞 B)) [𝔔.IsPrime] {n : ℕ}
    (he : 𝔔.ramificationIdx (𝓞 E) = n) (hB : Module.finrank K B = n) :
    Module.finrank K E = 1 := by
  have hb := Ideal.ramificationIdx_le_finrank_numberField (K := E) (F := B) 𝔔
  have hle : Module.finrank K E * Module.finrank E B ≤ 1 * Module.finrank E B := by
    rw [one_mul, Module.finrank_mul_finrank K E B, hB, ← he]; exact hb
  exact le_antisymm (Nat.le_of_mul_le_mul_right hle Module.finrank_pos) Module.finrank_pos

end TauCeti.NumberField
