/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.NumberTheory.NumberField.Basic
import TauCeti.NumberTheory.NumberField.IntegralSqrt
import Mathlib.FieldTheory.KummerPolynomial

/-!
# The `AdjoinRoot (X² + 5)` model of `ℚ(√-5)`

The concrete number field `AdjoinRoot (X² + 5)` serving as the canonical model of `ℚ(√-5)`, together
with its integral generator. This presentation datum is foundational: it is shared by both the
class-number and the `2`-rank worked examples for this field, so it lives here rather than in either
of them.

## Main results

* `TauCeti.NumberField.exists_minpoly_eq_X_sq_add_five_and_adjoin_eq_top`: the model has an
  integral generator with minimal polynomial `X² + 5` generating the field over `ℚ`.
-/

public section

open NumberField Polynomial
open scoped NumberField

namespace TauCeti.NumberField

/-- `X² + 5` is irreducible over `ℚ`, so `AdjoinRoot (X² + 5)` is a field. The instance carries an
explicit, field-specific name because an anonymous `Fact (Irreducible …)` instance receives an
auto-generated name that ignores the radicand, so the analogous instances for different radicands
would collide under one name when the whole library is loaded for the axioms audit. -/
instance irreducible_X_sq_add_five : Fact (Irreducible (X ^ 2 - C (-5 : ℚ))) := ⟨by
  exact (X_pow_sub_C_irreducible_iff_of_prime Nat.prime_two).mpr
    (fun q _ => by nlinarith [sq_nonneg q])⟩

/-- The concrete model `AdjoinRoot (X² + 5)` of `ℚ(√-5)` carries an integral generator with minimal
polynomial `X² + 5` generating the field over `ℚ`: the presentation data shared by the class-number
and `2`-rank worked examples for this field. -/
theorem exists_minpoly_eq_X_sq_add_five_and_adjoin_eq_top :
    ∃ θ : 𝓞 (AdjoinRoot (X ^ 2 - C (-5 : ℚ))),
      minpoly ℤ θ = X ^ 2 - C (-5 : ℤ) ∧
        Algebra.adjoin ℚ {(θ : AdjoinRoot (X ^ 2 - C (-5 : ℚ)))} = ⊤ := by
  let K := AdjoinRoot (X ^ 2 - C (-5 : ℚ))
  let x : K := AdjoinRoot.root (X ^ 2 - C (-5 : ℚ))
  have hx : x ^ 2 = algebraMap ℤ K (-5 : ℤ) := by
    have hroot := AdjoinRoot.eval₂_root (X ^ 2 - C (-5 : ℚ))
    rw [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, ← AdjoinRoot.algebraMap_eq, sub_eq_zero] at hroot
    rw [hroot, IsScalarTower.algebraMap_apply ℤ ℚ K]
    norm_num
  refine ⟨integralSqrt hx, minpoly_integralSqrt hx (fun ⟨q, hq⟩ => by
      norm_num at hq
      nlinarith [mul_self_nonneg q]), ?_⟩
  have hθx : ((integralSqrt hx : 𝓞 K) : K) = x := algebraMap_integralSqrt hx
  rw [hθx]
  exact AdjoinRoot.adjoinRoot_eq_top

end TauCeti.NumberField
