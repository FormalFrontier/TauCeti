/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdjoinRoot
public import TauCeti.NumberTheory.NumberField.IntegralSqrt
import Mathlib.FieldTheory.KummerPolynomial

/-!
# The `AdjoinRoot (X² + 21)` model of `ℚ(√-21)`

The concrete number field `AdjoinRoot (X² + 21)` serving as the canonical model of `ℚ(√-21)`,
together with its integral generator. This presentation datum is foundational: it is shared by both
the class-number and the `2`-rank worked examples for this field, so it lives here rather than in
either of them.

## Main results

* `TauCeti.NumberField.exists_isIntegralGen_adjoinRoot_sqrt_neg_twenty_one`: the model carries an
  integral generator whose minimal polynomial is `X² + 21` and which generates the field over `ℚ`.
-/

public section

open NumberField Polynomial
open scoped NumberField

namespace TauCeti.NumberField

/-- `X² + 21` is irreducible over `ℚ`, so `AdjoinRoot (X² + 21)` is a field. Exported (rather than
declared `local` in each consumer) with an explicit, field-specific name: an anonymous instance
would receive an auto-generated name that ignores the radicand, colliding with the sibling
`ℚ(√-N)` files' instances when they are imported together. -/
instance irreducible_sqrt_neg_twenty_one : Fact (Irreducible (X ^ 2 - C (-21 : ℚ))) := ⟨by
  exact (X_pow_sub_C_irreducible_iff_of_prime Nat.prime_two).mpr
    (fun q _ => by nlinarith [sq_nonneg q])⟩

/-- The concrete model `AdjoinRoot (X² + 21)` of `ℚ(√-21)` carries an integral generator with
minimal polynomial `X² + 21` generating the field over `ℚ`: the presentation data shared by the
class-number and `2`-rank worked examples for this field. -/
theorem exists_isIntegralGen_adjoinRoot_sqrt_neg_twenty_one :
    ∃ θ : 𝓞 (AdjoinRoot (X ^ 2 - C (-21 : ℚ))),
      minpoly ℤ θ = X ^ 2 - C (-21 : ℤ) ∧
        Algebra.adjoin ℚ {(θ : AdjoinRoot (X ^ 2 - C (-21 : ℚ)))} = ⊤ := by
  let K := AdjoinRoot (X ^ 2 - C (-21 : ℚ))
  let x : K := AdjoinRoot.root (X ^ 2 - C (-21 : ℚ))
  have hx : x ^ 2 = algebraMap ℤ K (-21 : ℤ) := by
    have hroot := AdjoinRoot.eval₂_root (X ^ 2 - C (-21 : ℚ))
    rw [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, ← AdjoinRoot.algebraMap_eq, sub_eq_zero] at hroot
    rw [hroot, IsScalarTower.algebraMap_apply ℤ ℚ K]
    norm_num
  refine ⟨integralSqrt hx, minpoly_integralSqrt hx (fun ⟨q, hq⟩ => by
      norm_num at hq
      nlinarith [mul_self_nonneg q]), ?_⟩
  have hfne : (X ^ 2 - C (-21 : ℚ)) ≠ 0 :=
    (monic_X_pow_sub_C (-21 : ℚ) (by norm_num)).ne_zero
  have hpb := (AdjoinRoot.powerBasis (f := X ^ 2 - C (-21 : ℚ)) hfne).adjoin_gen_eq_top
  rw [AdjoinRoot.powerBasis_gen] at hpb
  have hθx : ((integralSqrt hx : 𝓞 K) : K) = x := algebraMap_integralSqrt hx
  rw [hθx]
  exact hpb

end TauCeti.NumberField
