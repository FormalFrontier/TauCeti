/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.SeparableDegree
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.GenericPoint

/-!
# The generic x-coordinate is a separating element

For an elliptic curve `E` over a field `F`, the function field `F(E)` is separable over the
subfield `F(genericX E)`. The Weierstrass relation is a monic quadratic equation for `genericY E`
over this subfield, and its derivative at `genericY E` is the value of `W_Y` at the generic point,
which `evalEval_polynomialY_genericX_genericY_ne_zero` shows to be nonzero.

Together with `transcendental_genericX`, this separability exhibits `genericX E` as a separating
element of `F(E)` over `F`, which is what proves the Kähler differentials of `F(E)` to have basis
`dx`, and hence basis the invariant differential.

## Main results

* `WeierstrassCurve.Affine.isSeparable_adjoin_genericX`: `F(E)` is separable over `F(genericX E)`.

## Provenance

The separating-element argument is adapted from `kaehler_rank_one` in the AINTLIB `HasseWeil`
project (Chris Birkbeck), Apache-2.0, `HasseWeil/FormalGroupCorrespondence.lean` at commit
`513e83879e2f`.
-/

public section

open Polynomial

open scoped IntermediateField

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] (E : WeierstrassCurve.Affine F)

/-- The function field is generated over `F(genericX)` by `genericY`. -/
private theorem adjoin_genericY_eq_top : (F⟮genericX E⟯)⟮genericY E⟯ = ⊤ := by
  have hadj : ∀ z ∈ Algebra.adjoin F ({genericX E, genericY E} : Set E.FunctionField),
      z ∈ (F⟮genericX E⟯)⟮genericY E⟯ := by
    intro z hz
    induction hz using Algebra.adjoin_induction with
    | mem u hu =>
      rcases hu with rfl | rfl
      · exact IntermediateField.algebraMap_mem _
          (⟨genericX E, IntermediateField.mem_adjoin_simple_self F _⟩ : F⟮genericX E⟯)
      · exact IntermediateField.mem_adjoin_simple_self _ _
    | algebraMap r =>
      exact IntermediateField.algebraMap_mem _ (algebraMap F F⟮genericX E⟯ r)
    | add a b _ _ ha hb => exact add_mem ha hb
    | mul a b _ _ ha hb => exact mul_mem ha hb
  rw [eq_top_iff]
  intro z _
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := E.CoordinateRing) z
  rw [← hab]
  exact div_mem (hadj _ (algebraMap_mem_adjoin_genericX_genericY E a))
    (hadj _ (algebraMap_mem_adjoin_genericX_genericY E b))

/-- The generic `y`-coordinate is separable over `F(genericX)`: it satisfies the monic
Weierstrass quadratic, whose derivative at `y` is `W_Y` evaluated at the generic point. -/
private theorem isSeparable_genericY [E.IsElliptic] :
    IsSeparable F⟮genericX E⟯ (genericY E) := by
  let x : F⟮genericX E⟯ :=
    ⟨genericX E, IntermediateField.mem_adjoin_simple_self F _⟩
  let b : F⟮genericX E⟯ := algebraMap F F⟮genericX E⟯ E.a₁ * x +
    algebraMap F F⟮genericX E⟯ E.a₃
  let c : F⟮genericX E⟯ := x ^ 3 + algebraMap F F⟮genericX E⟯ E.a₂ * x ^ 2 +
    algebraMap F F⟮genericX E⟯ E.a₄ * x + algebraMap F F⟮genericX E⟯ E.a₆
  let q : (F⟮genericX E⟯)[X] := X ^ 2 + C b * X - C c
  have hb : (b : E.FunctionField) =
      algebraMap F E.FunctionField E.a₁ * genericX E + algebraMap F E.FunctionField E.a₃ := by
    simp only [b, x, IntermediateField.coe_add, IntermediateField.coe_mul,
      IntermediateField.coe_algebraMap_apply]
  have hc : (c : E.FunctionField) =
      genericX E ^ 3 + algebraMap F E.FunctionField E.a₂ * genericX E ^ 2 +
        algebraMap F E.FunctionField E.a₄ * genericX E + algebraMap F E.FunctionField E.a₆ := by
    simp only [c, x, IntermediateField.coe_add, IntermediateField.coe_mul,
      IntermediateField.coe_pow, IntermediateField.coe_algebraMap_apply]
  have hq : aeval (genericY E) q = 0 := by
    have h := equation_genericX_genericY E
    rw [WeierstrassCurve.Affine.equation_iff] at h
    simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁,
      WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄,
      WeierstrassCurve.map_a₆] at h
    dsimp only [q]
    simp only [map_sub, map_add, map_mul, map_pow, aeval_X, aeval_C,
      IntermediateField.algebraMap_apply, hb, hc]
    rw [sub_eq_zero]
    convert h using 1
    all_goals ring
  have hmonic : q.Monic := by
    dsimp only [q]
    rw [sub_eq_add_neg, add_assoc]
    apply monic_X_pow_add
    compute_degree
    norm_num
  have hyint : IsIntegral F⟮genericX E⟯ (genericY E) := ⟨q, hmonic, hq⟩
  rw [IsSeparable, separable_iff_derivative_ne_zero (minpoly.irreducible hyint)]
  intro hder
  obtain ⟨r, hr⟩ := minpoly.dvd F⟮genericX E⟯ (genericY E) hq
  have htwo : ((2 : F⟮genericX E⟯) : E.FunctionField) = 2 := by
    rw [← IntermediateField.algebraMap_apply]
    exact map_ofNat (algebraMap F⟮genericX E⟯ E.FunctionField) 2
  have hqder : aeval (genericY E) q.derivative =
      2 * genericY E + algebraMap F E.FunctionField E.a₁ * genericX E +
        algebraMap F E.FunctionField E.a₃ := by
    dsimp only [q]
    rw [derivative_sub, derivative_add, derivative_pow, derivative_mul]
    simp only [derivative_X, derivative_C, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one,
      zero_mul, zero_add, sub_zero]
    simp only [map_add, map_mul, aeval_C, aeval_X, IntermediateField.algebraMap_apply, htwo, hb]
    ring
  have hz : aeval (genericY E) q.derivative = 0 := by
    rw [hr, derivative_mul, hder]
    simp
  exact evalEval_polynomialY_genericX_genericY_ne_zero E <| by
    rw [evalEval_polynomialY]
    simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁,
      WeierstrassCurve.map_a₃]
    exact hqder.symm.trans hz

/-- **The function field is separable over `F(genericX)`**, so that `genericX` is a separating
element of `F(E)/F`. Together with `transcendental_genericX`, this is the curve-specific input to
the general separating-element API for function fields. -/
instance isSeparable_adjoin_genericX [E.IsElliptic] :
    Algebra.IsSeparable F⟮genericX E⟯ E.FunctionField := by
  rw [← IntermediateField.isSeparable_top, ← adjoin_genericY_eq_top E]
  exact (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable _ _).2
    (isSeparable_genericY E)

end WeierstrassCurve.Affine

end
