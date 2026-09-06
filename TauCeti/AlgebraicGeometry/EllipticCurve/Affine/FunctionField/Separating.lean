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
over this subfield, and its derivative at `genericY E` is the nonzero value of `W_Y` at the
generic point.

Together with `transcendental_genericX`, this separability exhibits `genericX E` as a separating
element of `F(E)` over `F`, which is what proves the Kähler differentials of `F(E)` to have basis
`dx`, and hence basis the invariant differential.

## Main results

* `WeierstrassCurve.Affine.evalEval_polynomialY_genericX_genericY_ne_zero`: `W_Y` is nonzero at
  the generic point of an elliptic curve.
* `WeierstrassCurve.Affine.isSeparable_adjoin_genericX`: `F(E)` is separable over `F(genericX E)`.

## Provenance

The separating-element argument is adapted from `kaehler_rank_one` in the AINTLIB `HasseWeil`
project (Chris Birkbeck), Apache-2.0, `HasseWeil/FormalGroupCorrespondence.lean` at commit
`513e83879e2f`.
-/

public section

open Polynomial Polynomial.Bivariate

open scoped IntermediateField

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] (E : WeierstrassCurve.Affine F)

/-- The partial derivative `W_Y = 2Y + a₁X + a₃` of the Weierstrass polynomial is a nonzero
polynomial when `E` is elliptic. In characteristic two the first term vanishes, and it is `Δ ≠ 0`
that rules out `a₁ = a₃ = 0`. -/
private lemma polynomialY_ne_zero [E.IsElliptic] : E.polynomialY ≠ 0 := by
  intro h
  rw [WeierstrassCurve.Affine.polynomialY] at h
  have h1 := congr_arg (fun p => p.coeff 1) h
  have h0 := congr_arg (fun p => p.coeff 0) h
  simp only [map_add, map_mul, coeff_add, coeff_mul_X, coeff_C, ↓reduceIte, coeff_mul_C,
    zero_mul, add_zero, coeff_zero, map_eq_zero, mul_coeff_zero, coeff_X, one_ne_zero,
    mul_zero, zero_add] at h1 h0
  have ha1 : E.a₁ = 0 := by
    have := congr_arg (fun p => p.coeff 1) h0
    simp only [coeff_add, coeff_mul_X, coeff_C_zero, coeff_C_succ, add_zero, coeff_zero] at this
    exact this
  have ha3 : E.a₃ = 0 := by
    have := congr_arg (fun p => p.coeff 0) h0
    simp only [coeff_add, mul_coeff_zero, coeff_C_zero, coeff_X_zero, mul_zero, zero_add,
      coeff_zero] at this
    exact this
  have hb₂ : WeierstrassCurve.b₂ E = 0 := by
    simp only [WeierstrassCurve.b₂, ha1]; linear_combination 2 * E.a₂ * h1
  have hb₄ : WeierstrassCurve.b₄ E = 0 := by
    simp only [WeierstrassCurve.b₄, ha1, ha3]; linear_combination E.a₄ * h1
  have hb₆ : WeierstrassCurve.b₆ E = 0 := by
    simp only [WeierstrassCurve.b₆, ha3]; linear_combination 2 * E.a₆ * h1
  have hΔ : WeierstrassCurve.Δ E = 0 := by
    simp only [WeierstrassCurve.Δ]; rw [hb₂, hb₄, hb₆]; ring
  exact absurd (hΔ ▸ E.isUnit_Δ) not_isUnit_zero

/-- `W_Y` stays nonzero in the coordinate ring: its degree is below `deg W`, so it is not a
multiple of `W`. -/
private lemma mk_polynomialY_ne_zero [E.IsElliptic] :
    WeierstrassCurve.Affine.CoordinateRing.mk E E.polynomialY ≠ 0 :=
  AdjoinRoot.mk_ne_zero_of_natDegree_lt monic_polynomial (polynomialY_ne_zero E) <| by
    rw [natDegree_polynomial, WeierstrassCurve.Affine.polynomialY]
    have : (Polynomial.C (Polynomial.C (2 : F)) * (Y : F[X][Y])).natDegree ≤ 1 :=
      Polynomial.natDegree_mul_le.trans
        (by simp [Polynomial.natDegree_C, Polynomial.natDegree_X])
    exact Nat.lt_of_le_of_lt (Polynomial.natDegree_add_le _ _)
      (by rw [Polynomial.natDegree_C]; omega)

/-- **The partial derivative `W_Y` is nonzero at the generic point** of an elliptic curve. -/
@[simp]
theorem evalEval_polynomialY_genericX_genericY_ne_zero [E.IsElliptic] :
    (E⁄E.FunctionField).toAffine.polynomialY.evalEval (genericX E) (genericY E) ≠ 0 := by
  have h := evalEval_genericX_genericY E E.polynomialY
  rw [← WeierstrassCurve.Affine.map_polynomialY] at h
  have h' :
      (E⁄E.FunctionField).toAffine.polynomialY.evalEval (genericX E) (genericY E) =
        algebraMap E.CoordinateRing E.FunctionField (CoordinateRing.mk E E.polynomialY) := by
    simpa only [WeierstrassCurve.baseChange] using h
  rw [h']
  exact fun hz => mk_polynomialY_ne_zero E
    ((IsFractionRing.injective E.CoordinateRing E.FunctionField).eq_iff.mp
      (hz.trans (map_zero _).symm))

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
