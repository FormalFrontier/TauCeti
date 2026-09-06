/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.LinearAlgebra.Basis.SMul
public import Mathlib.RingTheory.Kaehler.Polynomial
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.GenericPoint
public import TauCeti.FieldTheory.FunctionField.Differential.Kaehler

/-!
# The invariant differential of an elliptic curve

For an elliptic curve `E` over a field `F` this file constructs the invariant differential
`ω = dx / (2y + a₁x + a₃)` inside the module of Kähler differentials `Ω[K(E)/F]` of the
function field, and proves that `ω` is a basis: `Ω[K(E)/F]` is a one-dimensional `K(E)`-vector
space, so every differential of `K(E)` is `c • ω` for a unique `c ∈ K(E)`.

The Weierstrass relation is a monic quadratic equation for `y` over `F(x)`. Its derivative at
`y` is `W_Y = 2y + a₁x + a₃`, which is nonzero — in characteristic two that is exactly where
`Δ ≠ 0` enters, since there `W_Y = a₁X + a₃`. Thus `x` is a separating element of `K(E)/F`.
The general separating-element API then says that `dx` is a basis of the Kähler differentials;
rescaling it by `W_Y⁻¹` gives the invariant-differential basis.

The file also records the **chain rule** obtained by differentiating the Weierstrass relation:
`W_X · dx + W_Y · dy = 0`, where the coefficients are the two partial derivatives of the
Weierstrass polynomial evaluated at the generic point.

## Main definitions

* `WeierstrassCurve.Affine.invariantDifferentialDenom`: the denominator `2y + a₁x + a₃`.
* `WeierstrassCurve.Affine.invariantDifferential`: the invariant differential `ω`, as an
  element of `Ω[K(E)/F]`.
* `WeierstrassCurve.Affine.invariantDifferentialBasis`: `ω` as a basis of `Ω[K(E)/F]`.

## Main results

* `WeierstrassCurve.Affine.polynomialX_smul_D_genericX_add_polynomialY_smul_D_genericY_eq_zero`:
  the chain rule `W_X · dx + W_Y · dy = 0`.
* `WeierstrassCurve.Affine.invariantDifferentialDenom_ne_zero`: the denominator is nonzero.
* `WeierstrassCurve.Affine.D_mem_span_D_genericX`,
  `WeierstrassCurve.Affine.span_D_genericX_eq_top`: `dx` spans `Ω[K(E)/F]`.
* `WeierstrassCurve.Affine.D_genericX_ne_zero`: `dx ≠ 0` in `Ω[K(E)/F]`.
* `WeierstrassCurve.Affine.finrank_kaehlerDifferential`: `Ω[K(E)/F]` is one-dimensional
  over `K(E)`.
* `WeierstrassCurve.Affine.existsUnique_smul_invariantDifferential`: every differential is
  `c • ω` for a unique `c`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.1 and III.5.

Silverman's III.1.5 says more than anything proved here: that `div ω = 0`, so that `ω` is
regular and nonvanishing at every point. This file proves that `ω` is a *basis* of
`Ω[K(E)/F]`, which does not imply that — a nonzero rational differential may have both zeros
and poles. The divisor statement needs regularity and nonvanishing formalised pointwise, and is
left to the later rungs of the roadmap's differential API.

## Provenance

Ported from the AINTLIB `HasseWeil` project (Chris Birkbeck), Apache-2.0, at commit
`513e83879e2f`: `HasseWeil/InvariantDifferential.lean` (`D_x_ne_zero`, `denom_ne_zero`,
`invariantDifferential` and `invariantDifferential_ne_zero`) and
`HasseWeil/FormalGroupCorrespondence.lean` (`kaehler_rank_one`, the one-dimensionality, proved
there by the same span-of-`dx` argument).

The proofs are reorganised here, and the reorganisation is what removes the source's two
overrides: `D_x_ne_zero` carried a `maxHeartbeats` override and `kaehler_rank_one` carried a
larger one, while no declaration here needs any. The source's `[DecidableEq F]` hypothesis is
also dropped. Its direct span-of-`dx` proof is replaced by the general separating-element API in
`TauCeti.FieldTheory.FunctionField.Differential.Kaehler`; the curve-specific input here is that
the Weierstrass quadratic has nonzero derivative `W_Y` at `y`. The Weierstrass relation itself,
which the source re-derives inside `AdjoinRoot`, is the existing `equation_genericX_genericY`.
The chain rule, the spanning statement, the basis and the uniqueness statement are stated here
and are not in the source, which proves only `Module.finrank = 1`.

Sources swept for the same material and not carrying it:
`github.com/MichaelStollBayreuth/EllipticCurves` @ `449c7b936813` and
`github.com/ImperialCollegeLondon/FLT`, whose only mentions of `KaehlerDifferential` are in
Henselian-local-ring files; and pinned Mathlib, which computes `Module.rank Ω[S⁄R]` only for
standard smooth presentations (`RingTheory/Smooth/StandardSmoothCotangent.lean`), a hypothesis
not available here.
-/

public section

open Polynomial Polynomial.Bivariate

open scoped IntermediateField

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] (E : WeierstrassCurve.Affine F)

/-! ### The denominator `2y + a₁x + a₃` -/

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

/-- The denominator `2y + a₁x + a₃` of the invariant differential, as an element of `K(E)`. It
is the value at the generic point of the partial derivative `W_Y = polynomialY`, which is
`invariantDifferentialDenom_eq_evalEval_polynomialY`;
`invariantDifferentialDenom_ne_zero` shows it is nonzero when `E` is elliptic. The converse
fails: `y² = x³` over `ℚ` is singular, yet its `W_Y = 2y` is nonzero. -/
noncomputable def invariantDifferentialDenom : E.FunctionField :=
  2 * genericY E + algebraMap F E.FunctionField E.a₁ * genericX E +
    algebraMap F E.FunctionField E.a₃

/-- The defining formula for `invariantDifferentialDenom`. The definition body is not exposed, so
this equation lemma is how a consumer in another module computes with it. That is also why the
proof is the parenthesised `(rfl)`: a bare `rfl` is rejected for a theorem exported from this
module, exactly as for `invar_def` and `ψc_def` in `DivisionPolynomial/`. -/
theorem invariantDifferentialDenom_def :
    invariantDifferentialDenom E =
      2 * genericY E + algebraMap F E.FunctionField E.a₁ * genericX E +
        algebraMap F E.FunctionField E.a₃ :=
  (rfl)

/-- **The denominator is `W_Y` at the generic point.** This is the reading that makes it the
denominator of `ω = dx / W_Y`, and it is the form the chain rule below produces. -/
theorem invariantDifferentialDenom_eq_evalEval_polynomialY :
    invariantDifferentialDenom E =
      (E⁄E.FunctionField).toAffine.polynomialY.evalEval (genericX E) (genericY E) := by
  rw [evalEval_polynomialY]
  simp only [invariantDifferentialDenom_def, WeierstrassCurve.baseChange,
    WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃]

/-- The denominator, read as the image of the coordinate-ring class of `W_Y`. Kept private: it
is one rewrite of `invariantDifferentialDenom_eq_evalEval_polynomialY` by
`evalEval_genericX_genericY`, and only the nonvanishing proof below wants that form. -/
private lemma invariantDifferentialDenom_eq_algebraMap_mk :
    invariantDifferentialDenom E = algebraMap E.CoordinateRing E.FunctionField
      (WeierstrassCurve.Affine.CoordinateRing.mk E E.polynomialY) := by
  have h := evalEval_genericX_genericY E E.polynomialY
  rw [← WeierstrassCurve.Affine.map_polynomialY] at h
  rw [invariantDifferentialDenom_eq_evalEval_polynomialY]
  exact h

/-- **The denominator of the invariant differential is nonzero.** It is the image of `W_Y` in
`K(E)`, and `W_Y` is a nonzero polynomial of degree below `deg W`, so it survives both
`F[X][Y] → F[E]` and `F[E] → K(E)`. -/
@[simp]
theorem invariantDifferentialDenom_ne_zero [E.IsElliptic] :
    invariantDifferentialDenom E ≠ 0 := by
  rw [invariantDifferentialDenom_eq_algebraMap_mk]
  exact fun h => mk_polynomialY_ne_zero E
    ((IsFractionRing.injective E.CoordinateRing E.FunctionField).eq_iff.mp
      (h.trans (map_zero _).symm))

/-! ### The chain rule -/

/-- The differential of the quadratic side `y² + a₁xy + a₃y` of the Weierstrass relation. -/
private lemma D_quadratic_side :
    KaehlerDifferential.D F E.FunctionField
        (genericY E ^ 2 + algebraMap F E.FunctionField E.a₁ * genericX E * genericY E +
          algebraMap F E.FunctionField E.a₃ * genericY E) =
      (2 * genericY E + algebraMap F E.FunctionField E.a₁ * genericX E +
          algebraMap F E.FunctionField E.a₃) •
          KaehlerDifferential.D F E.FunctionField (genericY E) +
        (algebraMap F E.FunctionField E.a₁ * genericY E) •
          KaehlerDifferential.D F E.FunctionField (genericX E) := by
  simp only [map_add, Derivation.leibniz, Derivation.leibniz_pow, Derivation.map_algebraMap,
    smul_zero, add_zero, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, smul_smul,
    ← Nat.cast_smul_eq_nsmul E.FunctionField]
  rw [mul_comm (genericY E) (algebraMap F E.FunctionField E.a₁), add_smul, add_smul]
  abel

/-- The differential of the cubic side `x³ + a₂x² + a₄x + a₆` of the Weierstrass relation. -/
private lemma D_cubic_side :
    KaehlerDifferential.D F E.FunctionField
        (genericX E ^ 3 + algebraMap F E.FunctionField E.a₂ * genericX E ^ 2 +
          algebraMap F E.FunctionField E.a₄ * genericX E + algebraMap F E.FunctionField E.a₆) =
      (3 * genericX E ^ 2 + 2 * algebraMap F E.FunctionField E.a₂ * genericX E +
          algebraMap F E.FunctionField E.a₄) •
        KaehlerDifferential.D F E.FunctionField (genericX E) := by
  simp only [map_add, Derivation.leibniz, Derivation.leibniz_pow, Derivation.map_algebraMap,
    smul_zero, add_zero, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, smul_smul,
    ← Nat.cast_smul_eq_nsmul E.FunctionField]
  rw [← add_smul, ← add_smul]
  congr 1
  ring

/-- **The chain rule for the Weierstrass relation**: `W_X · dx + W_Y · dy = 0` in `Ω[K(E)/F]`,
the two coefficients being the partial derivatives of the Weierstrass polynomial evaluated at
the generic point. It holds for every Weierstrass curve, singular ones included: it is the
differential of the relation `equation_genericX_genericY`, which needs no hypothesis.

Ellipticity enters only afterwards, through `invariantDifferentialDenom_ne_zero`, which is what
lets the identity be solved for `dy`. -/
theorem polynomialX_smul_D_genericX_add_polynomialY_smul_D_genericY_eq_zero :
    (E⁄E.FunctionField).toAffine.polynomialX.evalEval (genericX E) (genericY E) •
        KaehlerDifferential.D F E.FunctionField (genericX E) +
      (E⁄E.FunctionField).toAffine.polynomialY.evalEval (genericX E) (genericY E) •
        KaehlerDifferential.D F E.FunctionField (genericY E) = 0 := by
  have h := equation_genericX_genericY E
  rw [WeierstrassCurve.Affine.equation_iff] at h
  rw [evalEval_polynomialX, evalEval_polynomialY]
  simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] at h ⊢
  have key := congrArg (KaehlerDifferential.D F E.FunctionField) h
  rw [D_quadratic_side, D_cubic_side] at key
  rw [sub_smul, ← key]
  abel

/-! ### `genericX` is a separating element -/

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
Weierstrass quadratic, whose derivative at `y` is the nonzero invariant-differential
denominator. -/
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
    change algebraMap F⟮genericX E⟯ E.FunctionField
      (algebraMap F F⟮genericX E⟯ E.a₁ * x + algebraMap F F⟮genericX E⟯ E.a₃) = _
    rw [map_add, map_mul, IsScalarTower.algebraMap_apply F F⟮genericX E⟯ E.FunctionField]
    rfl
  have hc : (c : E.FunctionField) =
      genericX E ^ 3 + algebraMap F E.FunctionField E.a₂ * genericX E ^ 2 +
        algebraMap F E.FunctionField E.a₄ * genericX E + algebraMap F E.FunctionField E.a₆ := by
    change algebraMap F⟮genericX E⟯ E.FunctionField
      (x ^ 3 + algebraMap F F⟮genericX E⟯ E.a₂ * x ^ 2 +
        algebraMap F F⟮genericX E⟯ E.a₄ * x + algebraMap F F⟮genericX E⟯ E.a₆) = _
    rw [map_add, map_add, map_add, map_mul, map_mul, map_pow, map_pow,
      IsScalarTower.algebraMap_apply F F⟮genericX E⟯ E.FunctionField]
    rfl
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
  exact invariantDifferentialDenom_ne_zero E
    ((invariantDifferentialDenom_def E).trans (hqder.symm.trans hz))

/-- The function field is separable over `F(genericX)`. -/
private instance isSeparable_adjoin_genericX [E.IsElliptic] :
    Algebra.IsSeparable F⟮genericX E⟯ E.FunctionField := by
  rw [← IntermediateField.isSeparable_top, ← adjoin_genericY_eq_top E]
  exact (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable _ _).2
    (isSeparable_genericY E)

/-! ### The differentials of the function field are spanned by `dx` -/

/-- **Every differential of `K(E)` is a multiple of `dx`.** The generic coordinate `x` is a
separating element, so this is the general separating-element spanning theorem. -/
theorem D_mem_span_D_genericX [E.IsElliptic] (s : E.FunctionField) :
    KaehlerDifferential.D F E.FunctionField s ∈
      Submodule.span E.FunctionField
        {KaehlerDifferential.D F E.FunctionField (genericX E)} := by
  rw [TauCeti.span_D_eq_top_of_separating (transcendental_genericX E)]
  trivial

/-- **`dx` spans `Ω[K(E)/F]`.** -/
theorem span_D_genericX_eq_top [E.IsElliptic] :
    Submodule.span E.FunctionField
      {KaehlerDifferential.D F E.FunctionField (genericX E)} = ⊤ := by
  exact TauCeti.span_D_eq_top_of_separating (transcendental_genericX E)

/-- **The differential of `x` is nonzero.** This is the nonvanishing theorem for the separating
element `genericX`. -/
@[simp]
theorem D_genericX_ne_zero [E.IsElliptic] :
    KaehlerDifferential.D F E.FunctionField (genericX E) ≠ 0 := by
  exact TauCeti.D_ne_zero_of_separating (transcendental_genericX E)

/-- **`Ω[K(E)/F]` is a one-dimensional `K(E)`-vector space**, spanned by the nonzero
element `dx` (Silverman III.1.5 for the sharper divisor statement). -/
theorem finrank_kaehlerDifferential [E.IsElliptic] :
    Module.finrank E.FunctionField (KaehlerDifferential F E.FunctionField) = 1 := by
  exact TauCeti.finrank_kaehlerDifferential_eq_one_of_separating (transcendental_genericX E)

/-! ### The invariant differential -/

/-- The invariant differential `ω = dx / (2y + a₁x + a₃)`, as an element of `Ω[K(E)/F]`. -/
noncomputable def invariantDifferential :
    KaehlerDifferential F E.FunctionField :=
  (invariantDifferentialDenom E)⁻¹ • KaehlerDifferential.D F E.FunctionField (genericX E)

/-- The defining formula for `invariantDifferential`. The definition body is not exposed, so this
equation lemma is how a consumer in another module computes with it. Not `@[simp]`: the point of
naming `invariantDifferentialDenom` is that the nonvanishing results can be stated over it, which
unfolding everywhere would defeat. -/
theorem invariantDifferential_def :
    invariantDifferential E =
      (invariantDifferentialDenom E)⁻¹ •
        KaehlerDifferential.D F E.FunctionField (genericX E) :=
  (rfl)

/-- **The invariant differential is nonzero** as an element of `Ω[K(E)/F]`. It is the product of
an inverse of the nonzero denominator with `dx`, both nonzero. -/
@[simp]
theorem invariantDifferential_ne_zero [E.IsElliptic] : invariantDifferential E ≠ 0 := by
  rw [invariantDifferential_def]
  exact smul_ne_zero (inv_ne_zero (invariantDifferentialDenom_ne_zero E)) (D_genericX_ne_zero E)

/-- **The invariant differential spans `Ω[K(E)/F]`**: it differs from `dx` by an invertible
scalar. -/
theorem span_invariantDifferential_eq_top [E.IsElliptic] :
    Submodule.span E.FunctionField {invariantDifferential E} = ⊤ := by
  rw [invariantDifferential_def,
    Submodule.span_singleton_smul_eq
      (IsUnit.mk0 _ (inv_ne_zero (invariantDifferentialDenom_ne_zero E))),
    span_D_genericX_eq_top E]

/-- **`ω` is a basis of `Ω[K(E)/F]`**, the module being one-dimensional and `ω` nonzero. -/
noncomputable def invariantDifferentialBasis [E.IsElliptic] :
    Module.Basis Unit E.FunctionField (KaehlerDifferential F E.FunctionField) :=
  (TauCeti.kaehlerBasisOfSeparating (transcendental_genericX E)).unitsSMul
    (fun _ => Units.mk0 (invariantDifferentialDenom E)⁻¹
      (inv_ne_zero (invariantDifferentialDenom_ne_zero E)))

@[simp]
theorem invariantDifferentialBasis_apply [E.IsElliptic] (i : Unit) :
    invariantDifferentialBasis E i = invariantDifferential E :=
  by
    rw [invariantDifferentialBasis, Module.Basis.unitsSMul_apply,
      TauCeti.kaehlerBasisOfSeparating_apply, Units.smul_def]
    exact (invariantDifferential_def E).symm

/-- **Every differential of `K(E)` is `c • ω` for a unique `c ∈ K(E)`.** This is the form the
differential calculus of isogenies consumes: the pullback coefficient of an isogeny `φ` is the
scalar attached to `φ^*ω` by this statement. -/
theorem existsUnique_smul_invariantDifferential [E.IsElliptic]
    (η : KaehlerDifferential F E.FunctionField) :
    ∃! c : E.FunctionField, c • invariantDifferential E = η := by
  have hmem : η ∈ Submodule.span E.FunctionField {invariantDifferential E} := by
    rw [span_invariantDifferential_eq_top E]; trivial
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  refine ⟨c, hc, fun c' hc' => ?_⟩
  have h := hc'.trans hc.symm
  rw [← sub_eq_zero, ← sub_smul] at h
  rcases smul_eq_zero.mp h with h' | h'
  · exact sub_eq_zero.mp h'
  · exact absurd h' (invariantDifferential_ne_zero E)

end WeierstrassCurve.Affine
