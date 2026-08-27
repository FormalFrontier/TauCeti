/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.RingTheory.Kaehler.Polynomial
public import Mathlib.RingTheory.Unramified.Field

/-!
# The invariant differential of an elliptic curve

For an elliptic curve `E` over a field `F` this file constructs the invariant differential
`ω = dx / (2y + a₁x + a₃)` inside the module of Kähler differentials `Ω[K(E)/F]` of the
function field, and proves that it is nonzero.

The denominator is the image in `K(E)` of `polynomialY = W_Y`, the partial derivative of the
Weierstrass polynomial with respect to `Y`. It is nonzero for two separate reasons, and the
file proves both: `W_Y` is a nonzero *polynomial* — in characteristic two that is exactly where
`Δ ≠ 0` enters, since there `W_Y = a₁X + a₃` — and it has degree below `deg W`, so it
survives the passage to `F[E]` and then to `K(E)`.

That `D x ≠ 0` is the substantial half. The argument is by contradiction and is
characteristic-free: if `D x = 0` then `D` kills every polynomial in `x`, and differentiating
the Weierstrass relation `y² + (a₁x + a₃) y = x³ + a₂x² + a₄x + a₆` leaves
`(2y + a₁x + a₃) · D y = 0`. The denominator is invertible in the field `K(E)`, so `D y = 0` as
well; since `F[E]` is spanned by `1` and `y` over `F[x]` and `K(E)` is its fraction field, `D`
then vanishes identically. A vanishing differential module says `K(E)/F` is formally unramified,
hence separable algebraic, which contradicts `x` being transcendental over `F`.

## Main definitions

* `WeierstrassCurve.Affine.invariantDifferentialDenom`: the denominator `2y + a₁x + a₃`.
* `WeierstrassCurve.Affine.invariantDifferential`: the invariant differential `ω`, as an
  element of `Ω[K(E)/F]`.

## Main results

* `WeierstrassCurve.Affine.invariantDifferentialDenom_def`,
  `WeierstrassCurve.Affine.invariantDifferential_def`: the two defining formulas.
* `WeierstrassCurve.Affine.invariantDifferentialDenom_ne_zero`: the denominator is nonzero.
* `WeierstrassCurve.Affine.D_X_ne_zero`: `D x ≠ 0` in `Ω[K(E)/F]`.
* `WeierstrassCurve.Affine.invariantDifferential_ne_zero`: `ω ≠ 0` in `Ω[K(E)/F]`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.1 and III.5.

Silverman's III.1.5 says more than anything proved here: that `div ω = 0`, so that `ω` is
regular and nonvanishing at every point. This file proves only that `ω` is a nonzero element of
`Ω[K(E)/F]`, which does not imply that — a nonzero rational differential may have both zeros and
poles. The divisor statement needs regularity and nonvanishing formalised pointwise, and is left
to the later rungs of the roadmap's differential API.

## Provenance

Ported from the AINTLIB `HasseWeil` project (Chris Birkbeck), Apache-2.0, file
`projects/HasseWeil/HasseWeil/InvariantDifferential.lean` at commit
`513e83879e2f`: `D_x_ne_zero`, `denom_ne_zero`, `invariantDifferential` and
`invariantDifferential_ne_zero`. The proofs are reorganised here: the source carried a
`maxHeartbeats` override on a single monolithic `D_x_ne_zero`, whose nested steps are separate
private lemmas below, and no declaration here needs a heartbeat override. Two arguments the
source repeated are proved once: the denominator argument, which it gave both as
`denom_ne_zero` and inline inside `D_x_ne_zero`, is `algebraMap_mk_polynomialY` together with
`two_mul_root_add_ne_zero`; and its `aeval` helper, likewise duplicated inline, is
`aeval_algebraMap_X`. The source's `[DecidableEq F]` hypothesis is dropped: nothing here uses
it, so it is not carried on the public statements.
-/

public section

open Polynomial Polynomial.Bivariate

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

/-- The image of `W_Y` in the function field, written out as `2y + (a₁x + a₃)`. Both
`denom_ne_zero` and the differentiation step inside `D_X_ne_zero` need this identification; the
source proved it twice. -/
private lemma algebraMap_mk_polynomialY :
    algebraMap E.CoordinateRing E.FunctionField
        (WeierstrassCurve.Affine.CoordinateRing.mk E E.polynomialY) =
      2 * algebraMap E.CoordinateRing E.FunctionField (AdjoinRoot.root E.polynomial) +
        algebraMap (Polynomial F) E.FunctionField
          (Polynomial.C E.a₁ * Polynomial.X + Polynomial.C E.a₃) := by
  have hmk : (WeierstrassCurve.Affine.CoordinateRing.mk E E.polynomialY :
        E.CoordinateRing) =
      algebraMap (Polynomial F) E.CoordinateRing (Polynomial.C 2) * AdjoinRoot.root E.polynomial +
        algebraMap (Polynomial F) E.CoordinateRing
          (Polynomial.C E.a₁ * Polynomial.X + Polynomial.C E.a₃) := by
    -- `CoordinateRing.mk` is *definitionally* `AdjoinRoot.mk`, and Mathlib exposes no rewrite
    -- lemma unfolding it, so `change` is the only way in. The equality is stable because
    -- `CoordinateRing.mk` is introduced as that quotient map and has no other definition.
    change AdjoinRoot.mk E.polynomial E.polynomialY = _
    rw [WeierstrassCurve.Affine.polynomialY, map_add, map_mul, AdjoinRoot.mk_X]
    rfl
  rw [hmk, map_add, map_mul,
    ← IsScalarTower.algebraMap_apply (Polynomial F) E.CoordinateRing E.FunctionField,
    ← IsScalarTower.algebraMap_apply (Polynomial F) E.CoordinateRing E.FunctionField]
  congr 1
  congr 1
  rw [Polynomial.C_eq_algebraMap,
    ← IsScalarTower.algebraMap_apply F (Polynomial F) E.FunctionField, map_ofNat]

/-- The denominator, in the `F[X]`-form the differentiation step produces. -/
private lemma two_mul_root_add_ne_zero [E.IsElliptic] :
    2 * algebraMap E.CoordinateRing E.FunctionField (AdjoinRoot.root E.polynomial) +
      algebraMap (Polynomial F) E.FunctionField
        (Polynomial.C E.a₁ * Polynomial.X + Polynomial.C E.a₃) ≠ 0 := by
  rw [← algebraMap_mk_polynomialY]
  intro h
  exact mk_polynomialY_ne_zero E
    ((IsFractionRing.injective E.CoordinateRing E.FunctionField).eq_iff.mp
      (h.trans (map_zero _).symm))

/-- `a₁x + a₃` in the function field is the image of the polynomial `a₁X + a₃`. -/
private lemma algebraMap_a₁_mul_X_add_a₃ :
    algebraMap F E.FunctionField E.a₁ *
        algebraMap E.CoordinateRing E.FunctionField
          (algebraMap (Polynomial F) E.CoordinateRing Polynomial.X) +
      algebraMap F E.FunctionField E.a₃ =
      algebraMap (Polynomial F) E.FunctionField
        (Polynomial.C E.a₁ * Polynomial.X + Polynomial.C E.a₃) := by
  rw [map_add, map_mul, Polynomial.C_eq_algebraMap, Polynomial.C_eq_algebraMap,
    ← IsScalarTower.algebraMap_apply F (Polynomial F) E.FunctionField,
    ← IsScalarTower.algebraMap_apply F (Polynomial F) E.FunctionField,
    IsScalarTower.algebraMap_apply (Polynomial F) E.CoordinateRing E.FunctionField]

/-- The denominator `2y + a₁x + a₃` of the invariant differential, as an element of `K(E)`. It
is the image of the partial derivative `W_Y = polynomialY`; `algebraMap_mk_polynomialY` is that
identification, and `invariantDifferentialDenom_ne_zero` shows it is nonzero when `E` is
elliptic. The converse fails: `y² = x³` over `ℚ` is singular, yet its `W_Y = 2y` is nonzero. -/
noncomputable def invariantDifferentialDenom : E.FunctionField :=
  2 * algebraMap E.CoordinateRing E.FunctionField (AdjoinRoot.root E.polynomial) +
    algebraMap F E.FunctionField E.a₁ *
      algebraMap E.CoordinateRing E.FunctionField
        (algebraMap (Polynomial F) E.CoordinateRing Polynomial.X) +
    algebraMap F E.FunctionField E.a₃

/-- The defining formula for `invariantDifferentialDenom`. The definition body is not exposed, so
this equation lemma is how a consumer in another module computes with it. That is also why the
proof is the parenthesised `(rfl)`: a bare `rfl` is rejected for a theorem exported from this
module, exactly as for `invar_def` and `ψc_def` in `DivisionPolynomial/`. -/
theorem invariantDifferentialDenom_def :
    invariantDifferentialDenom E =
      2 * algebraMap E.CoordinateRing E.FunctionField (AdjoinRoot.root E.polynomial) +
        algebraMap F E.FunctionField E.a₁ *
          algebraMap E.CoordinateRing E.FunctionField
            (algebraMap (Polynomial F) E.CoordinateRing Polynomial.X) +
        algebraMap F E.FunctionField E.a₃ :=
  (rfl)

/-- **The denominator of the invariant differential is nonzero.** It is the image of `W_Y` in
`K(E)`, and `W_Y` is a nonzero polynomial of degree below `deg W`, so it survives both
`F[X][Y] → F[E]` and `F[E] → K(E)`. -/
@[simp]
theorem invariantDifferentialDenom_ne_zero [E.IsElliptic] :
    invariantDifferentialDenom E ≠ 0 := by
  rw [invariantDifferentialDenom, add_assoc, algebraMap_a₁_mul_X_add_a₃]
  exact two_mul_root_add_ne_zero E

/-! ### The differential of `x` is nonzero -/

/-- `F[X] → K(E)` is injective: a nonzero polynomial cannot be a multiple of `W`, whose degree
in `Y` is two, and `F[E] → K(E)` is injective. -/
private lemma algebraMap_polynomial_injective :
    Function.Injective (algebraMap (Polynomial F) E.FunctionField) := by
  rw [IsScalarTower.algebraMap_eq (Polynomial F) E.CoordinateRing E.FunctionField]
  refine (IsFractionRing.injective E.CoordinateRing E.FunctionField).comp ?_
  intro p q (h : algebraMap _ E.CoordinateRing p = algebraMap _ E.CoordinateRing q)
  by_contra hpq
  have h' : algebraMap (Polynomial F) E.CoordinateRing (p - q) = 0 := by
    rw [map_sub, sub_eq_zero, h]
  have hle := Polynomial.natDegree_le_of_dvd (AdjoinRoot.mk_eq_zero.mp h')
    (Polynomial.C_ne_zero.mpr (sub_ne_zero.mpr hpq))
  have hC : (algebraMap (Polynomial F) (Polynomial (Polynomial F)) (p - q)).natDegree = 0 :=
    Polynomial.natDegree_C _
  rw [natDegree_polynomial] at hle
  omega

/-- Evaluating a polynomial at `x` in `K(E)` is applying `algebraMap` to it. -/
private lemma aeval_algebraMap_X (p : Polynomial F) :
    Polynomial.aeval (algebraMap (Polynomial F) E.FunctionField Polynomial.X) p =
      algebraMap (Polynomial F) E.FunctionField p := by
  have h := Polynomial.aeval_algHom
    (IsScalarTower.toAlgHom F (Polynomial F) E.FunctionField) Polynomial.X
  rw [Polynomial.aeval_X_left, AlgHom.comp_id] at h
  exact DFunLike.congr_fun h p

/-- `x` is transcendental over `F`. -/
private lemma not_isAlgebraic_X :
    ¬ IsAlgebraic F (algebraMap (Polynomial F) E.FunctionField Polynomial.X) := by
  rintro ⟨p, hp_ne, hp_eval⟩
  exact hp_ne (algebraMap_polynomial_injective E
    (((aeval_algebraMap_X E p).symm.trans hp_eval).trans (map_zero _).symm))

/-- If `D x = 0` then `D` kills every polynomial in `x`. -/
private lemma D_algebraMap_polynomial
    (hDx : KaehlerDifferential.D F E.FunctionField
      (algebraMap (Polynomial F) E.FunctionField Polynomial.X) = 0) (p : Polynomial F) :
    KaehlerDifferential.D F E.FunctionField
      (algebraMap (Polynomial F) E.FunctionField p) = 0 := by
  have hxn : ∀ n : ℕ, KaehlerDifferential.D F E.FunctionField
      (algebraMap (Polynomial F) E.FunctionField Polynomial.X ^ n) = 0 := by
    intro n
    induction n with
    | zero => rw [pow_zero, Derivation.map_one_eq_zero]
    | succ n ih => rw [pow_succ, Derivation.leibniz, ih, smul_zero, hDx, smul_zero, add_zero]
  rw [← aeval_algebraMap_X E p]
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, hp, hq, add_zero]
  | monomial n a =>
    rw [Polynomial.aeval_monomial, Derivation.leibniz, Derivation.map_algebraMap, smul_zero,
      add_zero, hxn n, smul_zero]

/-- The Weierstrass relation `y² + (a₁x + a₃) y = x³ + a₂x² + a₄x + a₆`, in the coordinate ring
`F[E]`: it is the defining relation of `F[E] = F[X][Y]/(W)`, read through `AdjoinRoot.mk`. -/
private lemma weierstrass_relation_coordinateRing :
    (AdjoinRoot.root E.polynomial) ^ 2 +
        algebraMap (Polynomial F) E.CoordinateRing
          (Polynomial.C E.a₁ * Polynomial.X + Polynomial.C E.a₃) *
        AdjoinRoot.root E.polynomial =
      algebraMap (Polynomial F) E.CoordinateRing
        (Polynomial.X ^ 3 + Polynomial.C E.a₂ * Polynomial.X ^ 2 +
          Polynomial.C E.a₄ * Polynomial.X + Polynomial.C E.a₆) := by
  have Y_sq : (AdjoinRoot.mk E.polynomial) Y ^ 2 =
      (AdjoinRoot.mk E.polynomial) (Polynomial.C (Polynomial.X ^ 3 +
        Polynomial.C E.a₂ * Polynomial.X ^ 2 + Polynomial.C E.a₄ * Polynomial.X +
        Polynomial.C E.a₆) -
      Polynomial.C (Polynomial.C E.a₁ * Polynomial.X + Polynomial.C E.a₃) * Y) :=
    AdjoinRoot.mk_eq_mk.mpr ⟨1, by rw [WeierstrassCurve.Affine.polynomial]; ring1⟩
  rw [AdjoinRoot.mk_X] at Y_sq
  simp only [map_sub, map_mul, AdjoinRoot.mk_X] at Y_sq
  rw [AdjoinRoot.mk_C, AdjoinRoot.mk_C, ← AdjoinRoot.algebraMap_eq] at Y_sq
  linear_combination Y_sq

/-- The Weierstrass relation, transported from `F[E]` to `K(E)`. -/
private lemma weierstrass_relation :
    (algebraMap E.CoordinateRing E.FunctionField (AdjoinRoot.root E.polynomial)) ^ 2 +
        algebraMap (Polynomial F) E.FunctionField
          (Polynomial.C E.a₁ * Polynomial.X + Polynomial.C E.a₃) *
        algebraMap E.CoordinateRing E.FunctionField (AdjoinRoot.root E.polynomial) =
      algebraMap (Polynomial F) E.FunctionField
        (Polynomial.X ^ 3 + Polynomial.C E.a₂ * Polynomial.X ^ 2 +
          Polynomial.C E.a₄ * Polynomial.X + Polynomial.C E.a₆) := by
  have h := congr_arg (algebraMap E.CoordinateRing E.FunctionField)
    (weierstrass_relation_coordinateRing E)
  rw [map_add, map_mul, map_pow] at h
  rwa [← IsScalarTower.algebraMap_apply (Polynomial F) E.CoordinateRing E.FunctionField,
    ← IsScalarTower.algebraMap_apply (Polynomial F) E.CoordinateRing E.FunctionField] at h

/-- If `D x = 0` then `D y = 0`: differentiating the Weierstrass relation leaves
`(2y + a₁x + a₃) · D y = 0`, and that denominator is invertible in the field `K(E)`. -/
private lemma D_root [E.IsElliptic]
    (hDx : KaehlerDifferential.D F E.FunctionField
      (algebraMap (Polynomial F) E.FunctionField Polynomial.X) = 0) :
    KaehlerDifferential.D F E.FunctionField
      (algebraMap E.CoordinateRing E.FunctionField (AdjoinRoot.root E.polynomial)) = 0 := by
  set D := KaehlerDifferential.D F E.FunctionField
  set y : E.FunctionField :=
    algebraMap E.CoordinateRing E.FunctionField (AdjoinRoot.root E.polynomial)
  set c := algebraMap (Polynomial F) E.FunctionField
    (Polynomial.C E.a₁ * Polynomial.X + Polynomial.C E.a₃)
  have hDc : D c = 0 := D_algebraMap_polynomial E hDx _
  have hsmul : (2 * y + c) • D y = 0 := by
    have hD_lhs : D (y ^ 2 + c * y) = (2 * y + c) • D y := by
      rw [map_add, sq, Derivation.leibniz, Derivation.leibniz, hDc, smul_zero, add_zero,
        add_smul, two_mul, add_smul]
    rw [← hD_lhs, weierstrass_relation E]
    exact D_algebraMap_polynomial E hDx _
  have hne : 2 * y + c ≠ 0 := two_mul_root_add_ne_zero E
  calc D y = (1 : E.FunctionField) • D y := (one_smul _ _).symm
    _ = ((2 * y + c)⁻¹ * (2 * y + c)) • D y := by rw [inv_mul_cancel₀ hne]
    _ = (2 * y + c)⁻¹ • ((2 * y + c) • D y) := (smul_smul _ _ _).symm
    _ = (2 * y + c)⁻¹ • 0 := by rw [hsmul]
    _ = 0 := smul_zero _

/-- If `D x = 0` then `D` kills the coordinate ring, which is spanned by `1` and `y`. -/
private lemma D_algebraMap_coordinateRing [E.IsElliptic]
    (hDx : KaehlerDifferential.D F E.FunctionField
      (algebraMap (Polynomial F) E.FunctionField Polynomial.X) = 0) (r : E.CoordinateRing) :
    KaehlerDifferential.D F E.FunctionField
      (algebraMap E.CoordinateRing E.FunctionField r) = 0 := by
  obtain ⟨p, q, hpq⟩ := WeierstrassCurve.Affine.CoordinateRing.exists_smul_basis_eq r
  rw [← hpq, map_add]
  simp only [Algebra.smul_def, map_mul, mul_one]
  rw [AdjoinRoot.mk_X, map_add, Derivation.leibniz,
    ← IsScalarTower.algebraMap_apply (Polynomial F) E.CoordinateRing E.FunctionField,
    ← IsScalarTower.algebraMap_apply (Polynomial F) E.CoordinateRing E.FunctionField,
    D_algebraMap_polynomial E hDx p, D_algebraMap_polynomial E hDx q, D_root E hDx, smul_zero,
    smul_zero, add_zero, add_zero]

/-- If `D x = 0` then `D` vanishes identically: every element of `K(E)` is a ratio of two
elements of `F[E]`. -/
private lemma D_eq_zero [E.IsElliptic]
    (hDx : KaehlerDifferential.D F E.FunctionField
      (algebraMap (Polynomial F) E.FunctionField Polynomial.X) = 0) (s : E.FunctionField) :
    KaehlerDifferential.D F E.FunctionField s = 0 := by
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := E.CoordinateRing) s
  rw [← hab, (KaehlerDifferential.D F E.FunctionField).leibniz_div_const _ _
    (D_algebraMap_coordinateRing E hDx b), D_algebraMap_coordinateRing E hDx a, smul_zero]

/-- **The differential of `x` is nonzero.** If it vanished, `D` would vanish identically, so
`Ω[K(E)/F] = 0` and `K(E)/F` would be formally unramified, hence separable algebraic —
contradicting the transcendence of `x`.

Deliberately not `@[simp]`, unlike the other two nonvanishing results here: its left-hand side is
not in simp-normal form, because `simp` rewrites `algebraMap (Polynomial F) E.CoordinateRing` to
`AdjoinRoot.of E.polynomial` via `AdjoinRoot.algebraMap_eq`, so the lemma could never fire. The
`algebraMap` spelling is kept because it is the form `invariantDifferential` is defined over. -/
theorem D_X_ne_zero [E.IsElliptic] :
    KaehlerDifferential.D F E.FunctionField
      (algebraMap E.CoordinateRing E.FunctionField
        (algebraMap (Polynomial F) E.CoordinateRing Polynomial.X)) ≠ 0 := by
  rw [← IsScalarTower.algebraMap_apply (Polynomial F) E.CoordinateRing E.FunctionField]
  intro hDx
  have hΩ : Subsingleton (KaehlerDifferential F E.FunctionField) := by
    suffices (⊤ : Submodule E.FunctionField (KaehlerDifferential F E.FunctionField)) ≤ ⊥ from
      (subsingleton_iff_forall_eq 0).mpr fun ω => this trivial
    rw [← KaehlerDifferential.span_range_derivation, Submodule.span_le]
    rintro _ ⟨s, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_bot]
    exact D_eq_zero E hDx s
  have hFU : Algebra.FormallyUnramified F E.FunctionField := ⟨hΩ⟩
  have hSep := (Algebra.FormallyUnramified.iff_isSeparable F E.FunctionField).mp hFU
  exact not_isAlgebraic_X E ((Algebra.IsSeparable.isAlgebraic F E.FunctionField).isAlgebraic _)

/-! ### The invariant differential -/

/-- The invariant differential `ω = dx / (2y + a₁x + a₃)`, as an element of `Ω[K(E)/F]`. -/
noncomputable def invariantDifferential :
    KaehlerDifferential F E.FunctionField :=
  (invariantDifferentialDenom E)⁻¹ •
    KaehlerDifferential.D F E.FunctionField
      (algebraMap E.CoordinateRing E.FunctionField
        (algebraMap (Polynomial F) E.CoordinateRing Polynomial.X))

/-- The defining formula for `invariantDifferential`. The definition body is not exposed, so this
equation lemma is how a consumer in another module computes with it. Not `@[simp]`: the point of
naming `invariantDifferentialDenom` is that the nonvanishing results can be stated over it, which
unfolding everywhere would defeat. -/
theorem invariantDifferential_def :
    invariantDifferential E = (invariantDifferentialDenom E)⁻¹ •
      KaehlerDifferential.D F E.FunctionField
        (algebraMap E.CoordinateRing E.FunctionField
          (algebraMap (Polynomial F) E.CoordinateRing Polynomial.X)) :=
  (rfl)

/-- **The invariant differential is nonzero** as an element of `Ω[K(E)/F]`. It is the product of
an inverse of the nonzero denominator with `D x`, both nonzero.

This is strictly weaker than Silverman's III.1.5, `div ω = 0`: a nonzero rational differential
may still have zeros and poles, and no pointwise regularity or nonvanishing statement is
formalised here. -/
@[simp]
theorem invariantDifferential_ne_zero [E.IsElliptic] : invariantDifferential E ≠ 0 := by
  rw [invariantDifferential_def]
  exact smul_ne_zero (inv_ne_zero (invariantDifferentialDenom_ne_zero E)) (D_X_ne_zero E)

end WeierstrassCurve.Affine
