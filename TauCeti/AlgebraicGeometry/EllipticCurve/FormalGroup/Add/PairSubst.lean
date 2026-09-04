/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Add.Series
public import TauCeti.RingTheory.MvPowerSeries.Substitution

/-!
# The chord construction along an arbitrary pair of parameters

`FormalGroup/Chord.lean` builds the chord data — the slope `λ`, the intercept `ν`, the third
root `z₃` and the addition series `F` — as two-variable series in `MvPowerSeries (Unit ⊕ Unit) O`,
and states their defining identities in the two variables themselves. This file substitutes an
**arbitrary pair** `(q₁, q₂)` of series with vanishing constant coefficient for those variables,
and carries each identity across.

`FormalGroup/Add/Inverse.lean` already does this for the one pair `(z, ι(z))`. Its versions are
this file's, specialized; see the Provenance note there.

## Main results

* `WeierstrassCurve.subst_pair_toMvPowerSeries_inl`,
  `WeierstrassCurve.subst_pair_toMvPowerSeries_inr`: the one-variable `w`-expansion, embedded in
  either variable, becomes `w(q₁)` respectively `w(q₂)`.
* `WeierstrassCurve.subst_pair_formalSlope_mul`: `λ(q₁, q₂) * (q₂ - q₁) = w(q₂) - w(q₁)`.
* `WeierstrassCurve.subst_pair_formalThirdRoot_formalW`: the `w`-expansion at the third root
  is the chord line read there.
* `WeierstrassCurve.subst_pair_thirdRootDenom_mul`: Vieta's denominator stays a unit at the
  pair, and `WeierstrassCurve.subst_pair_thirdRootDenom_ne_zero`: in particular it is nonzero.
* `WeierstrassCurve.subst_pair_formalThirdRoot_relation`: the defining relation of `z₃` at
  the pair, with that inverse cleared.
* `WeierstrassCurve.constantCoeff_subst_pair_formalThirdRoot`: the third root at the pair again
  vanishes at the origin, so it is itself a legitimate parameter.
* `WeierstrassCurve.subst_pair_formalAdd`: the addition series at the pair is the formal inverse
  read at `z₃`.
* `WeierstrassCurve.subst_pair_formalW_formalAdd`: the `w`-expansion at the addition series,
  `w(F(q₁, q₂)) = -(w(z₃) * u(z₃)⁻¹)`.
* `WeierstrassCurve.subst_pair_formalInverseDenom_mul`,
  `WeierstrassCurve.subst_pair_formalInverseDenom_eq`: the denominator of the formal inverse,
  read at `z₃`, is a unit and equals `1 - a₁ z₃ - a₃ w(z₃)`.
* `WeierstrassCurve.subst_pair_formalAdd_eq`: the addition series written out,
  `F(q₁, q₂) = -(z₃ * u(z₃)⁻¹)`.
* `WeierstrassCurve.subst_pair_formalIntercept_eq_inl`,
  `WeierstrassCurve.subst_pair_formalIntercept_eq_inr`: the chord's intercept at the pair, read
  from either of the two points.
* `WeierstrassCurve.subst_pair_formalIntercept_mul_sub`: the cross combination
  `q₁ w(q₂) - q₂ w(q₁) = ν(q₁, q₂) * (q₁ - q₂)`, which is what the two readings buy.
* `WeierstrassCurve.subst_pair_formalThirdRoot_ne_zero`: a nonzero intercept forces a nonzero
  third root.

## Implementation notes

The pair is the family `Sum.elim (fun _ ↦ q₁) fun _ ↦ q₂` on `Unit ⊕ Unit`, written inline
throughout as `Add/Inverse.lean` writes its own family inline.

Two of Stoll's helpers in this range are not ported, because this repository already has them in
a more general form. His `subst_pair_rename`, which pushes the substitution through the
one-variable-into-two-variable embedding, is Mathlib's `PowerSeries.subst_toMvPowerSeries`
composed with `Sum.elim_inl`/`Sum.elim_inr` — this repository builds the two-variable series with
`PowerSeries.toMvPowerSeries` where the source uses `MvPowerSeries.rename`. His
`subst_wSeries_fix`, that `w` composed with any parameter solves the `w`-equation, is
`WeierstrassCurve.subst_formalW_wEquation` in `FormalGroup/WExpansion.lean`, stated there over an
arbitrary algebra.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1.

## Provenance

Adapted from Michael Stoll's `EllipticCurves` project
(`github.com/MichaelStollBayreuth/EllipticCurves`, Apache-2.0) at commit
`66889eada51a74c2f5dfb7fb5909b0b5a0a2d96e`,
`EllipticCurves/WeierstrassFormalGroup/ThirdPoint.lean`, declarations `hasSubst_pair`,
`pair_slope_identity`, `pair_A_mul` and `pair_T₃_relation`, together with `pair_online`
from `EllipticCurves/WeierstrassFormalGroup/GroupLaw.lean`.

The source's `slopeSeries`, `interceptSeries` and `wSeries` are `formalSlope`, `formalIntercept`
and `formalW` here, continuing the renaming this repository applies to that development, so
`pair_slope_identity` and `pair_online` are `subst_pair_formalSlope_mul` and
`subst_pair_formalThirdRoot_formalW`.
Stoll's `A` for Vieta's denominator is `formalThirdRootDenom` here, so `pair_A_mul` and
`pair_T₃_relation` are `subst_pair_thirdRootDenom_mul` and
`subst_pair_formalThirdRoot_relation`.

Also from that file, `pair_thirdRoot_constantCoeff` is
`constantCoeff_subst_pair_formalThirdRoot` and `pair_wF` is `subst_pair_formalW_formalAdd`.
The source's `pair_F_comp` needs no counterpart of its own: it says the addition series at the
pair is the inverse series read at the third root, which here is `formalAdd`'s *definition*
(`Add/Series.lean`) pushed through the substitution, and that is `subst_pair_formalAdd`.

**A naming trap worth recording, since the rename map above invites the wrong reading.** Stoll's
`uSeries` (`Chord.lean:351`, `1 - a₁ z - a₃ w`) is `formalInverseDenom` here
(`FormalGroup/Inverse.lean`), **not** `formalU`. This repository's `formalU` is a different
series — the unit part of the `w`-expansion, `w = z³ u`. Anything ported from the source's `u`
lemmas must target `formalInverseDenom`.

The source's `pair_intercept_identity₁` and `pair_intercept_identity₂` are
`subst_pair_formalIntercept_eq_inl` and `subst_pair_formalIntercept_eq_inr` here.
-/

public section

namespace WeierstrassCurve

open MvPowerSeries

variable {O : Type*} [CommRing O] (W : WeierstrassCurve O)
variable {σ : Type*} {q₁ q₂ : MvPowerSeries σ O}

/-- The `w`-expansion in the first parameter becomes `w(q₁)`. -/
@[simp]
theorem subst_pair_toMvPowerSeries_inl (h₁ : constantCoeff q₁ = 0)
    (h₂ : constantCoeff q₂ = 0) :
    subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) : Unit ⊕ Unit → MvPowerSeries σ O)
      ((formalW W).toMvPowerSeries (Sum.inl ())) = PowerSeries.subst q₁ (formalW W) := by
  rw [PowerSeries.subst_toMvPowerSeries (hasSubst_pair h₁ h₂), Sum.elim_inl]

/-- The `w`-expansion in the second parameter becomes `w(q₂)`. -/
@[simp]
theorem subst_pair_toMvPowerSeries_inr (h₁ : constantCoeff q₁ = 0)
    (h₂ : constantCoeff q₂ = 0) :
    subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) : Unit ⊕ Unit → MvPowerSeries σ O)
      ((formalW W).toMvPowerSeries (Sum.inr ())) = PowerSeries.subst q₂ (formalW W) := by
  rw [PowerSeries.subst_toMvPowerSeries (hasSubst_pair h₁ h₂), Sum.elim_inr]

/-! ### The chord through the two parametrized points -/

/-- The defining property of the slope, read at the pair `(q₁, q₂)`:
`λ(q₁, q₂) * (q₂ - q₁) = w(q₂) - w(q₁)`. -/
theorem subst_pair_formalSlope_mul (h₁ : constantCoeff q₁ = 0) (h₂ : constantCoeff q₂ = 0) :
    subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) : Unit ⊕ Unit → MvPowerSeries σ O)
        (formalSlope W) * (q₂ - q₁) =
      PowerSeries.subst q₂ (formalW W) - PowerSeries.subst q₁ (formalW W) := by
  have h := congrArg (subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) :
    Unit ⊕ Unit → MvPowerSeries σ O)) (formalSlope_mul_sub W)
  rw [← coe_substAlgHom (hasSubst_pair h₁ h₂)] at h
  simp only [map_mul, map_sub] at h
  simp only [coe_substAlgHom (hasSubst_pair h₁ h₂), subst_pair_toMvPowerSeries_inl W h₁ h₂,
    subst_pair_toMvPowerSeries_inr W h₁ h₂, subst_X (hasSubst_pair h₁ h₂)] at h
  have h1 : (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) :
      Unit ⊕ Unit → MvPowerSeries σ O) (Sum.inr ()) = q₂ := rfl
  have h2 : (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) :
      Unit ⊕ Unit → MvPowerSeries σ O) (Sum.inl ()) = q₁ := rfl
  rw [h1, h2] at h
  linear_combination h

/-! ### The third point of the chord lies on the curve -/

/-- The on-line identity at the pair `(q₁, q₂)`: reading the `w`-expansion at the third root
gives the chord line read there. -/
theorem subst_pair_formalThirdRoot_formalW (h₁ : constantCoeff q₁ = 0) (h₂ : constantCoeff q₂ = 0) :
    subst (fun _ : Unit ↦ subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) :
        Unit ⊕ Unit → MvPowerSeries σ O) (formalThirdRoot W)) (formalW W) =
      subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) : Unit ⊕ Unit → MvPowerSeries σ O)
          (formalSlope W) *
        subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) : Unit ⊕ Unit → MvPowerSeries σ O)
          (formalThirdRoot W) +
        subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) : Unit ⊕ Unit → MvPowerSeries σ O)
          (formalIntercept W) := by
  have h := congrArg (substAlgHom (hasSubst_pair h₁ h₂)) (subst_formalThirdRoot_formalW W)
  simp only [map_add, map_mul] at h
  simp only [coe_substAlgHom (hasSubst_pair h₁ h₂)] at h
  rwa [subst_comp_subst_apply (hasSubst_formalThirdRoot W) (hasSubst_pair h₁ h₂)] at h

/-! ### Vieta's denominator and the third-root relation -/

/-- Vieta's denominator, read at the pair `(q₁, q₂)`, is still a unit: it times its `invOfUnit`
is `1`. -/
theorem subst_pair_thirdRootDenom_mul (h₁ : constantCoeff q₁ = 0) (h₂ : constantCoeff q₂ = 0) :
    (1 + C W.a₂ *
        subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) : Unit ⊕ Unit → MvPowerSeries σ O)
          (formalSlope W) +
        C W.a₄ *
        subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) : Unit ⊕ Unit → MvPowerSeries σ O)
          (formalSlope W) ^ 2 +
        C W.a₆ *
        subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) : Unit ⊕ Unit → MvPowerSeries σ O)
          (formalSlope W) ^ 3) *
      subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) : Unit ⊕ Unit → MvPowerSeries σ O)
        (invOfUnit (1 + C W.a₂ * formalSlope W + C W.a₄ * formalSlope W ^ 2 +
      C W.a₆ * formalSlope W ^ 3) 1) = 1 := by
  have h := congrArg (substAlgHom (hasSubst_pair h₁ h₂))
    (mul_invOfUnit (1 + C W.a₂ * formalSlope W + C W.a₄ * formalSlope W ^ 2 +
      C W.a₆ * formalSlope W ^ 3) 1 (constantCoeff_formalThirdRootDenom W))
  simp only [map_mul, map_add, map_one, map_pow] at h
  simp only [coe_substAlgHom (hasSubst_pair h₁ h₂), subst_C] at h
  exact h

/-- Vieta's denominator at the pair is nonzero, because it has an explicit inverse. Over a
nontrivial base this is immediate from `subst_pair_thirdRootDenom_mul`; no coefficient
computation is needed. -/
theorem subst_pair_thirdRootDenom_ne_zero [Nontrivial O] (h₁ : constantCoeff q₁ = 0)
    (h₂ : constantCoeff q₂ = 0) :
    (1 + C W.a₂ *
        subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) : Unit ⊕ Unit → MvPowerSeries σ O)
          (formalSlope W) +
        C W.a₄ *
        subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) : Unit ⊕ Unit → MvPowerSeries σ O)
          (formalSlope W) ^ 2 +
        C W.a₆ *
        subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) : Unit ⊕ Unit → MvPowerSeries σ O)
          (formalSlope W) ^ 3) ≠ 0 := by
  intro h
  have hmul := subst_pair_thirdRootDenom_mul W h₁ h₂
  rw [h, zero_mul] at hmul
  exact zero_ne_one hmul

/-- The defining relation of the third root at the pair `(q₁, q₂)`, with the inverse of Vieta's
denominator eliminated. -/
theorem subst_pair_formalThirdRoot_relation (h₁ : constantCoeff q₁ = 0)
    (h₂ : constantCoeff q₂ = 0) :
    (1 + C W.a₂ *
        subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) : Unit ⊕ Unit → MvPowerSeries σ O)
          (formalSlope W) +
        C W.a₄ *
        subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) : Unit ⊕ Unit → MvPowerSeries σ O)
          (formalSlope W) ^ 2 +
        C W.a₆ *
        subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) : Unit ⊕ Unit → MvPowerSeries σ O)
          (formalSlope W) ^ 3) *
      (subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) : Unit ⊕ Unit → MvPowerSeries σ O)
          (formalThirdRoot W) + q₁ + q₂) =
      -(C W.a₁ *
        subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) : Unit ⊕ Unit → MvPowerSeries σ O)
          (formalSlope W) +
        C W.a₂ *
        subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) : Unit ⊕ Unit → MvPowerSeries σ O)
          (formalIntercept W) +
        C W.a₃ *
        subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) : Unit ⊕ Unit → MvPowerSeries σ O)
          (formalSlope W) ^ 2 +
        2 * C W.a₄ *
        subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) : Unit ⊕ Unit → MvPowerSeries σ O)
          (formalSlope W) *
          subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) : Unit ⊕ Unit → MvPowerSeries σ O)
            (formalIntercept W) +
        3 * C W.a₆ *
        subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) : Unit ⊕ Unit → MvPowerSeries σ O)
          (formalSlope W) ^ 2 *
          subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) : Unit ⊕ Unit → MvPowerSeries σ O)
            (formalIntercept W)) := by
  have hexp := congrArg (substAlgHom (hasSubst_pair h₁ h₂)) (formalThirdRoot_def W)
  simp only [map_sub, map_neg, map_mul, map_add, map_pow, map_ofNat] at hexp
  simp only [coe_substAlgHom (hasSubst_pair h₁ h₂), subst_X (hasSubst_pair h₁ h₂),
    subst_C] at hexp
  have hr : (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) :
      Unit ⊕ Unit → MvPowerSeries σ O) (Sum.inr ()) = q₂ := rfl
  have hl : (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) :
      Unit ⊕ Unit → MvPowerSeries σ O) (Sum.inl ()) = q₁ := rfl
  rw [hr, hl] at hexp
  have hAd := subst_pair_thirdRootDenom_mul W h₁ h₂
  set Lp :=
    subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) : Unit ⊕ Unit → MvPowerSeries σ O)
      (formalSlope W)
  set Np :=
    subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) : Unit ⊕ Unit → MvPowerSeries σ O)
      (formalIntercept W)
  set Tp :=
    subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) : Unit ⊕ Unit → MvPowerSeries σ O)
      (formalThirdRoot W)
  set dp :=
    subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) : Unit ⊕ Unit → MvPowerSeries σ O)
      (invOfUnit (1 + C W.a₂ * formalSlope W + C W.a₄ * formalSlope W ^ 2 +
      C W.a₆ * formalSlope W ^ 3) 1)
  clear_value Lp Np Tp dp
  linear_combination (1 + C W.a₂ * Lp + C W.a₄ * Lp ^ 2 + C W.a₆ * Lp ^ 3) * hexp -
    (C W.a₁ * Lp + C W.a₂ * Np + C W.a₃ * Lp ^ 2 + 2 * C W.a₄ * Lp * Np +
      3 * C W.a₆ * Lp ^ 2 * Np) * hAd

/-! ### The third root as a parameter in its own right -/

/-- The third root, read at the pair `(q₁, q₂)`, again has vanishing constant coefficient, so it
is itself a legitimate parameter to substitute into a one-variable series. -/
@[simp]
theorem constantCoeff_subst_pair_formalThirdRoot (h₁ : constantCoeff q₁ = 0)
    (h₂ : constantCoeff q₂ = 0) :
    constantCoeff (subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) : Unit ⊕ Unit → MvPowerSeries σ O)
      (formalThirdRoot W)) = 0 :=
  constantCoeff_subst_eq_zero (hasSubst_pair h₁ h₂) (by rintro (j | j) <;> simpa)
    (constantCoeff_formalThirdRoot W)

/-- The addition series at the pair `(q₁, q₂)` is the formal inverse read at the third root
`z₃(q₁, q₂)`.

This is `formalAdd_def` pushed through the pair substitution, and it is the bridge that turns any
one-variable identity about `formalInverse` into a statement about the group law at the pair. -/
theorem subst_pair_formalAdd (h₁ : constantCoeff q₁ = 0) (h₂ : constantCoeff q₂ = 0) :
    subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) : Unit ⊕ Unit → MvPowerSeries σ O) (formalAdd W) =
      subst (fun _ : Unit ↦ subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) :
        Unit ⊕ Unit → MvPowerSeries σ O) (formalThirdRoot W)) (formalInverse W) := by
  rw [formalAdd_def, subst_comp_subst_apply (hasSubst_formalThirdRoot W) (hasSubst_pair h₁ h₂)]

/-- The `w`-expansion at the addition series, read at the pair `(q₁, q₂)`:
`w(F(q₁, q₂)) = -(w(z₃) * u(z₃)⁻¹)`, where `z₃ = z₃(q₁, q₂)` is the third root and `u` is
`formalInverseDenom`, the denominator of the formal inverse.

This is the one-variable `subst_formalInverse_formalW` carried across by `subst_pair_formalAdd`,
so the group law's `w` at a pair is never recomputed. The third root is spelled as a `Unit`-family
substitution, matching `subst_pair_formalThirdRoot_formalW`, so the two rewrite against each
other. -/
theorem subst_pair_formalW_formalAdd (h₁ : constantCoeff q₁ = 0) (h₂ : constantCoeff q₂ = 0) :
    subst (fun _ : Unit ↦ subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) :
        Unit ⊕ Unit → MvPowerSeries σ O) (formalAdd W)) (formalW W) =
      -(subst (fun _ : Unit ↦ subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) :
            Unit ⊕ Unit → MvPowerSeries σ O) (formalThirdRoot W)) (formalW W) *
        subst (fun _ : Unit ↦ subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) :
            Unit ⊕ Unit → MvPowerSeries σ O) (formalThirdRoot W))
          (PowerSeries.invOfUnit (formalInverseDenom W) 1)) := by
  have hT : HasSubst (fun _ : Unit ↦ subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) :
      Unit ⊕ Unit → MvPowerSeries σ O) (formalThirdRoot W)) :=
    hasSubst_of_constantCoeff_zero fun _ ↦ constantCoeff_subst_pair_formalThirdRoot W h₁ h₂
  have hfam : (fun _ : Unit ↦ subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) :
        Unit ⊕ Unit → MvPowerSeries σ O) (formalAdd W)) =
      fun _ : Unit ↦ subst (fun _ : Unit ↦ subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) :
        Unit ⊕ Unit → MvPowerSeries σ O) (formalThirdRoot W)) (formalInverse W) :=
    funext fun _ ↦ subst_pair_formalAdd W h₁ h₂
  -- `PowerSeries.subst` *is* the `Unit`-indexed `MvPowerSeries.subst` by definition, so the
  -- middle step is `rfl`; it is needed because `subst_formalInverse_formalW` is stated in the
  -- univariate spelling while `subst_comp_subst_apply` produces the multivariable one.
  rw [hfam, ← subst_comp_subst_apply (hasSubst_of_constantCoeff_zero
    fun _ ↦ constantCoeff_formalInverse W) hT,
    show subst (fun _ : Unit ↦ formalInverse W) (formalW W) =
      PowerSeries.subst (formalInverse W) (formalW W) from rfl,
    subst_formalInverse_formalW, ← coe_substAlgHom hT]
  simp only [map_neg, map_mul]

/-- The denominator of the formal inverse, read at the third root `z₃(q₁, q₂)`, is still a unit:
it times its `invOfUnit` is `1`. -/
theorem subst_pair_formalInverseDenom_mul (h₁ : constantCoeff q₁ = 0)
    (h₂ : constantCoeff q₂ = 0) :
    subst (fun _ : Unit ↦ subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) :
          Unit ⊕ Unit → MvPowerSeries σ O) (formalThirdRoot W)) (formalInverseDenom W) *
        subst (fun _ : Unit ↦ subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) :
          Unit ⊕ Unit → MvPowerSeries σ O) (formalThirdRoot W))
          (PowerSeries.invOfUnit (formalInverseDenom W) 1) = 1 := by
  have hT : HasSubst (fun _ : Unit ↦ subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) :
      Unit ⊕ Unit → MvPowerSeries σ O) (formalThirdRoot W)) :=
    hasSubst_of_constantCoeff_zero fun _ ↦ constantCoeff_subst_pair_formalThirdRoot W h₁ h₂
  have h := congrArg (substAlgHom hT) (mul_invOfUnit_formalInverseDenom W)
  simp only [map_mul, map_one] at h
  simpa only [coe_substAlgHom hT] using h

/-- The denominator of the formal inverse, read at the third root, written out:
`u(z₃) = 1 - a₁ z₃ - a₃ w(z₃)`. -/
theorem subst_pair_formalInverseDenom_eq (h₁ : constantCoeff q₁ = 0)
    (h₂ : constantCoeff q₂ = 0) :
    subst (fun _ : Unit ↦ subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) :
        Unit ⊕ Unit → MvPowerSeries σ O) (formalThirdRoot W)) (formalInverseDenom W) =
      1 - C W.a₁ * subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) :
          Unit ⊕ Unit → MvPowerSeries σ O) (formalThirdRoot W) -
        C W.a₃ * subst (fun _ : Unit ↦ subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) :
          Unit ⊕ Unit → MvPowerSeries σ O) (formalThirdRoot W)) (formalW W) := by
  have hT : HasSubst (fun _ : Unit ↦ subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) :
      Unit ⊕ Unit → MvPowerSeries σ O) (formalThirdRoot W)) :=
    hasSubst_of_constantCoeff_zero fun _ ↦ constantCoeff_subst_pair_formalThirdRoot W h₁ h₂
  rw [formalInverseDenom_def, ← coe_substAlgHom hT]
  simp only [map_sub, map_one, map_mul]
  rw [coe_substAlgHom hT]
  -- `PowerSeries O` *is* `MvPowerSeries Unit O`, but the two namespaces name the constant and the
  -- variable differently, and `subst_C`/`subst_X` are stated in the multivariable spelling. The
  -- two identifications are `rfl`; there is no rewrite that reaches them, because the goal is
  -- already syntactically in the univariate spelling.
  simp only [show (PowerSeries.C : O →+* PowerSeries O) = MvPowerSeries.C from rfl,
    show (PowerSeries.X : PowerSeries O) = MvPowerSeries.X () from rfl, subst_C, subst_X hT]

/-- The addition series at the pair, written out: `F(q₁, q₂) = -(z₃ * u(z₃)⁻¹)`. -/
theorem subst_pair_formalAdd_eq (h₁ : constantCoeff q₁ = 0) (h₂ : constantCoeff q₂ = 0) :
    subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) : Unit ⊕ Unit → MvPowerSeries σ O) (formalAdd W) =
      -(subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) : Unit ⊕ Unit → MvPowerSeries σ O)
          (formalThirdRoot W) *
        subst (fun _ : Unit ↦ subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) :
          Unit ⊕ Unit → MvPowerSeries σ O) (formalThirdRoot W))
          (PowerSeries.invOfUnit (formalInverseDenom W) 1)) := by
  have hT : HasSubst (fun _ : Unit ↦ subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) :
      Unit ⊕ Unit → MvPowerSeries σ O) (formalThirdRoot W)) :=
    hasSubst_of_constantCoeff_zero fun _ ↦ constantCoeff_subst_pair_formalThirdRoot W h₁ h₂
  rw [subst_pair_formalAdd W h₁ h₂, formalInverse_def, ← coe_substAlgHom hT]
  simp only [map_neg, map_mul]
  -- as above: `PowerSeries.X` and `MvPowerSeries.X ()` are the same term, and `subst_X` is
  -- stated for the latter.
  rw [coe_substAlgHom hT,
    show (PowerSeries.X : PowerSeries O) = MvPowerSeries.X () from rfl, subst_X hT]

/-! ### The chord data at the pair, read from either point -/

/-- The intercept of the chord through the two parametrized points, read at the pair `(q₁, q₂)`
from the first point: `ν(q₁, q₂) = w(q₁) - λ(q₁, q₂) * q₁`.

`subst_pair_formalIntercept_eq_inr` is the same intercept read from the second point; the two
statements differ only in which parameter appears on the right, and rewriting with either one
clears the intercept but leaves the slope behind. Combining the two readings is what cancels the
slope, and that combination is already packaged as `subst_pair_formalIntercept_mul_sub`, so a
consumer that wants the slope gone should reach for it rather than for these two. -/
theorem subst_pair_formalIntercept_eq_inl (h₁ : constantCoeff q₁ = 0) (h₂ : constantCoeff q₂ = 0) :
    subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) : Unit ⊕ Unit → MvPowerSeries σ O)
        (formalIntercept W) = PowerSeries.subst q₁ (formalW W) -
      subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) : Unit ⊕ Unit → MvPowerSeries σ O)
        (formalSlope W) * q₁ := by
  simp [formalIntercept_def, subst_sub (hasSubst_pair h₁ h₂), subst_mul (hasSubst_pair h₁ h₂),
    subst_pair_toMvPowerSeries_inl W h₁ h₂, subst_X (hasSubst_pair h₁ h₂)]

/-- The same intercept read from the second point: `ν(q₁, q₂) = w(q₂) - λ(q₁, q₂) * q₂`. Together
with `subst_pair_formalIntercept_eq_inl` this is what expresses `q₁ * w(q₂) - q₂ * w(q₁)` through
the intercept alone.

The two readings differ only in which parameter appears on the right, and rewriting with either
one clears the intercept but leaves the slope behind; a consumer that wants the slope gone should
reach for `subst_pair_formalIntercept_mul_sub`, which packages the combination that cancels it. -/
theorem subst_pair_formalIntercept_eq_inr (h₁ : constantCoeff q₁ = 0) (h₂ : constantCoeff q₂ = 0) :
    subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) : Unit ⊕ Unit → MvPowerSeries σ O)
        (formalIntercept W) = PowerSeries.subst q₂ (formalW W) -
      subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) : Unit ⊕ Unit → MvPowerSeries σ O)
        (formalSlope W) * q₂ := by
  linear_combination subst_pair_formalIntercept_eq_inl W h₁ h₂ + subst_pair_formalSlope_mul W h₁ h₂

/-- The cross combination `q₁ w(q₂) - q₂ w(q₁)` is expressed through the intercept alone:
`q₁ w(q₂) - q₂ w(q₁) = ν(q₁, q₂) * (q₁ - q₂)`.

Reading the intercept from *both* points is what makes the slope cancel, so this is the one
intercept identity with no `λ` in it: `subst_pair_formalIntercept_eq_inl` and
`subst_pair_formalIntercept_eq_inr` each clear the intercept but leave the slope behind. The
factored `(q₁ - q₂)` on the right is what the associativity assembly needs in order to know that
the chord's `x`-coordinates are distinct; reach for it there as a single rewrite rather than
recombining the two readings by hand. -/
theorem subst_pair_formalIntercept_mul_sub (h₁ : constantCoeff q₁ = 0) (h₂ : constantCoeff q₂ = 0) :
    q₁ * PowerSeries.subst q₂ (formalW W) - q₂ * PowerSeries.subst q₁ (formalW W) =
      subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) : Unit ⊕ Unit → MvPowerSeries σ O)
        (formalIntercept W) * (q₁ - q₂) := by
  -- weighting the two readings by `q₂` and `q₁` makes the `λ` terms coincide and cancel
  linear_combination q₂ * subst_pair_formalIntercept_eq_inl W h₁ h₂ -
    q₁ * subst_pair_formalIntercept_eq_inr W h₁ h₂

/-- A nonzero intercept forces a nonzero third root: at `z₃ = 0` the on-line identity
`w(z₃) = λ z₃ + ν` collapses to `0 = ν`, since `w` has no constant term. -/
theorem subst_pair_formalThirdRoot_ne_zero (h₁ : constantCoeff q₁ = 0) (h₂ : constantCoeff q₂ = 0)
    (hN : subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) : Unit ⊕ Unit → MvPowerSeries σ O)
      (formalIntercept W) ≠ 0) :
    subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) : Unit ⊕ Unit → MvPowerSeries σ O)
      (formalThirdRoot W) ≠ 0 := by
  intro h
  refine hN ?_
  have honline := subst_pair_formalThirdRoot_formalW W h₁ h₂
  -- `rw [h]` leaves the substitution family as the literal `fun _ ↦ 0`, which is the zero
  -- function only definitionally, so it must be folded before
  -- `subst_zero_of_constantCoeff_zero` will match.
  rw [h, show (fun _ : Unit ↦ (0 : MvPowerSeries σ O)) = 0 from rfl,
    subst_zero_of_constantCoeff_zero (constantCoeff_formalW W)] at honline
  linear_combination -honline

end WeierstrassCurve
