/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Inverse
public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.WExpansion
public import TauCeti.RingTheory.MvPowerSeries.Inverse

/-!
# The formal inverse of a Weierstrass curve

In the `(z, w)`-chart of `WeierstrassCurve.formalW`, where `x = z / w` and `y = -1 / w`, the
negative of the point with parameter `z` has parameter `ι(z) = -z / (1 - a₁ z - a₃ w(z))`. This
file constructs that series and proves it is an involution.

The denominator is `formalInverseDenom`; its constant coefficient is `1`, so it is a unit, which is
what makes `formalInverse` a power series at all.

## Main definitions

* `WeierstrassCurve.formalInverseDenom`: the series `1 - a₁ z - a₃ w(z)` inverted in `ι`.
* `WeierstrassCurve.formalInverse`: the parameter `ι(z)` of the negative point.

## Main results

* `WeierstrassCurve.subst_formalInverse_self`: `ι(ι(z)) = z`, the formal inverse is an
  involution. This is the formal-series form of `-(-P) = P`.
* `WeierstrassCurve.subst_formalInverse_formalW` and
  `WeierstrassCurve.subst_formalInverse_formalInverseDenom`: the two substitution identities the
  involution is assembled from, giving the `w`-coordinate and the denominator at the negative
  point.
* `WeierstrassCurve.isUnit_formalInverseDenom`: the denominator is a unit.
* `WeierstrassCurve.constantCoeff_formalInverse`: `ι(0) = 0`, so `ι` may itself be substituted
  into a power series — `WeierstrassCurve.hasSubst_formalInverse`.

## Implementation notes

The substitution identities are proved through the uniqueness of the solution of the
`w`-equation (`WeierstrassCurve.eq_subst_formalW_of_wEquation`) rather than by comparing
coefficients: `w ∘ ι` and the candidate `-w · u⁻¹` both solve that equation at the parameter
`ι`, and a solution with vanishing constant coefficient is unique.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1.

## Provenance

Adapted from Michael Stoll's `EllipticCurves` project
(`github.com/MichaelStollBayreuth/EllipticCurves`, Apache-2.0, pinned by
`TauCetiRoadmap/EllipticCurves/README.md` at `66889eada51a`),
`EllipticCurves/WeierstrassFormalGroup/Chord.lean` — declarations `uSeries`,
`constantCoeff_uSeries`, `mul_invOfUnit_uSeries`, `isUnit_uSeries`, `inverseSeries`,
`constantCoeff_inverseSeries`, `hasSubst_inverseSeries`, `subst_inverseSeries_invOfUnit`,
`subst_inverseSeries_wSeries`, `subst_inverseSeries_uSeries` and `subst_inverseSeries_self`.

The source's `uSeries` is renamed `formalInverseDenom` here. It must not be called `formalU`: that
name is already taken, in `FormalGroup/WExpansion.lean`, by the unit part `w(z) / z ^ 3`, which
is a different series (it is the source's `vSeries`). The source proves the substitution
identities through its own private `wStep` recursion; this file uses the `w`-equation API of
`FormalGroup/WExpansion.lean` instead, so the source's `wStepAt` lemmas are not ported.
-/

public section

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-! ### The denominator of the formal inverse -/

/-- The denominator `1 - a₁ z - a₃ w(z)` of the formal inverse.

Up to sign and a factor of `w`, this is the `y`-coordinate of the negative of the point with
parameter `z`, in the coordinates `x = z / w`, `y = -1 / w`. -/
noncomputable def formalInverseDenom : PowerSeries R :=
  1 - PowerSeries.C W.a₁ * PowerSeries.X - PowerSeries.C W.a₃ * formalW W

/-- The defining formula for `formalInverseDenom`. -/
theorem formalInverseDenom_def :
    formalInverseDenom W =
      1 - PowerSeries.C W.a₁ * PowerSeries.X - PowerSeries.C W.a₃ * formalW W :=
  (rfl)

/-- The denominator of the formal inverse is `1` at the origin, which is what makes it a unit. -/
@[simp]
theorem constantCoeff_formalInverseDenom :
    PowerSeries.constantCoeff (formalInverseDenom W) = 1 := by
  rw [formalInverseDenom_def]
  simp

/-- The denominator times its `invOfUnit` is `1`. -/
theorem mul_invOfUnit_formalInverseDenom :
    formalInverseDenom W * PowerSeries.invOfUnit (formalInverseDenom W) 1 = 1 :=
  PowerSeries.mul_invOfUnit _ _ (by simp)

/-- The denominator of the formal inverse is a unit. -/
theorem isUnit_formalInverseDenom : IsUnit (formalInverseDenom W) :=
  IsUnit.of_mul_eq_one _ (mul_invOfUnit_formalInverseDenom W)

/-! ### The formal inverse -/

/-- The parameter `ι(z) = -z / (1 - a₁ z - a₃ w(z))` of the negative of the point with parameter
`z` on the curve `(z, w(z))`. -/
noncomputable def formalInverse : PowerSeries R :=
  -(PowerSeries.X * PowerSeries.invOfUnit (formalInverseDenom W) 1)

/-- The defining formula for `formalInverse`. -/
theorem formalInverse_def :
    formalInverse W = -(PowerSeries.X * PowerSeries.invOfUnit (formalInverseDenom W) 1) :=
  (rfl)

/-- The formal inverse vanishes at the origin: the negative of `O` is `O`. -/
@[simp]
theorem constantCoeff_formalInverse : PowerSeries.constantCoeff (formalInverse W) = 0 := by
  rw [formalInverse_def]
  simp

/-- The formal inverse may be substituted into a power series. -/
theorem hasSubst_formalInverse : PowerSeries.HasSubst (formalInverse W) :=
  PowerSeries.HasSubst.of_constantCoeff_zero' (constantCoeff_formalInverse W)

/-! ### Substituting the formal inverse -/

/-- Composing the `w`-expansion with the formal inverse gives `-w / (1 - a₁ z - a₃ w)`, the
`w`-coordinate of the negative point.

Both sides solve the `w`-equation at the parameter `ι` and have vanishing constant coefficient,
so they agree by `eq_subst_formalW_of_wEquation`. Clearing the denominator `u ^ 3`, the identity
to check is `-w u ^ 2 = -z ^ 3 + a₁ z w u - a₂ z ^ 2 w + a₃ w ^ 2 u - a₄ z w ^ 2 - a₆ w ^ 3`,
which is the `w`-equation itself after `a₁ z w + a₃ w ^ 2 = w (1 - u)`. -/
theorem subst_formalInverse_formalW :
    PowerSeries.subst (formalInverse W) (formalW W) =
      -(formalW W * PowerSeries.invOfUnit (formalInverseDenom W) 1) := by
  have hu := mul_invOfUnit_formalInverseDenom W
  have hw := formalW_wEquation W
  refine (eq_subst_formalW_of_wEquation W (constantCoeff_formalInverse W) ?_ ?_).symm
  · simp
  · refine ((isUnit_formalInverseDenom W).pow 3).mul_left_cancel ?_
    rw [wEquationRHS_powerSeries, formalInverse_def, formalInverseDenom_def] at *
    grind

/-- Composing the denominator with the formal inverse inverts it. -/
theorem subst_formalInverse_formalInverseDenom :
    PowerSeries.subst (formalInverse W) (formalInverseDenom W) =
      PowerSeries.invOfUnit (formalInverseDenom W) 1 := by
  have hu := mul_invOfUnit_formalInverseDenom W
  refine (isUnit_formalInverseDenom W).mul_left_cancel ?_
  rw [mul_invOfUnit_formalInverseDenom W, formalInverseDenom_def,
    ← PowerSeries.coe_substAlgHom (hasSubst_formalInverse W)]
  -- `subst_C` lands on `MvPowerSeries.C`; `C_apply` is what identifies it with `PowerSeries.C`,
  -- without which the two spellings of the same map are opaque to `grind`.
  simp only [map_sub, map_mul, map_one, PowerSeries.coe_substAlgHom,
    PowerSeries.substAlgHom_X, PowerSeries.subst_C, ← PowerSeries.C_apply,
    subst_formalInverse_formalW W]
  rw [formalInverse_def, formalInverseDenom_def] at *
  grind

/-- **The formal inverse is an involution**: `ι(ι(z)) = z`.

This is the formal-series form of `-(-P) = P` for the group law near the origin. -/
theorem subst_formalInverse_self :
    PowerSeries.subst (formalInverse W) (formalInverse W) = PowerSeries.X := by
  have hu := mul_invOfUnit_formalInverseDenom W
  have hinv := PowerSeries.ringHom_invOfUnit
    (PowerSeries.substAlgHom (hasSubst_formalInverse W)) (D := formalInverseDenom W)
    (u := 1) (v := 1) (constantCoeff_formalInverseDenom W)
    (by rw [PowerSeries.coe_substAlgHom, subst_formalInverse_formalInverseDenom W]
        exact PowerSeries.constantCoeff_invOfUnit _ _)
  rw [PowerSeries.coe_substAlgHom] at hinv
  have hdouble : PowerSeries.invOfUnit (PowerSeries.invOfUnit (formalInverseDenom W) 1) 1 =
      formalInverseDenom W := by
    have h2 : PowerSeries.invOfUnit (formalInverseDenom W) 1 *
        PowerSeries.invOfUnit (PowerSeries.invOfUnit (formalInverseDenom W) 1) 1 = 1 :=
      PowerSeries.mul_invOfUnit _ 1 (by simp [PowerSeries.constantCoeff_invOfUnit])
    calc PowerSeries.invOfUnit (PowerSeries.invOfUnit (formalInverseDenom W) 1) 1
        = formalInverseDenom W * (PowerSeries.invOfUnit (formalInverseDenom W) 1 *
            PowerSeries.invOfUnit (PowerSeries.invOfUnit (formalInverseDenom W) 1) 1) := by
          rw [← mul_assoc, hu, one_mul]
      _ = formalInverseDenom W := by rw [h2, mul_one]
  have hexp : PowerSeries.subst (formalInverse W) (formalInverse W) =
      -(formalInverse W * PowerSeries.subst (formalInverse W)
        (PowerSeries.invOfUnit (formalInverseDenom W) 1)) := by
    have h : PowerSeries.subst (formalInverse W) (formalInverse W) =
        PowerSeries.subst (formalInverse W)
          (-(PowerSeries.X * PowerSeries.invOfUnit (formalInverseDenom W) 1)) := by
      rw [← formalInverse_def]
    rw [h, ← PowerSeries.coe_substAlgHom (hasSubst_formalInverse W), map_neg, map_mul,
      PowerSeries.substAlgHom_X (hasSubst_formalInverse W)]
  rw [hexp, hinv, subst_formalInverse_formalInverseDenom W, hdouble, formalInverse_def]
  linear_combination (PowerSeries.X : PowerSeries R) * hu

/-! ### Base change -/

section BaseChange

variable {S : Type*} [CommRing S] (φ : R →+* S)

/-- The denominator of the formal inverse commutes with base change. -/
@[simp]
theorem map_formalInverseDenom :
    formalInverseDenom (W.map φ) = PowerSeries.map φ (formalInverseDenom W) := by
  simp only [formalInverseDenom_def, map_sub, map_one, map_mul, PowerSeries.map_C,
    PowerSeries.map_X, map_formalW W φ, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃]

/-- **The formal inverse commutes with base change.** -/
@[simp]
theorem map_formalInverse :
    formalInverse (W.map φ) = PowerSeries.map φ (formalInverse W) := by
  have hinv := PowerSeries.ringHom_invOfUnit (PowerSeries.map φ) (D := formalInverseDenom W)
    (u := 1) (v := 1) (constantCoeff_formalInverseDenom W)
    (by rw [show (PowerSeries.map φ (formalInverseDenom W) : PowerSeries S) =
          formalInverseDenom (W.map φ) from (map_formalInverseDenom W φ).symm]
        exact constantCoeff_formalInverseDenom (W.map φ))
  rw [formalInverse_def, formalInverse_def, map_neg, map_mul, PowerSeries.map_X, hinv,
    map_formalInverseDenom W φ]

end BaseChange

end WeierstrassCurve
