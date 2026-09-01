/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Add.Series
public import TauCeti.AlgebraicGeometry.EllipticCurve.Universal

/-!
# The inverse law of the chord group law

`FormalGroup/Add/Series.lean` produces `formalAdd`, the series `F(z₁, z₂) = ι(z₃(z₁, z₂))` of the
chord construction, and `FormalGroup/Add/Unit.lean` proves its two unit laws. This file proves the
**inverse law** `F(z, ι(z)) = 0`, where `ι = formalInverse` is the formal inverse.

This is not one of the axioms of `FormalGroup`, which asks only for the constant and linear
coefficients and for associativity; a formal group law has a unique inverse series regardless.
What the identity says is that the series produced from the curve's negation is that inverse, so
the geometric `ι` and the abstract one agree.

Geometrically the chord through a point `P` and its negative `-P` is the vertical line through
them, which meets the curve again at the point at infinity; so the third root `z₃(z, ι(z))`
vanishes, and `F(z, ι(z)) = ι(z₃(z, ι(z))) = ι(0) = 0`.

## Main results

* `WeierstrassCurve.subst_invPair_formalThirdRoot`: the third root of the chord through a point
  and its formal inverse vanishes, `z₃(z, ι(z)) = 0`.
* `WeierstrassCurve.subst_invPair_formalAdd`: the **inverse law** `F(z, ι(z)) = 0`.

## Implementation notes

Both results hold over an arbitrary commutative ring, but the chord argument does not prove them
there: it divides by `ι - z`, so it needs `O` to be a domain, and it reaches `2 = 0` in the branch
it has to rule out. Both hypotheses are met by `ℤ[A₁, ⋯, A₆]`, so the argument runs over the
universal curve, and `map_specialize` then carries the conclusion to every `W` — the descent
`DivisionPolynomial/Omega.lean` also runs. The nondegeneracy `ι ≠ z` is not a further hypothesis:
it follows from `2 ≠ 0` by comparing linear coefficients.

The pair `(z, ι(z))` enters as the substituted family `Sum.elim X (fun _ ↦ formalInverse W)`,
written inline throughout, as `Add/Unit.lean` writes its own two families inline: it appears only
in this file, and naming it would add a definition whose unfolding lemma every proof would carry.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1.

## Provenance

Adapted from Michael Stoll's `EllipticCurves` project
(`github.com/MichaelStollBayreuth/EllipticCurves`, Apache-2.0, pinned by
`TauCetiRoadmap/EllipticCurves/README.md` at `66889eada51a`),
`EllipticCurves/WeierstrassFormalGroup/GroupLaw.lean` lines 118-308, the section `Domain`, and
`EllipticCurves/WeierstrassFormalGroup/ThirdPoint.lean` lines 372-460, 501-577 and 630-653.

The source's `addSeries`, `thirdRootSeries`, `slopeSeries`, `interceptSeries`, `inverseSeries`,
`uSeries` and `wSeries` are `formalAdd`, `formalThirdRoot`, `formalSlope`, `formalIntercept`,
`formalInverse`, `formalInverseDenom` and `formalW` here, continuing the renaming this repository
applies to the rest of that development.

The source states its pair lemmas for an arbitrary pair `(q₁, q₂)` of series with vanishing
constant coefficient, because its later `Assembly` and `Universal` sections reuse them at other
pairs. Every one of them is used here only at the pair `(z, ι(z))`, so they are stated at that
pair; the general forms belong with their first general consumer.

The source's `subst_wSeries_ne_zero`, `interceptSeries_ne_zero` and `X_pair_intercept_ne_zero`
are not ported. Their only consumers are in the source's `Assembly` and `Universal` sections,
which are not part of this development yet, so here they would be private lemmas with no
consumer.
-/

public section

namespace WeierstrassCurve

open MvPowerSeries

variable {O : Type*} [CommRing O] (W : WeierstrassCurve O)

/-! ### Substituting a point and its formal inverse -/

/-- Substituting `z` for the first parameter and `ι(z)` for the second is a legitimate
substitution: both series have vanishing constant coefficient. -/
private theorem hasSubst_invPair :
    HasSubst (Sum.elim X (fun _ ↦ formalInverse W) : Unit ⊕ Unit → MvPowerSeries Unit O) :=
  hasSubst_of_constantCoeff_zero
    (by rintro (j | j); exacts [constantCoeff_X j, constantCoeff_formalInverse W])

/-- The `w`-expansion in the first parameter is unchanged by the specialization. -/
private theorem subst_invPair_toMvPowerSeries_inl :
    subst (Sum.elim X (fun _ ↦ formalInverse W) : Unit ⊕ Unit → MvPowerSeries Unit O)
      ((formalW W).toMvPowerSeries (Sum.inl ())) = formalW W := by
  rw [PowerSeries.subst_toMvPowerSeries (hasSubst_invPair W), Sum.elim_inl]
  exact PowerSeries.X_subst (formalW W)

/-- The `w`-expansion in the second parameter becomes the `w`-coordinate of the negative point. -/
private theorem subst_invPair_toMvPowerSeries_inr :
    subst (Sum.elim X (fun _ ↦ formalInverse W) : Unit ⊕ Unit → MvPowerSeries Unit O)
      ((formalW W).toMvPowerSeries (Sum.inr ())) =
      -(formalW W * PowerSeries.invOfUnit (formalInverseDenom W) 1) := by
  rw [PowerSeries.subst_toMvPowerSeries (hasSubst_invPair W), Sum.elim_inr]
  exact subst_formalInverse_formalW W

/-! ### The chord through a point and its formal inverse -/

/-- The defining property of the slope, read at the pair `(z, ι(z))`. -/
private theorem subst_invPair_formalSlope_mul :
    subst (Sum.elim X (fun _ ↦ formalInverse W) : Unit ⊕ Unit → MvPowerSeries Unit O)
        (formalSlope W) * (formalInverse W - X ()) =
      -(formalW W * PowerSeries.invOfUnit (formalInverseDenom W) 1) - formalW W := by
  have h := congrArg (subst
    (Sum.elim X (fun _ ↦ formalInverse W) : Unit ⊕ Unit → MvPowerSeries Unit O))
    (formalSlope_mul_sub W)
  rw [← coe_substAlgHom (hasSubst_invPair W)] at h
  simp only [map_mul, map_sub] at h
  simp only [coe_substAlgHom (hasSubst_invPair W), subst_invPair_toMvPowerSeries_inl,
    subst_invPair_toMvPowerSeries_inr, subst_X (hasSubst_invPair W)] at h
  have h1 : (Sum.elim X (fun _ ↦ formalInverse W) :
      Unit ⊕ Unit → MvPowerSeries Unit O) (Sum.inr ()) = formalInverse W := rfl
  have h2 : (Sum.elim X (fun _ ↦ formalInverse W) :
      Unit ⊕ Unit → MvPowerSeries Unit O) (Sum.inl ()) = X () := rfl
  rw [h1, h2] at h
  linear_combination h

/-- The intercept at the pair `(z, ι(z))`, computed from the first point. -/
private theorem subst_invPair_formalIntercept_eq_inl :
    subst (Sum.elim X (fun _ ↦ formalInverse W) : Unit ⊕ Unit → MvPowerSeries Unit O)
        (formalIntercept W) =
      formalW W - subst (Sum.elim X (fun _ ↦ formalInverse W) :
        Unit ⊕ Unit → MvPowerSeries Unit O) (formalSlope W) * X () := by
  have h := congrArg (subst
    (Sum.elim X (fun _ ↦ formalInverse W) : Unit ⊕ Unit → MvPowerSeries Unit O))
    (formalIntercept_def W)
  rw [← coe_substAlgHom (hasSubst_invPair W)] at h
  simp only [map_mul, map_sub] at h
  simp only [coe_substAlgHom (hasSubst_invPair W), subst_invPair_toMvPowerSeries_inl,
    subst_X (hasSubst_invPair W)] at h
  have h2 : (Sum.elim X (fun _ ↦ formalInverse W) :
      Unit ⊕ Unit → MvPowerSeries Unit O) (Sum.inl ()) = X () := rfl
  rw [h2] at h
  exact h

/-- The intercept at the pair `(z, ι(z))`, computed from the second point. -/
private theorem subst_invPair_formalIntercept_eq_inr :
    subst (Sum.elim X (fun _ ↦ formalInverse W) : Unit ⊕ Unit → MvPowerSeries Unit O)
        (formalIntercept W) =
      -(formalW W * PowerSeries.invOfUnit (formalInverseDenom W) 1) -
        subst (Sum.elim X (fun _ ↦ formalInverse W) :
          Unit ⊕ Unit → MvPowerSeries Unit O) (formalSlope W) * formalInverse W := by
  have h := congrArg (subst
    (Sum.elim X (fun _ ↦ formalInverse W) : Unit ⊕ Unit → MvPowerSeries Unit O))
    (formalIntercept_eq_inr W)
  rw [← coe_substAlgHom (hasSubst_invPair W)] at h
  simp only [map_mul, map_sub] at h
  simp only [coe_substAlgHom (hasSubst_invPair W), subst_invPair_toMvPowerSeries_inr,
    subst_X (hasSubst_invPair W)] at h
  have h1 : (Sum.elim X (fun _ ↦ formalInverse W) :
      Unit ⊕ Unit → MvPowerSeries Unit O) (Sum.inr ()) = formalInverse W := rfl
  rw [h1] at h
  exact h

/-- The third root at the pair `(z, ι(z))` vanishes at the origin, so it may itself be
substituted into a one-variable series. -/
private theorem constantCoeff_subst_invPair_formalThirdRoot :
    constantCoeff (subst (Sum.elim X (fun _ ↦ formalInverse W) :
      Unit ⊕ Unit → MvPowerSeries Unit O) (formalThirdRoot W)) = 0 :=
  constantCoeff_subst_eq_zero (hasSubst_invPair W)
    (by rintro (j | j); exacts [constantCoeff_X j, constantCoeff_formalInverse W])
    (constantCoeff_formalThirdRoot W)

/-- Vieta's denominator, read at the pair `(z, ι(z))`, is still a unit: it times its
`invOfUnit` is `1`. -/
private theorem subst_invPair_thirdRootDenom_mul :
    (1 + C W.a₂ * subst (Sum.elim X (fun _ ↦ formalInverse W) :
          Unit ⊕ Unit → MvPowerSeries Unit O) (formalSlope W) +
        C W.a₄ * subst (Sum.elim X (fun _ ↦ formalInverse W) :
          Unit ⊕ Unit → MvPowerSeries Unit O) (formalSlope W) ^ 2 +
        C W.a₆ * subst (Sum.elim X (fun _ ↦ formalInverse W) :
          Unit ⊕ Unit → MvPowerSeries Unit O) (formalSlope W) ^ 3) *
      subst (Sum.elim X (fun _ ↦ formalInverse W) : Unit ⊕ Unit → MvPowerSeries Unit O)
        (invOfUnit (1 + C W.a₂ * formalSlope W + C W.a₄ * formalSlope W ^ 2 +
          C W.a₆ * formalSlope W ^ 3) 1) = 1 := by
  have h := congrArg (substAlgHom (hasSubst_invPair W))
    (mul_invOfUnit (1 + C W.a₂ * formalSlope W + C W.a₄ * formalSlope W ^ 2 +
      C W.a₆ * formalSlope W ^ 3) 1 (constantCoeff_formalThirdRootDenom W))
  simp only [map_mul, map_add, map_one, map_pow] at h
  simp only [coe_substAlgHom (hasSubst_invPair W), subst_C] at h
  exact h

/-- The defining relation of the third root at the pair `(z, ι(z))`, with the inverse of
Vieta's denominator eliminated. -/
private theorem subst_invPair_formalThirdRoot_relation :
    (1 + C W.a₂ * subst (Sum.elim X (fun _ ↦ formalInverse W) :
          Unit ⊕ Unit → MvPowerSeries Unit O) (formalSlope W) +
        C W.a₄ * subst (Sum.elim X (fun _ ↦ formalInverse W) :
          Unit ⊕ Unit → MvPowerSeries Unit O) (formalSlope W) ^ 2 +
        C W.a₆ * subst (Sum.elim X (fun _ ↦ formalInverse W) :
          Unit ⊕ Unit → MvPowerSeries Unit O) (formalSlope W) ^ 3) *
      (subst (Sum.elim X (fun _ ↦ formalInverse W) :
          Unit ⊕ Unit → MvPowerSeries Unit O) (formalThirdRoot W) + X () + formalInverse W) =
      -(C W.a₁ * subst (Sum.elim X (fun _ ↦ formalInverse W) :
            Unit ⊕ Unit → MvPowerSeries Unit O) (formalSlope W) +
        C W.a₂ * subst (Sum.elim X (fun _ ↦ formalInverse W) :
            Unit ⊕ Unit → MvPowerSeries Unit O) (formalIntercept W) +
        C W.a₃ * subst (Sum.elim X (fun _ ↦ formalInverse W) :
            Unit ⊕ Unit → MvPowerSeries Unit O) (formalSlope W) ^ 2 +
        2 * C W.a₄ * subst (Sum.elim X (fun _ ↦ formalInverse W) :
            Unit ⊕ Unit → MvPowerSeries Unit O) (formalSlope W) *
          subst (Sum.elim X (fun _ ↦ formalInverse W) :
            Unit ⊕ Unit → MvPowerSeries Unit O) (formalIntercept W) +
        3 * C W.a₆ * subst (Sum.elim X (fun _ ↦ formalInverse W) :
            Unit ⊕ Unit → MvPowerSeries Unit O) (formalSlope W) ^ 2 *
          subst (Sum.elim X (fun _ ↦ formalInverse W) :
            Unit ⊕ Unit → MvPowerSeries Unit O) (formalIntercept W)) := by
  have hexp := congrArg (substAlgHom (hasSubst_invPair W)) (formalThirdRoot_def W)
  simp only [map_sub, map_neg, map_mul, map_add, map_pow, map_ofNat] at hexp
  simp only [coe_substAlgHom (hasSubst_invPair W), subst_X (hasSubst_invPair W), subst_C] at hexp
  have h1 : (Sum.elim X (fun _ ↦ formalInverse W) :
      Unit ⊕ Unit → MvPowerSeries Unit O) (Sum.inr ()) = formalInverse W := rfl
  have h2 : (Sum.elim X (fun _ ↦ formalInverse W) :
      Unit ⊕ Unit → MvPowerSeries Unit O) (Sum.inl ()) = X () := rfl
  rw [h1, h2] at hexp
  have hAd := subst_invPair_thirdRootDenom_mul W
  set Lp := subst (Sum.elim X (fun _ ↦ formalInverse W) :
    Unit ⊕ Unit → MvPowerSeries Unit O) (formalSlope W)
  set Np := subst (Sum.elim X (fun _ ↦ formalInverse W) :
    Unit ⊕ Unit → MvPowerSeries Unit O) (formalIntercept W)
  set Tp := subst (Sum.elim X (fun _ ↦ formalInverse W) :
    Unit ⊕ Unit → MvPowerSeries Unit O) (formalThirdRoot W)
  set dp := subst (Sum.elim X (fun _ ↦ formalInverse W) :
    Unit ⊕ Unit → MvPowerSeries Unit O)
    (invOfUnit (1 + C W.a₂ * formalSlope W + C W.a₄ * formalSlope W ^ 2 +
      C W.a₆ * formalSlope W ^ 3) 1)
  clear_value Lp Np Tp dp
  linear_combination (1 + C W.a₂ * Lp + C W.a₄ * Lp ^ 2 + C W.a₆ * Lp ^ 3) * hexp -
    (C W.a₁ * Lp + C W.a₂ * Np + C W.a₃ * Lp ^ 2 + 2 * C W.a₄ * Lp * Np +
      3 * C W.a₆ * Lp ^ 2 * Np) * hAd

/-- The on-line identity at the pair `(z, ι(z))`: reading the `w`-expansion at the third root
gives the chord line read there. -/
private theorem subst_invPair_online :
    subst (fun _ : Unit ↦ subst (Sum.elim X (fun _ ↦ formalInverse W) :
        Unit ⊕ Unit → MvPowerSeries Unit O) (formalThirdRoot W)) (formalW W) =
      subst (Sum.elim X (fun _ ↦ formalInverse W) :
          Unit ⊕ Unit → MvPowerSeries Unit O) (formalSlope W) *
        subst (Sum.elim X (fun _ ↦ formalInverse W) :
          Unit ⊕ Unit → MvPowerSeries Unit O) (formalThirdRoot W) +
        subst (Sum.elim X (fun _ ↦ formalInverse W) :
          Unit ⊕ Unit → MvPowerSeries Unit O) (formalIntercept W) := by
  have h := congrArg (substAlgHom (hasSubst_invPair W)) (subst_formalThirdRoot_formalW W)
  simp only [map_add, map_mul] at h
  simp only [coe_substAlgHom (hasSubst_invPair W)] at h
  rwa [subst_comp_subst_apply (hasSubst_formalThirdRoot W) (hasSubst_invPair W)] at h

/-- **The chord through a point and its formal inverse passes through the origin**, in the form
that holds over any base: the intercept at the pair `(z, ι(z))`, multiplied by `ι(z) - z`,
vanishes. Over a domain the second factor is nonzero, and the intercept itself vanishes. -/
private theorem subst_invPair_formalIntercept_mul :
    subst (Sum.elim X (fun _ ↦ formalInverse W) : Unit ⊕ Unit → MvPowerSeries Unit O)
        (formalIntercept W) * (formalInverse W - X ()) = 0 := by
  have hi₁ := subst_invPair_formalIntercept_eq_inl W
  have hi₂ := subst_invPair_formalIntercept_eq_inr W
  -- `PowerSeries.X` is `MvPowerSeries.X ()`: defeq, but not syntactically equal, so this is
  -- `formalInverse_def` restated in the spelling `linear_combination` will normalize against.
  have hd : formalInverse W = -(X () * PowerSeries.invOfUnit (formalInverseDenom W) 1) :=
    formalInverse_def W
  linear_combination formalInverse W * hi₁ - X () * hi₂ + formalW W * hd

/-! ### The formal inverse is not the identity -/

/-- **The formal inverse is not the identity** when `2 ≠ 0`: the linear coefficient of `ι` is
`-1`, while that of `z` is `1`. This discharges the nondegeneracy the chord argument needs, so
neither of the two results below has to carry it as a hypothesis. -/
private theorem formalInverse_ne_X (h2 : (2 : O) ≠ 0) : formalInverse W ≠ X () := by
  intro h
  -- `PowerSeries.X` is `MvPowerSeries.X ()`: defeq, but not syntactically equal, so `h` is
  -- restated here in the one-variable spelling the coefficient lemmas are stated in.
  have h1 : PowerSeries.coeff 1 (formalInverse W) = PowerSeries.coeff 1 PowerSeries.X :=
    congrArg (PowerSeries.coeff 1) h
  rw [formalInverse_def, map_neg, PowerSeries.coeff_succ_X_mul,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.constantCoeff_invOfUnit,
    PowerSeries.coeff_one_X] at h1
  simp only [inv_one, Units.val_one] at h1
  exact h2 (by linear_combination -h1)

section Domain

variable [IsDomain O]

/-- Over a domain, if `ι ≠ z`, the intercept of the chord through a point and its formal inverse
vanishes: the chord is the vertical line through the two points. -/
private theorem subst_invPair_formalIntercept (hne : formalInverse W ≠ X ()) :
    subst (Sum.elim X (fun _ ↦ formalInverse W) : Unit ⊕ Unit → MvPowerSeries Unit O)
      (formalIntercept W) = 0 :=
  (mul_eq_zero.mp (subst_invPair_formalIntercept_mul W)).resolve_right (sub_ne_zero.mpr hne)

omit [IsDomain O] in
/-- The second branch of the factorization of Vieta's cubic is impossible.

If the cofactor vanished, the chord relation would force `w · (d + 1)` to be divisible by `z ^ 4`,
while `w = z ^ 3 · u` with `u` a unit; comparing the coefficient of `z ^ 3` gives `2 = 0`. -/
private theorem invPair_vieta_cofactor_absurd (h2 : (2 : O) ≠ 0)
    {Lp Tp : MvPowerSeries Unit O} (hTc : constantCoeff Tp = 0)
    (hslope : Lp * (formalInverse W - X ()) =
      -(formalW W * PowerSeries.invOfUnit (formalInverseDenom W) 1) - formalW W)
    (hrel : (1 + C W.a₂ * Lp + C W.a₄ * Lp ^ 2 + C W.a₆ * Lp ^ 3) *
        (Tp + X () + formalInverse W) =
      -(C W.a₁ * Lp + C W.a₂ * 0 + C W.a₃ * Lp ^ 2 + 2 * C W.a₄ * Lp * 0 +
        3 * C W.a₆ * Lp ^ 2 * 0))
    (hbranch : Lp - Tp ^ 2 - C W.a₁ * Lp * Tp - C W.a₂ * Lp * Tp ^ 2 - C W.a₃ * Lp ^ 2 * Tp -
      C W.a₄ * Lp ^ 2 * Tp ^ 2 - C W.a₆ * Lp ^ 3 * Tp ^ 2 = 0) : False := by
  set d := PowerSeries.invOfUnit (formalInverseDenom W) 1 with hddef
  have hd : formalInverse W = -(X () * d) := formalInverse_def W
  have hcontr : formalW W * (d + 1) =
      (1 + C W.a₂ * Lp + C W.a₄ * Lp ^ 2 + C W.a₆ * Lp ^ 3) * Tp *
        (X () + formalInverse W) * (formalInverse W - X ()) := by
    linear_combination hslope - (formalInverse W - X ()) * hbranch -
      (formalInverse W - X ()) * Tp * hrel
  have hdvd : (X () : MvPowerSeries Unit O) ^ 4 ∣
      (1 + C W.a₂ * Lp + C W.a₄ * Lp ^ 2 + C W.a₆ * Lp ^ 3) * Tp *
        (X () + formalInverse W) * (formalInverse W - X ()) := by
    have d1 : (X () : MvPowerSeries Unit O) ∣ Tp := PowerSeries.X_dvd_iff.mpr hTc
    have d2 : (X () : MvPowerSeries Unit O) ^ 2 ∣ X () + formalInverse W := by
      have h1d : (X () : MvPowerSeries Unit O) ∣ 1 - d :=
        PowerSeries.X_dvd_iff.mpr (by simp [hddef])
      obtain ⟨c, hc⟩ := h1d
      exact ⟨c, by rw [hd]; linear_combination X () * hc⟩
    have d3 : (X () : MvPowerSeries Unit O) ∣ formalInverse W - X () := ⟨-d - 1, by rw [hd]; ring⟩
    -- The three factors above carry `z`, `z ^ 2` and `z` respectively; split `z ^ 4` to match.
    have hsplit : (X () : MvPowerSeries Unit O) ^ 4 = X () * X () ^ 2 * X () := by ring
    rw [hsplit]
    exact mul_dvd_mul (mul_dvd_mul (Dvd.dvd.mul_left d1 _) d2) d3
  have h3 := congrArg (PowerSeries.coeff 3) hcontr
  rw [PowerSeries.X_pow_dvd_iff.mp hdvd 3 (by lia), formalW_eq_X_pow_mul_formalU,
    mul_assoc, PowerSeries.coeff_X_pow_mul'] at h3
  simp only [le_refl, ↓reduceIte, Nat.sub_self] at h3
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul, constantCoeff_formalU,
    map_add, map_one, one_mul, hddef, PowerSeries.constantCoeff_invOfUnit] at h3
  simp only [inv_one, Units.val_one] at h3
  exact h2 (by linear_combination h3)

/-- The third-root vanishing over a domain in which `2 ≠ 0`, the case the chord argument proves
directly. `subst_invPair_formalThirdRoot` descends it to an arbitrary commutative ring. -/
private theorem subst_invPair_formalThirdRoot_of_isDomain (h2 : (2 : O) ≠ 0) :
    subst (Sum.elim X (fun _ ↦ formalInverse W) : Unit ⊕ Unit → MvPowerSeries Unit O)
      (formalThirdRoot W) = 0 := by
  have hNp := subst_invPair_formalIntercept W (formalInverse_ne_X W h2)
  have hOL := subst_invPair_online W
  have hrel := subst_invPair_formalThirdRoot_relation W
  have hslope := subst_invPair_formalSlope_mul W
  have hTc := constantCoeff_subst_invPair_formalThirdRoot W
  have hfix := subst_formalW_wEquation W (PowerSeries.HasSubst.of_constantCoeff_zero hTc)
  rw [hNp, add_zero] at hOL
  rw [hNp] at hrel
  -- `wEquationRHS` is stated over an arbitrary algebra, so its constants arrive as `algebraMap`;
  -- on `MvPowerSeries Unit O` that map is `C`, the spelling the other hypotheses use.
  have hC : ∀ a : O, algebraMap O (MvPowerSeries Unit O) a = C a := fun _ ↦ rfl
  rw [wEquationRHS_def] at hfix
  simp only [hC] at hfix
  set Lp := subst (Sum.elim X (fun _ ↦ formalInverse W) :
    Unit ⊕ Unit → MvPowerSeries Unit O) (formalSlope W)
  set Tp := subst (Sum.elim X (fun _ ↦ formalInverse W) :
    Unit ⊕ Unit → MvPowerSeries Unit O) (formalThirdRoot W)
  -- `PowerSeries.subst a` is `MvPowerSeries.subst (fun _ ↦ a)`: defeq, but the two spellings are
  -- distinct atoms to `linear_combination`, so put both hypotheses in the same one.
  rw [show subst (fun _ : Unit ↦ Tp) (formalW W) = PowerSeries.subst Tp (formalW W) from rfl] at hOL
  set wT := PowerSeries.subst Tp (formalW W)
  have hTP : Tp * (Lp - Tp ^ 2 - C W.a₁ * Lp * Tp - C W.a₂ * Lp * Tp ^ 2 -
      C W.a₃ * Lp ^ 2 * Tp - C W.a₄ * Lp ^ 2 * Tp ^ 2 - C W.a₆ * Lp ^ 3 * Tp ^ 2) = 0 := by
    linear_combination hfix - (1 - C W.a₁ * Tp - C W.a₂ * Tp ^ 2 - C W.a₃ * (Lp * Tp + wT) -
      C W.a₄ * Tp * (Lp * Tp + wT) - C W.a₆ * (Lp ^ 2 * Tp ^ 2 + Lp * Tp * wT + wT ^ 2)) * hOL
  exact (mul_eq_zero.mp hTP).resolve_right
    fun hbranch ↦ invPair_vieta_cofactor_absurd W h2 hTc hslope hrel hbranch

end Domain

/-- **The third point of the chord through a point and its formal inverse is the origin**:
`z₃(z, ι(z)) = 0`.

The chord through `(z, w(z))` and its negative is the vertical line through them, which meets the
curve again only at the point at infinity.

The chord argument needs a domain in which `2 ≠ 0`; the identity itself needs neither, and is
obtained here by descent from the universal curve, whose base `ℤ[A₁, ⋯, A₆]` supplies both. -/
@[simp]
theorem subst_invPair_formalThirdRoot :
    subst (Sum.elim X (fun _ ↦ formalInverse W) : Unit ⊕ Unit → MvPowerSeries Unit O)
      (formalThirdRoot W) = 0 := by
  conv_lhs => rw [← W.map_specialize]
  rw [map_formalThirdRoot, map_formalInverse]
  have hfam : (Sum.elim X (fun _ ↦ PowerSeries.map W.specialize (formalInverse Universal.curve)) :
        Unit ⊕ Unit → MvPowerSeries Unit O) =
      fun i ↦ MvPowerSeries.map W.specialize
        (Sum.elim X (fun _ ↦ formalInverse Universal.curve) i) := by
    funext i
    -- `PowerSeries.map` is by definition `MvPowerSeries.map` at the one-element index type;
    -- unfolding it is what reconciles the two spellings in the `inr` branch.
    cases i <;> simp [PowerSeries.map]
  rw [hfam, ← MvPowerSeries.map_subst (hasSubst_invPair Universal.curve),
    subst_invPair_formalThirdRoot_of_isDomain Universal.curve two_ne_zero, map_zero]

/-- **The inverse law of the chord group law**: `F(z, ι(z)) = 0`.

The sum of a point and its formal inverse is the origin, so `formalInverse` is the inverse series
of `formalAdd`; with `rename_swap_formalAdd` it is a two-sided one. -/
@[simp]
theorem subst_invPair_formalAdd :
    subst (Sum.elim X (fun _ ↦ formalInverse W) : Unit ⊕ Unit → MvPowerSeries Unit O)
      (formalAdd W) = 0 := by
  rw [formalAdd_def, subst_comp_subst_apply (hasSubst_formalThirdRoot W) (hasSubst_invPair W)]
  -- The outer substitution is at the constant family `0`, by the third-root vanishing above.
  have hT : (fun _ : Unit ↦ subst (Sum.elim X (fun _ ↦ formalInverse W) :
        Unit ⊕ Unit → MvPowerSeries Unit O) (formalThirdRoot W)) =
      fun _ : Unit ↦ (0 : MvPowerSeries Unit O) :=
    funext fun _ ↦ subst_invPair_formalThirdRoot W
  rw [hT]
  exact PowerSeries.subst_zero_of_constantCoeff_zero (constantCoeff_formalInverse W)

end WeierstrassCurve
