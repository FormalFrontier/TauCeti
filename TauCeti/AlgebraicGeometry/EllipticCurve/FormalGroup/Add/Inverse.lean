/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Add.Series
public import TauCeti.AlgebraicGeometry.EllipticCurve.Universal
import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Add.PairSubst

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
(`github.com/MichaelStollBayreuth/EllipticCurves`, Apache-2.0, `66889eada51a`),
`EllipticCurves/WeierstrassFormalGroup/GroupLaw.lean` lines 118-308, the section `Domain`, and
`EllipticCurves/WeierstrassFormalGroup/ThirdPoint.lean` lines 372-460, 501-577 and 630-653.

The source's `addSeries`, `thirdRootSeries`, `slopeSeries`, `interceptSeries`, `inverseSeries`,
`uSeries` and `wSeries` are `formalAdd`, `formalThirdRoot`, `formalSlope`, `formalIntercept`,
`formalInverse`, `formalInverseDenom` and `formalW` here, continuing the renaming this repository
applies to the rest of that development.

`FormalGroup/Add/PairSubst.lean` proves the chord identities for an arbitrary pair `(q₁, q₂)` of
series with vanishing constant coefficient; this module specializes them to the pair `(z, ι(z))`,
which is the case the formal inverse law needs.

The source's `subst_wSeries_ne_zero` is `subst_formalW_ne_zero` in `FormalGroup/Add/Assoc.lean`;
its `interceptSeries_ne_zero` and `X_pair_intercept_ne_zero` have no counterpart in this
repository.
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
  hasSubst_pair (constantCoeff_X ()) (constantCoeff_formalInverse W)

/-! ### The chord through a point and its formal inverse -/

/-- The pair `(z, ι(z))` written in the shape `FormalGroup/Add/PairSubst.lean` states its
identities in. `Sum.elim X` and `Sum.elim (fun _ ↦ X ())` are the same family — `Unit` has one
element — but only the second is syntactically an instance of the general `(q₁, q₂)` pattern, so
rewriting with this is what lets the specializations below be `exact` applications. -/
private theorem invPair_eq :
    (Sum.elim X (fun _ ↦ formalInverse W) : Unit ⊕ Unit → MvPowerSeries Unit O) =
      Sum.elim (fun _ ↦ (X () : MvPowerSeries Unit O)) (fun _ ↦ formalInverse W) :=
  funext fun j ↦ by rcases j with j | j <;> rfl

/-- The third root at the pair `(z, ι(z))` vanishes at the origin, so it may itself be
substituted into a one-variable series. -/
private theorem constantCoeff_subst_invPair_formalThirdRoot :
    constantCoeff (subst (Sum.elim X (fun _ ↦ formalInverse W) :
      Unit ⊕ Unit → MvPowerSeries Unit O) (formalThirdRoot W)) = 0 := by
  rw [invPair_eq]
  exact constantCoeff_subst_pair_formalThirdRoot W (constantCoeff_X ())
    (constantCoeff_formalInverse W)

/-- **The chord through a point and its formal inverse passes through the origin**, in the form
that holds over any base: the intercept at the pair `(z, ι(z))`, multiplied by `ι(z) - z`,
vanishes. Over a domain the second factor is nonzero, and the intercept itself vanishes. -/
private theorem subst_invPair_formalIntercept_mul :
    subst (Sum.elim X (fun _ ↦ formalInverse W) : Unit ⊕ Unit → MvPowerSeries Unit O)
        (formalIntercept W) * (formalInverse W - X ()) = 0 := by
  -- the two readings of the intercept, taken from `PairSubst` at `(z, ι(z))` and turned back
  -- into this module's spelling of the pair
  have hi₁ := subst_pair_formalIntercept_eq_inl W (constantCoeff_X ())
    (constantCoeff_formalInverse W)
  have hi₂ := subst_pair_formalIntercept_eq_inr W (constantCoeff_X ())
    (constantCoeff_formalInverse W)
  rw [← invPair_eq,
    show PowerSeries.subst (X () : MvPowerSeries Unit O) (formalW W) = formalW W from
      PowerSeries.X_subst (formalW W)] at hi₁
  rw [← invPair_eq, subst_formalInverse_formalW W] at hi₂
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
  -- the on-line identity, the third-root relation and the slope identity, taken from `PairSubst`
  -- at `(z, ι(z))` and turned back into this module's spelling of the pair
  have hOL := subst_pair_formalThirdRoot_formalW W (constantCoeff_X ())
    (constantCoeff_formalInverse W)
  have hrel := subst_pair_formalThirdRoot_relation W (constantCoeff_X ())
    (constantCoeff_formalInverse W)
  have hslope := subst_pair_formalSlope_mul W (constantCoeff_X ())
    (constantCoeff_formalInverse W)
  rw [← invPair_eq] at hOL hrel
  rw [← invPair_eq, subst_formalInverse_formalW W,
    show PowerSeries.subst (X () : MvPowerSeries Unit O) (formalW W) = formalW W from
      PowerSeries.X_subst (formalW W)] at hslope
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
