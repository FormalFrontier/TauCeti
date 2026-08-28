/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Chord
public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Inverse

/-!
# The formal addition series of a Weierstrass curve

The chord through the points with parameters `z₁` and `z₂` meets the curve a third time at
`WeierstrassCurve.formalThirdRoot W`. Negating that third point gives their sum, so substituting
the third-root series into `WeierstrassCurve.formalInverse W` defines the addition series
`WeierstrassCurve.formalAdd W`.

This file proves the properties of that series which do not require associativity: it is symmetric,
has zero constant coefficient, restricts to the identity on either coordinate axis, and has linear
coefficient `1` in each variable. Thus it supplies all the coefficient data required by Mathlib's
`FormalGroup` structure; associativity, and hence the bundled structure itself, is left to the
next stage of the elliptic formal-group construction.

## Main definitions

* `WeierstrassCurve.formalAdd`: the two-variable series giving addition near infinity.

## Main results

* `WeierstrassCurve.rename_swap_formalAdd`: the addition series is symmetric.
* `WeierstrassCurve.subst_inr_zero_formalAdd` and
  `WeierstrassCurve.subst_inl_zero_formalAdd`: adding zero on either side does nothing.
* `WeierstrassCurve.coeff_single_inl_formalAdd` and
  `WeierstrassCurve.coeff_single_inr_formalAdd`: both linear coefficients are `1`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1.

## Provenance

Adapted from Michael Stoll's `EllipticCurves` project
(`github.com/MichaelStollBayreuth/EllipticCurves`, Apache-2.0, pinned by
`TauCetiRoadmap/EllipticCurves/README.md` at `66889eada51a`),
`EllipticCurves/WeierstrassFormalGroup/Chord.lean`, from `addSeries` through
`coeff_single_inr_addSeries`. The source's `thirdRootSeries`, `inverseSeries`, and `addSeries`
are named `formalThirdRoot`, `formalInverse`, and `formalAdd` here, consistently with the
preceding files in this directory. The source's generic `ringHom_invOfUnit` is kept private at
its only use.
-/

public section

namespace WeierstrassCurve

open MvPowerSeries

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-! ### The addition series -/

/-- The formal addition series
`F(z₁, z₂) = ι(z₃(z₁, z₂))`, obtained by negating the third point of the chord. -/
noncomputable def formalAdd : MvPowerSeries (Unit ⊕ Unit) R :=
  subst (fun _ : Unit => formalThirdRoot W) (formalInverse W)

/-- The defining formula for `formalAdd`. -/
theorem formalAdd_def :
    formalAdd W = subst (fun _ : Unit => formalThirdRoot W) (formalInverse W) :=
  (rfl)

/-- The third-root series may be substituted into a power series. -/
theorem hasSubst_formalThirdRoot : HasSubst (fun _ : Unit => formalThirdRoot W) :=
  hasSubst_of_constantCoeff_zero fun _ => constantCoeff_formalThirdRoot W

/-- The addition series vanishes at the origin. -/
@[simp]
theorem constantCoeff_formalAdd : constantCoeff (formalAdd W) = 0 :=
  constantCoeff_subst_eq_zero (hasSubst_formalThirdRoot W)
    (fun _ => constantCoeff_formalThirdRoot W) (constantCoeff_formalInverse W)

/-- The formal addition series may be substituted into a power series. -/
theorem hasSubst_formalAdd : HasSubst (fun _ : Unit => formalAdd W) :=
  hasSubst_of_constantCoeff_zero fun _ => constantCoeff_formalAdd W

/-- The addition series is unchanged when its two parameters are exchanged. -/
theorem rename_swap_formalAdd : rename Sum.swap (formalAdd W) = formalAdd W := by
  rw [formalAdd_def, rename_eq_subst,
    subst_comp_subst_apply (hasSubst_formalThirdRoot W) (HasSubst.X_comp _)]
  congr 1
  funext u
  rw [← rename_eq_subst, rename_swap_formalThirdRoot]

/-! ### Adding zero -/

private theorem hasSubst_inr_zero :
    HasSubst (Sum.elim X (fun _ => 0) : Unit ⊕ Unit → MvPowerSeries Unit R) :=
  hasSubst_of_constantCoeff_zero (by rintro (j | j) <;> simp)

private theorem subst_inr_zero_formalW_inl :
    subst (Sum.elim X (fun _ => 0) : Unit ⊕ Unit → MvPowerSeries Unit R)
      ((formalW W).toMvPowerSeries (Sum.inl ())) = formalW W := by
  rw [PowerSeries.subst_toMvPowerSeries (hasSubst_inr_zero (R := R))]
  exact PowerSeries.X_subst (formalW W)

private theorem subst_inr_zero_formalW_inr :
    subst (Sum.elim X (fun _ => 0) : Unit ⊕ Unit → MvPowerSeries Unit R)
      ((formalW W).toMvPowerSeries (Sum.inr ())) = 0 := by
  rw [PowerSeries.subst_toMvPowerSeries (hasSubst_inr_zero (R := R))]
  exact subst_zero_of_constantCoeff_zero (constantCoeff_formalW W)

private theorem X_mul_subst_inr_zero_formalSlope :
    (PowerSeries.X : PowerSeries R) *
      subst (Sum.elim X (fun _ => 0)) (formalSlope W) = formalW W := by
  have h := congrArg
    (subst (Sum.elim X (fun _ => 0) : Unit ⊕ Unit → MvPowerSeries Unit R))
    (formalSlope_mul_sub W)
  rw [← coe_substAlgHom (hasSubst_inr_zero (R := R))] at h
  simp only [map_mul, map_sub, coe_substAlgHom, subst_inr_zero_formalW_inl,
    subst_inr_zero_formalW_inr, subst_X (hasSubst_inr_zero (R := R))] at h
  have hr : (Sum.elim X (fun _ => 0) : Unit ⊕ Unit → MvPowerSeries Unit R)
      (Sum.inr ()) = 0 := rfl
  have hl : (Sum.elim X (fun _ => 0) : Unit ⊕ Unit → MvPowerSeries Unit R)
      (Sum.inl ()) = PowerSeries.X := rfl
  rw [hr, hl] at h
  linear_combination -h

private theorem subst_inr_zero_formalIntercept :
    subst (Sum.elim X (fun _ => 0) : Unit ⊕ Unit → MvPowerSeries Unit R)
      (formalIntercept W) = 0 := by
  rw [formalIntercept_def, ← coe_substAlgHom (hasSubst_inr_zero (R := R)), map_sub, map_mul]
  simp only [coe_substAlgHom, subst_inr_zero_formalW_inl,
    subst_X (hasSubst_inr_zero (R := R))]
  have hl : (Sum.elim X (fun _ => 0) : Unit ⊕ Unit → MvPowerSeries Unit R)
      (Sum.inl ()) = PowerSeries.X := rfl
  rw [hl]
  linear_combination -(X_mul_subst_inr_zero_formalSlope W)

/-- A ring homomorphism preserving the constant coefficient of a unit series preserves its
`invOfUnit`. This is private proof plumbing for the specialization of `formalThirdRoot`. -/
private theorem map_invOfUnit {R' : Type*} [CommRing R'] {σ τ : Type*} {F : Type*}
    [FunLike F (MvPowerSeries σ R) (MvPowerSeries τ R')]
    [RingHomClass F (MvPowerSeries σ R) (MvPowerSeries τ R')] (f : F)
    {D : MvPowerSeries σ R} (hD : constantCoeff D = 1)
    (hD' : constantCoeff (f D) = 1) :
    f (invOfUnit D 1) = invOfUnit (f D) 1 := by
  have h1 : f D * f (invOfUnit D 1) = 1 := by
    rw [← map_mul, mul_invOfUnit D 1 (by rw [hD]; rfl), map_one]
  have h2 : f D * invOfUnit (f D) 1 = 1 :=
    mul_invOfUnit _ 1 (by rw [hD']; rfl)
  calc
    f (invOfUnit D 1) = f (invOfUnit D 1) * (f D * invOfUnit (f D) 1) := by
      rw [h2, mul_one]
    _ = (f D * f (invOfUnit D 1)) * invOfUnit (f D) 1 := by ring
    _ = invOfUnit (f D) 1 := by rw [h1, one_mul]

/-- Specializing the second parameter of the third-root series to zero gives the formal inverse. -/
theorem subst_inr_zero_formalThirdRoot :
    subst (Sum.elim X (fun _ => 0) : Unit ⊕ Unit → MvPowerSeries Unit R)
      (formalThirdRoot W) = formalInverse W := by
  -- First specialize the slope and derive its fixed-point equation from the Weierstrass equation.
  set L : PowerSeries R :=
    subst (Sum.elim X (fun _ => 0) : Unit ⊕ Unit → MvPowerSeries Unit R)
      (formalSlope W) with hL
  have hXL : PowerSeries.X * L = formalW W := X_mul_subst_inr_zero_formalSlope W
  have hLfix : L = PowerSeries.X ^ 2 + PowerSeries.C W.a₁ * PowerSeries.X * L +
      PowerSeries.C W.a₂ * PowerSeries.X ^ 2 * L +
      PowerSeries.C W.a₃ * PowerSeries.X * L ^ 2 +
      PowerSeries.C W.a₄ * PowerSeries.X ^ 2 * L ^ 2 +
      PowerSeries.C W.a₆ * PowerSeries.X ^ 2 * L ^ 3 := by
    refine PowerSeries.X_mul_cancel ?_
    rw [hXL]
    conv_lhs => rw [formalW_wEquation W]
    rw [← hXL]
    rw [wEquationRHS_powerSeries]
    ring
  have hL0 : PowerSeries.constantCoeff L = 0 := by
    have h := congrArg PowerSeries.constantCoeff hLfix
    simpa [pow_two] using h
  -- Next identify the specialized denominator and commute its formal inverse with substitution.
  set D : MvPowerSeries (Unit ⊕ Unit) R :=
    1 + C W.a₂ * formalSlope W + C W.a₄ * formalSlope W ^ 2 +
      C W.a₆ * formalSlope W ^ 3 with hD
  have hDsub : subst
      (Sum.elim X (fun _ => 0) : Unit ⊕ Unit → MvPowerSeries Unit R) D =
      1 + PowerSeries.C W.a₂ * L + PowerSeries.C W.a₄ * L ^ 2 +
        PowerSeries.C W.a₆ * L ^ 3 := by
    rw [hD, ← coe_substAlgHom (hasSubst_inr_zero (R := R))]
    simp only [map_add, map_mul, map_pow, map_one, coe_substAlgHom,
      subst_C]
    rfl
  have hD1 : constantCoeff D = 1 := by simp [hD]
  have hD1' : PowerSeries.constantCoeff
      (1 + PowerSeries.C W.a₂ * L + PowerSeries.C W.a₄ * L ^ 2 +
        PowerSeries.C W.a₆ * L ^ 3) = 1 := by
    simp [hL0]
  have hInv : subst
      (Sum.elim X (fun _ => 0) : Unit ⊕ Unit → MvPowerSeries Unit R)
      (invOfUnit D 1) =
      invOfUnit (1 + PowerSeries.C W.a₂ * L + PowerSeries.C W.a₄ * L ^ 2 +
        PowerSeries.C W.a₆ * L ^ 3) 1 := by
    have h := map_invOfUnit (R' := R) (substAlgHom (hasSubst_inr_zero (R := R))) hD1
      (by rw [coe_substAlgHom, hDsub]; exact hD1')
    rwa [coe_substAlgHom, hDsub] at h
  -- Expanding the third-root formula now expresses the specialization solely in terms of `L`.
  have hexp : subst
      (Sum.elim X (fun _ => 0) : Unit ⊕ Unit → MvPowerSeries Unit R)
      (formalThirdRoot W) = -PowerSeries.X -
      (PowerSeries.C W.a₁ * L + PowerSeries.C W.a₃ * L ^ 2) *
        invOfUnit (1 + PowerSeries.C W.a₂ * L + PowerSeries.C W.a₄ * L ^ 2 +
          PowerSeries.C W.a₆ * L ^ 3) 1 := by
    rw [formalThirdRoot_def, ← hD, ← coe_substAlgHom (hasSubst_inr_zero (R := R))]
    simp only [map_sub, map_neg, map_add, map_mul, map_pow, map_ofNat,
      coe_substAlgHom, subst_C, subst_X (hasSubst_inr_zero (R := R)), hInv,
      subst_inr_zero_formalIntercept,
      -- `PowerSeries R` abbreviates `MvPowerSeries Unit R`, and its `C` is definitionally the
      -- multivariate constant-series hom; Mathlib has no separate conversion lemma to apply here.
      show (MvPowerSeries.C : R →+* MvPowerSeries Unit R) = PowerSeries.C from rfl]
    have hr : (Sum.elim X (fun _ => 0) : Unit ⊕ Unit → MvPowerSeries Unit R)
        (Sum.inr ()) = 0 := rfl
    have hl : (Sum.elim X (fun _ => 0) : Unit ⊕ Unit → MvPowerSeries Unit R)
        (Sum.inl ()) = PowerSeries.X := rfl
    rw [hr, hl]
    rw [← hL]
    ring
  rw [hexp]
  -- Finally clear the two unit denominators and discharge the resulting polynomial identity
  -- with the slope fixed-point equation.
  set d : PowerSeries R := invOfUnit
    (1 + PowerSeries.C W.a₂ * L + PowerSeries.C W.a₄ * L ^ 2 +
      PowerSeries.C W.a₆ * L ^ 3) 1 with hd
  have hUnit2 : (1 + PowerSeries.C W.a₂ * L + PowerSeries.C W.a₄ * L ^ 2 +
      PowerSeries.C W.a₆ * L ^ 3) * d = 1 :=
    mul_invOfUnit _ 1 (by exact_mod_cast hD1')
  have hUnit1 := mul_invOfUnit_formalInverseDenom W
  clear_value L d
  refine ((isUnit_formalInverseDenom W).mul (IsUnit.of_mul_eq_one _ hUnit2)).mul_left_cancel ?_
  rw [formalInverse_def]
  rw [formalInverseDenom_def] at hUnit1 ⊢
  rw [← hXL] at hUnit1 ⊢
  linear_combination
    ((1 + PowerSeries.C W.a₂ * L + PowerSeries.C W.a₄ * L ^ 2 +
      PowerSeries.C W.a₆ * L ^ 3) * PowerSeries.X) * hUnit1 -
    ((1 - PowerSeries.C W.a₁ * PowerSeries.X - PowerSeries.C W.a₃ *
      (PowerSeries.X * L)) * (PowerSeries.C W.a₁ * L + PowerSeries.C W.a₃ * L ^ 2)) *
      hUnit2 - (PowerSeries.C W.a₁ + PowerSeries.C W.a₃ * L) * hLfix

/-- Adding zero in the second parameter does nothing. -/
@[simp]
theorem subst_inr_zero_formalAdd :
    subst (Sum.elim X (fun _ => 0) : Unit ⊕ Unit → MvPowerSeries Unit R)
      (formalAdd W) = PowerSeries.X := by
  rw [formalAdd_def,
    subst_comp_subst_apply (hasSubst_formalThirdRoot W) (hasSubst_inr_zero (R := R))]
  have h : (fun _ : Unit => subst
      (Sum.elim X (fun _ => 0) : Unit ⊕ Unit → MvPowerSeries Unit R)
      (formalThirdRoot W)) = fun _ : Unit => (formalInverse W : MvPowerSeries Unit R) := by
    funext u
    exact subst_inr_zero_formalThirdRoot W
  rw [h]
  exact subst_formalInverse_self W

private theorem hasSubst_inl_zero :
    HasSubst (Sum.elim (fun _ => 0) X : Unit ⊕ Unit → MvPowerSeries Unit R) :=
  hasSubst_of_constantCoeff_zero (by rintro (j | j) <;> simp)

/-- Adding zero in the first parameter does nothing. -/
@[simp]
theorem subst_inl_zero_formalAdd :
    subst (Sum.elim (fun _ => 0) X : Unit ⊕ Unit → MvPowerSeries Unit R)
      (formalAdd W) = PowerSeries.X := by
  conv_lhs => rw [← rename_swap_formalAdd W]
  rw [rename_eq_subst,
    subst_comp_subst_apply (HasSubst.X_comp _) (hasSubst_inl_zero (R := R))]
  have h : (fun s : Unit ⊕ Unit => subst
      (Sum.elim (fun _ => 0) X : Unit ⊕ Unit → MvPowerSeries Unit R)
      ((X ∘ Sum.swap : Unit ⊕ Unit → MvPowerSeries (Unit ⊕ Unit) R) s)) =
      (Sum.elim X (fun _ => 0) : Unit ⊕ Unit → MvPowerSeries Unit R) := by
    funext s
    rw [Function.comp_apply, subst_X (hasSubst_inl_zero (R := R))]
    match s with
    | .inl () => rfl
    | .inr () => rfl
  rw [h]
  exact subst_inr_zero_formalAdd W

/-! ### Linear coefficients -/

private theorem coeff_single_eq_one_of_subst_eq_X {f : MvPowerSeries (Unit ⊕ Unit) R}
    {s₀ : Unit ⊕ Unit} {fam : Unit ⊕ Unit → MvPowerSeries Unit R}
    (hfam₀ : fam s₀ = X ()) (hfam : ∀ s ≠ s₀, fam s = 0)
    (hsubst : subst fam f = PowerSeries.X) : coeff (Finsupp.single s₀ 1) f = 1 := by
  have hS : HasSubst fam := by
    refine hasSubst_of_constantCoeff_zero fun s => ?_
    rcases eq_or_ne s s₀ with rfl | h
    · rw [hfam₀]
      exact constantCoeff_X ()
    · rw [hfam s h, map_zero]
  have h := congrArg (coeff (Finsupp.single () 1)) hsubst
  -- `PowerSeries R` is the abbreviation `MvPowerSeries Unit R`, under which the two `X`
  -- constants are definitionally equal; no coercion or wrapper theorem is available or needed.
  rw [coeff_subst hS, show (PowerSeries.X : PowerSeries R) = X () from rfl,
    coeff_X, ite_eq_left rfl] at h
  rw [finsum_eq_single _ (Finsupp.single s₀ 1) (fun d hd => ?_)] at h
  · rwa [Finsupp.prod_single_index (h := fun s e => fam s ^ e) (pow_zero _), hfam₀,
      pow_one, coeff_X, ite_eq_left rfl, smul_eq_mul, mul_one] at h
  · rcases Classical.em (∃ s ≠ s₀, d s ≠ 0) with ⟨s, hs, hds⟩ | hd0
    · rw [Finsupp.prod, Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hds)
        (by rw [hfam s hs, zero_pow hds]), map_zero, smul_zero]
    · push Not at hd0
      have hd' : d = Finsupp.single s₀ (d s₀) := Finsupp.ext fun u => by
        rcases eq_or_ne u s₀ with rfl | hu
        · rw [Finsupp.single_eq_same]
        · simp [hd0 u hu, Ne.symm hu]
      have hne1 : d s₀ ≠ 1 := fun h1 => hd (by rw [hd', h1])
      rw [hd', Finsupp.prod_single_index (h := fun s e => fam s ^ e) (pow_zero _), hfam₀,
        X_pow_eq () (d s₀), coeff_monomial,
        ite_eq_right (by simpa using fun h => absurd h.symm hne1), smul_zero]

/-- The linear coefficient of the addition series in the first variable is `1`. -/
@[simp]
theorem coeff_single_inl_formalAdd :
    coeff (Finsupp.single (Sum.inl ()) 1) (formalAdd W) = 1 :=
  coeff_single_eq_one_of_subst_eq_X rfl
    (fun s h => by
      rcases s with u | u
      · exact absurd rfl h
      · rfl)
    (subst_inr_zero_formalAdd W)

/-- The linear coefficient of the addition series in the second variable is `1`. -/
@[simp]
theorem coeff_single_inr_formalAdd :
    coeff (Finsupp.single (Sum.inr ()) 1) (formalAdd W) = 1 :=
  coeff_single_eq_one_of_subst_eq_X rfl
    (fun s h => by
      rcases s with u | u
      · rfl
      · exact absurd rfl h)
    (subst_inl_zero_formalAdd W)

end WeierstrassCurve
