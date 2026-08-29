/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Add.Series
import TauCeti.RingTheory.MvPowerSeries.Rename

/-!
# The unit laws and the linear part of the chord group law

`FormalGroup/Add/Series.lean` produces `formalAdd`, the series `F(z₁, z₂) = ι(z₃(z₁, z₂))` of the
chord construction. This file records what `F` does at the origin and in lowest degree: the two
unit laws `F(z, 0) = z` and `F(0, z) = z`, and the fact that `F(z₁, z₂) = z₁ + z₂` up to terms of
total degree at least two.

Together with `rename_swap_formalAdd`, already in `Add/Series.lean`, the two unit laws are the
formal-group-law axioms for `formalAdd` apart from associativity. `constantCoeff_formalAdd` is not
one of those axioms: it supplies the `HasSubst` prerequisite that substituting `F` into a series
requires in the first place.

## Main results

* `WeierstrassCurve.subst_unitR_formalThirdRoot`: setting the second parameter to zero sends the
  third root of the chord to the formal inverse, `z₃(z, 0) = ι(z)`. Geometrically the chord
  through `P` and `O` meets the curve again at `-P`.
* `WeierstrassCurve.subst_unitR_formalAdd` and `WeierstrassCurve.subst_unitL_formalAdd`: the two
  **unit laws** `F(z, 0) = z` and `F(0, z) = z`.
* `WeierstrassCurve.coeff_single_inl_formalAdd` and
  `WeierstrassCurve.coeff_single_inr_formalAdd`: both linear coefficients of `F` are `1`.
* `WeierstrassCurve.coeff_formalAdd_sub_eq_zero_of_degree_lt`: below total degree two, `F` agrees
  with `z₁ + z₂`.

## Implementation notes

The two specializations are substitutions of the families `Sum.elim X (fun _ ↦ 0)` and
`Sum.elim (fun _ ↦ 0) X`, written inline throughout rather than named: they appear only in this
file, and naming them would add a definition whose unfolding lemma every proof would then have to
carry.

Only the right-hand unit law is proved directly. The left-hand one follows from it and the
swap-invariance `rename_swap_formalAdd`, which is why this file needs no separate analysis of the
chord in the second variable.

One-variable series are viewed in a single parameter of the pair through
`PowerSeries.toMvPowerSeries`, the spelling `Chord.lean` and `TauCeti/RingTheory/MvPowerSeries/`
`Equiv.lean` already use, rather than through `MvPowerSeries.rename (fun _ ↦ s)`. The two are
definitionally equal (`PowerSeries.toMvPowerSeries_apply`), and the proofs below cross between
them where the `rename` API is the more convenient of the two.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1.

## Provenance

Adapted from Michael Stoll's `EllipticCurves` project
(`github.com/MichaelStollBayreuth/EllipticCurves`, Apache-2.0, pinned by
`TauCetiRoadmap/EllipticCurves/README.md` at `66889eada51a`),
`EllipticCurves/WeierstrassFormalGroup/Chord.lean` lines 576-870, the section `AddZero` —
declarations `hasSubst_unitR`, `subst_unitR_renameL`, `subst_unitR_renameR`,
`X_mul_subst_unitR_slopeSeries`, `subst_unitR_interceptSeries`, `ringHom_invOfUnit`,
`subst_unitR_thirdRootSeries`, `subst_unitR_addSeries`, `hasSubst_unitL`,
`subst_unitL_addSeries`, `coeff_single_eq_one_of_subst_eq_X`, `coeff_single_inl_addSeries`,
`coeff_single_inr_addSeries`, `degree_two_var` and `coeff_addSeries_sub_of_degree_lt`.

The source's `addSeries`, `thirdRootSeries`, `slopeSeries`, `interceptSeries`, `inverseSeries`,
`uSeries` and `wSeries` are `formalAdd`, `formalThirdRoot`, `formalSlope`, `formalIntercept`,
`formalInverse`, `formalInverseDenom` and `formalW` here, continuing the renaming this repository
applies to the rest of that file. The source's `rename (fun _ ↦ s)` spelling is replaced by
`PowerSeries.toMvPowerSeries s` throughout, as elsewhere in `FormalGroup/`.

The source's private `ringHom_invOfUnit` is not ported. It carries no elliptic content, and the
general statement now lives in a general file as `MvPowerSeries.ringHom_invOfUnit`, which this file
uses directly.
-/

public section

namespace WeierstrassCurve

open MvPowerSeries

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-! ### Setting the second parameter to zero -/

/-- Substituting `X` for the first parameter and `0` for the second is a legitimate
substitution: both series have zero constant coefficient. -/
private theorem hasSubst_unitR :
    HasSubst (Sum.elim X (fun _ ↦ 0) : Unit ⊕ Unit → MvPowerSeries Unit R) :=
  hasSubst_of_constantCoeff_zero (by rintro (j | j) <;> simp)

/-- The `w`-expansion in the first parameter survives the specialization. -/
private theorem subst_unitR_toMvPowerSeries_inl :
    subst (Sum.elim X (fun _ ↦ 0) : Unit ⊕ Unit → MvPowerSeries Unit R)
      ((formalW W).toMvPowerSeries (Sum.inl ())) = formalW W := by
  rw [PowerSeries.subst_toMvPowerSeries hasSubst_unitR, Sum.elim_inl]
  -- the residue is `subst (X ()) w`; `PowerSeries.X` is `MvPowerSeries.X ()`, defeq but not
  -- syntactically equal, so this closes by `exact` rather than by another `rw`.
  exact PowerSeries.X_subst (formalW W)

/-- The `w`-expansion in the second parameter is killed by the specialization. -/
private theorem subst_unitR_toMvPowerSeries_inr :
    subst (Sum.elim X (fun _ ↦ 0) : Unit ⊕ Unit → MvPowerSeries Unit R)
      ((formalW W).toMvPowerSeries (Sum.inr ())) = 0 := by
  rw [PowerSeries.subst_toMvPowerSeries hasSubst_unitR, Sum.elim_inr]
  -- `PowerSeries.` is explicit here: this file `open`s `MvPowerSeries`, whose namesake lemma is
  -- about `MvPowerSeries.subst` and does not match the `PowerSeries.subst` goal.
  exact PowerSeries.subst_zero_of_constantCoeff_zero (constantCoeff_formalW W)

/-- The specialized slope still satisfies the defining relation of the slope, in the form
`z * λ(z, 0) = w(z)`. -/
private theorem X_mul_subst_unitR_formalSlope :
    (PowerSeries.X : PowerSeries R) *
      subst (Sum.elim X (fun _ ↦ 0)) (formalSlope W) = formalW W := by
  have h := congrArg (subst
    (Sum.elim X (fun _ ↦ 0) : Unit ⊕ Unit → MvPowerSeries Unit R)) (formalSlope_mul_sub W)
  rw [← coe_substAlgHom hasSubst_unitR] at h
  simp only [map_mul, map_sub] at h
  simp only [coe_substAlgHom hasSubst_unitR, subst_unitR_toMvPowerSeries_inl,
    subst_unitR_toMvPowerSeries_inr, subst_X hasSubst_unitR] at h
  have h1 : (Sum.elim X (fun _ ↦ 0) : Unit ⊕ Unit → MvPowerSeries Unit R) (Sum.inr ()) = 0 := rfl
  have h2 : (Sum.elim X (fun _ ↦ 0) : Unit ⊕ Unit → MvPowerSeries Unit R) (Sum.inl ()) =
      PowerSeries.X := rfl
  rw [h1, h2] at h
  linear_combination -h

/-- The chord through a point and the origin has vanishing intercept: its equation in the
`(z, w)` chart is `w = λz`, so it passes through the origin. -/
private theorem subst_unitR_formalIntercept :
    subst (Sum.elim X (fun _ ↦ 0) : Unit ⊕ Unit → MvPowerSeries Unit R)
      (formalIntercept W) = 0 := by
  rw [formalIntercept_def, ← coe_substAlgHom hasSubst_unitR, map_sub, map_mul]
  simp only [coe_substAlgHom hasSubst_unitR, subst_unitR_toMvPowerSeries_inl,
    subst_X hasSubst_unitR]
  have h2 : (Sum.elim X (fun _ ↦ 0) : Unit ⊕ Unit → MvPowerSeries Unit R) (Sum.inl ()) =
      PowerSeries.X := rfl
  rw [h2]
  linear_combination -X_mul_subst_unitR_formalSlope W

/-! ### The third point of a chord through the origin -/

/-- **The `z`-cancelled `w`-equation.** If `z · L = w(z)` then `L` satisfies the equation obtained
from the `w`-equation by cancelling one factor of `z`. This is the coefficient identity the
third-root comparison runs on, and the only place the `w`-equation enters this file. -/
private theorem wEquation_of_X_mul {L : PowerSeries R}
    (hXL : PowerSeries.X * L = formalW W) :
    L = PowerSeries.X ^ 2 + PowerSeries.C W.a₁ * PowerSeries.X * L +
      PowerSeries.C W.a₂ * PowerSeries.X ^ 2 * L + PowerSeries.C W.a₃ * PowerSeries.X * L ^ 2 +
      PowerSeries.C W.a₄ * PowerSeries.X ^ 2 * L ^ 2 +
      PowerSeries.C W.a₆ * PowerSeries.X ^ 2 * L ^ 3 := by
  refine PowerSeries.X_mul_cancel ?_
  rw [hXL]
  conv_lhs => rw [formalW_wEquation W, wEquationRHS_powerSeries]
  rw [← hXL]
  ring

/-- **The substituted third root, expanded.** Setting the second parameter to zero sends
`formalThirdRoot` to `-z` minus the `a₁`/`a₃` numerator over the specialized denominator: every
term of the numerator carrying `formalIntercept` vanishes, because the intercept of a chord through
the origin is zero. `L` is the specialized slope. -/
private theorem subst_unitR_formalThirdRoot_eq {L : PowerSeries R}
    (hL : subst (Sum.elim X (fun _ ↦ 0) : Unit ⊕ Unit → MvPowerSeries Unit R)
      (formalSlope W) = L)
    (hL0 : PowerSeries.constantCoeff L = 0) :
    subst (Sum.elim X (fun _ ↦ 0) : Unit ⊕ Unit → MvPowerSeries Unit R) (formalThirdRoot W) =
      -PowerSeries.X - (PowerSeries.C W.a₁ * L + PowerSeries.C W.a₃ * L ^ 2) *
        invOfUnit (1 + PowerSeries.C W.a₂ * L + PowerSeries.C W.a₄ * L ^ 2 +
          PowerSeries.C W.a₆ * L ^ 3) 1 := by
  set D : MvPowerSeries (Unit ⊕ Unit) R := 1 + C W.a₂ * formalSlope W +
    C W.a₄ * formalSlope W ^ 2 + C W.a₆ * formalSlope W ^ 3 with hD
  have hDsub : subst (Sum.elim X (fun _ ↦ 0) : Unit ⊕ Unit → MvPowerSeries Unit R) D =
      1 + PowerSeries.C W.a₂ * L + PowerSeries.C W.a₄ * L ^ 2 + PowerSeries.C W.a₆ * L ^ 3 := by
    rw [hD, ← coe_substAlgHom hasSubst_unitR]
    simp only [map_add, map_mul, map_pow, map_one]
    rw [coe_substAlgHom hasSubst_unitR]
    simp only [subst_C, ← PowerSeries.C_apply, hL]
  have hD1 : constantCoeff D = 1 := by simp [hD]
  have hD1' : PowerSeries.constantCoeff
      (1 + PowerSeries.C W.a₂ * L + PowerSeries.C W.a₄ * L ^ 2 +
        PowerSeries.C W.a₆ * L ^ 3) = 1 := by
    simp [hL0]
  have hInv : subst (Sum.elim X (fun _ ↦ 0) : Unit ⊕ Unit → MvPowerSeries Unit R) (invOfUnit D 1) =
      invOfUnit (1 + PowerSeries.C W.a₂ * L + PowerSeries.C W.a₄ * L ^ 2 +
        PowerSeries.C W.a₆ * L ^ 3) 1 := by
    have h := MvPowerSeries.ringHom_invOfUnit (S := R) (u := 1) (v := 1)
      (substAlgHom hasSubst_unitR) hD1
      (by rw [coe_substAlgHom, hDsub]; exact hD1')
    rwa [coe_substAlgHom, hDsub] at h
  rw [formalThirdRoot_def, ← hD, ← coe_substAlgHom hasSubst_unitR]
  simp only [map_sub, map_neg, map_add, map_mul, map_pow, map_ofNat]
  rw [coe_substAlgHom hasSubst_unitR]
  simp only [subst_C, subst_X hasSubst_unitR, hInv, subst_unitR_formalIntercept, hL,
    ← PowerSeries.C_apply]
  have h1 : ((Sum.elim X (fun _ ↦ 0) : Unit ⊕ Unit → MvPowerSeries Unit R)) (Sum.inr ()) = 0 := rfl
  have h2 : ((Sum.elim X (fun _ ↦ 0) : Unit ⊕ Unit → MvPowerSeries Unit R))
      (Sum.inl ()) = PowerSeries.X := rfl
  rw [h1, h2]
  ring

/-- **Specializing the third root at the origin gives the formal inverse**: substituting `z` for
the first parameter and `0` for the second sends `formalThirdRoot` to `formalInverse`, that is
`z₃(z, 0) = ι(z)`.

The identity is motivated by the chord through a point and the origin meeting the curve again at
the negative of that point, but nothing about points of the curve is proved here — only the
corresponding identity of power series. -/
@[simp]
theorem subst_unitR_formalThirdRoot :
    subst (Sum.elim X (fun _ ↦ 0) : Unit ⊕ Unit → MvPowerSeries Unit R)
      (formalThirdRoot W) = formalInverse W := by
  have hXL : PowerSeries.X *
      subst (Sum.elim X (fun _ ↦ 0) : Unit ⊕ Unit → MvPowerSeries Unit R)
        (formalSlope W) = formalW W :=
    X_mul_subst_unitR_formalSlope W
  have hLfix := wEquation_of_X_mul W hXL
  have hL0 : PowerSeries.constantCoeff
      (subst (Sum.elim X (fun _ ↦ 0) : Unit ⊕ Unit → MvPowerSeries Unit R)
        (formalSlope W)) = 0 := by
    have := congrArg PowerSeries.constantCoeff hLfix
    simpa [pow_two] using this
  rw [subst_unitR_formalThirdRoot_eq W rfl hL0]
  -- compare with `ι = -z · u⁻¹` after clearing both units
  set L : PowerSeries R :=
    subst (Sum.elim X (fun _ ↦ 0) : Unit ⊕ Unit → MvPowerSeries Unit R)
      (formalSlope W) with hLset
  have hden : PowerSeries.constantCoeff (1 + PowerSeries.C W.a₂ * L +
      PowerSeries.C W.a₄ * L ^ 2 + PowerSeries.C W.a₆ * L ^ 3) = 1 := by simp [hL0]
  set d : PowerSeries R := invOfUnit (1 + PowerSeries.C W.a₂ * L +
    PowerSeries.C W.a₄ * L ^ 2 + PowerSeries.C W.a₆ * L ^ 3) 1 with hd
  have hUnit2 : (1 + PowerSeries.C W.a₂ * L + PowerSeries.C W.a₄ * L ^ 2 +
      PowerSeries.C W.a₆ * L ^ 3) * d = 1 := mul_invOfUnit _ 1 (by exact_mod_cast hden)
  have hUnit1 := mul_invOfUnit_formalInverseDenom W
  clear_value L d
  refine (isUnit_formalInverseDenom W |>.mul (IsUnit.of_mul_eq_one _ hUnit2)).mul_left_cancel ?_
  rw [formalInverse_def]
  simp only [formalInverseDenom_def] at hUnit1 ⊢
  rw [← hXL] at hUnit1 ⊢
  linear_combination ((1 + PowerSeries.C W.a₂ * L + PowerSeries.C W.a₄ * L ^ 2 +
      PowerSeries.C W.a₆ * L ^ 3) * PowerSeries.X) * hUnit1 -
    ((1 - PowerSeries.C W.a₁ * PowerSeries.X - PowerSeries.C W.a₃ * (PowerSeries.X * L)) *
      (PowerSeries.C W.a₁ * L + PowerSeries.C W.a₃ * L ^ 2)) * hUnit2 -
    (PowerSeries.C W.a₁ + PowerSeries.C W.a₃ * L) * hLfix

/-! ### The unit laws -/

/-- **The right unit law**: `F(z, 0) = z`. Adding the origin does nothing. -/
@[simp]
theorem subst_unitR_formalAdd :
    subst (Sum.elim X (fun _ ↦ 0) : Unit ⊕ Unit → MvPowerSeries Unit R)
      (formalAdd W) = PowerSeries.X := by
  rw [formalAdd_def, subst_comp_subst_apply (hasSubst_formalThirdRoot W) hasSubst_unitR]
  have h : (fun _ : Unit ↦ subst
      (Sum.elim X (fun _ ↦ 0) : Unit ⊕ Unit → MvPowerSeries Unit R) (formalThirdRoot W)) =
      fun _ : Unit ↦ (formalInverse W : MvPowerSeries Unit R) := by
    funext u
    exact subst_unitR_formalThirdRoot W
  rw [h]
  exact subst_formalInverse_self W

/-- Substituting `0` for the first parameter and `X` for the second is a legitimate
substitution. -/
private theorem hasSubst_unitL :
    HasSubst (Sum.elim (fun _ ↦ 0) X : Unit ⊕ Unit → MvPowerSeries Unit R) :=
  hasSubst_of_constantCoeff_zero (by rintro (j | j) <;> simp)

/-- **The left unit law**: `F(0, z) = z`, by the right unit law and commutativity. -/
@[simp]
theorem subst_unitL_formalAdd :
    subst (Sum.elim (fun _ ↦ 0) X : Unit ⊕ Unit → MvPowerSeries Unit R)
      (formalAdd W) = PowerSeries.X := by
  conv_lhs => rw [← rename_swap_formalAdd W]
  rw [subst_rename Sum.swap (formalAdd W) hasSubst_unitL]
  have h : (Sum.elim (fun _ ↦ 0) X : Unit ⊕ Unit → MvPowerSeries Unit R) ∘ Sum.swap =
      (Sum.elim X (fun _ ↦ 0) : Unit ⊕ Unit → MvPowerSeries Unit R) := by
    funext s
    match s with
    | .inl () => rfl
    | .inr () => rfl
  rw [h]
  exact subst_unitR_formalAdd W

/-! ### The linear coefficients -/

/-- Extract a linear coefficient from an axis substitution: if substituting `X` at `s₀` and `0`
at the other variable turns `f` into `X`, then the coefficient of `f` at `s₀` is `1`. -/
private theorem coeff_single_eq_one_of_subst_eq_X {f : MvPowerSeries (Unit ⊕ Unit) R}
    {s₀ : Unit ⊕ Unit} {fam : Unit ⊕ Unit → MvPowerSeries Unit R}
    (hfam₀ : fam s₀ = X ()) (hfam : ∀ s ≠ s₀, fam s = 0)
    (hsubst : subst fam f = PowerSeries.X) :
    coeff (Finsupp.single s₀ 1) f = 1 := by
  have hS : HasSubst fam := by
    refine hasSubst_of_constantCoeff_zero fun s ↦ ?_
    rcases eq_or_ne s s₀ with rfl | h
    · rw [hfam₀]
      exact constantCoeff_X ()
    · rw [hfam s h, map_zero]
  have h := congrArg (coeff (Finsupp.single () 1)) hsubst
  rw [coeff_subst hS, PowerSeries.X_apply, coeff_X, ite_eq_left rfl] at h
  rw [finsum_eq_single _ (Finsupp.single s₀ 1) (fun d hd ↦ ?_)] at h
  · rwa [Finsupp.prod_single_index (h := fun s e ↦ fam s ^ e) (pow_zero _), hfam₀, pow_one,
      coeff_X, ite_eq_left rfl, smul_eq_mul, mul_one] at h
  · rcases Classical.em (∃ s ≠ s₀, d s ≠ 0) with ⟨s, hs, hds⟩ | hd0
    · rw [Finsupp.prod, Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hds)
        (by rw [hfam s hs, zero_pow hds]), map_zero, smul_zero]
    · push Not at hd0
      have hd' : d = Finsupp.single s₀ (d s₀) := Finsupp.ext fun u ↦ by
        rcases eq_or_ne u s₀ with rfl | hu
        · rw [Finsupp.single_eq_same]
        · simp [hd0 u hu, Ne.symm hu]
      have hne1 : d s₀ ≠ 1 := fun h1 ↦ hd (by rw [hd', h1])
      rw [hd', Finsupp.prod_single_index (h := fun s e ↦ fam s ^ e) (pow_zero _), hfam₀,
        X_pow_eq () (d s₀), coeff_monomial,
        ite_eq_right (by simpa using fun h ↦ absurd h.symm hne1), smul_zero]

/-- The linear coefficient of the addition series in the first parameter is `1`. -/
@[simp]
theorem coeff_single_inl_formalAdd :
    coeff (Finsupp.single (Sum.inl ()) 1) (formalAdd W) = 1 :=
  coeff_single_eq_one_of_subst_eq_X rfl
    (fun s h ↦ by
      rcases s with u | u
      · exact absurd rfl h
      · rfl)
    (subst_unitR_formalAdd W)

/-- The linear coefficient of the addition series in the second parameter is `1`. -/
@[simp]
theorem coeff_single_inr_formalAdd :
    coeff (Finsupp.single (Sum.inr ()) 1) (formalAdd W) = 1 :=
  coeff_single_eq_one_of_subst_eq_X rfl
    (fun s h ↦ by
      rcases s with u | u
      · rfl
      · exact absurd rfl h)
    (subst_unitL_formalAdd W)

/-- The total degree of a two-variable exponent is the sum of its two entries. Both variables
range over `Unit`, so the degree is a sum over a two-element type. -/
private theorem degree_two_var (d : Unit ⊕ Unit →₀ ℕ) :
    d.degree = d (Sum.inl ()) + d (Sum.inr ()) := by
  rw [Finsupp.degree_eq_sum]
  simp [Fintype.sum_sum_type]

/-- **Below total degree two the group law is addition**: the coefficients of
`formalAdd W - X (Sum.inl ()) - X (Sum.inr ())` vanish on every exponent of total degree `< 2`. -/
theorem coeff_formalAdd_sub_eq_zero_of_degree_lt {d : Unit ⊕ Unit →₀ ℕ} (hd : d.degree < 2) :
    coeff d (formalAdd W - X (Sum.inl ()) - X (Sum.inr ())) = 0 := by
  rw [degree_two_var] at hd
  simp only [map_sub, coeff_X]
  have hcase : d (Sum.inl ()) = 0 ∧ d (Sum.inr ()) = 0 ∨
      d (Sum.inl ()) = 1 ∧ d (Sum.inr ()) = 0 ∨
      d (Sum.inl ()) = 0 ∧ d (Sum.inr ()) = 1 := by omega
  have hext : ∀ a b, d (Sum.inl ()) = a → d (Sum.inr ()) = b →
      d = Finsupp.single (Sum.inl ()) a + Finsupp.single (Sum.inr ()) b := fun a b ha hb ↦
    Finsupp.ext fun s ↦ by rcases s with u | u <;> simp [← ha, ← hb]
  rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    rw [hext _ _ h1 h2] <;>
    simp [coeff_zero_eq_constantCoeff_apply,
      constantCoeff_formalAdd W, coeff_single_inl_formalAdd W, coeff_single_inr_formalAdd W,
      Finsupp.single_eq_single_iff,
      (Ne.symm (Finsupp.single_ne_zero.mpr one_ne_zero) :
        (0 : Unit ⊕ Unit →₀ ℕ) ≠ Finsupp.single (Sum.inl ()) 1),
      (Ne.symm (Finsupp.single_ne_zero.mpr one_ne_zero) :
        (0 : Unit ⊕ Unit →₀ ℕ) ≠ Finsupp.single (Sum.inr ()) 1)]

end WeierstrassCurve
