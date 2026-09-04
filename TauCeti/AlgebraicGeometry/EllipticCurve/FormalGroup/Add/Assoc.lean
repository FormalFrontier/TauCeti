/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Add.Series
import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Add.PairSubst
import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Add.Unit
import TauCeti.AlgebraicGeometry.EllipticCurve.Universal
import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.ThirdPoint

/-!
# The chord group law over the fraction field of the series ring

**Associativity of the chord addition series**, `F(F(t₁, t₂), t₃) = F(t₁, F(t₂, t₃))`, proved by
transporting the honest group law of a Weierstrass curve. The parameters are power series, so the
curve has to be read over a field containing them: this file base changes `W` along
`O → MvPowerSeries σ O → KK`, records the `w`-equation there, and identifies a parameter with the
point `(q, w(q))` it names. Chord addition of those points *is* the addition series, so
associativity of the curve's group law is associativity of the series.

That argument needs a domain, so it runs over the universal curve, whose base `ℤ[A₁, ⋯, A₆]`
supplies one; `map_specialize` carries the conclusion to every `W` over every commutative ring.

## Main statements

* `WeierstrassCurve.formalAdd_assoc` : **the associativity of the addition series**, for every
  Weierstrass curve over every commutative ring. It is this module's only exported result; the
  fraction-field base change, the parametrized point `θ` and the chord additions it satisfies are
  private implementation details of its proof.

## Provenance

Adapted from Michael Stoll's `EllipticCurves` project
(`github.com/MichaelStollBayreuth/EllipticCurves`, Apache-2.0) at commit
`66889eada51a74c2f5dfb7fb5909b0b5a0a2d96e`,
`EllipticCurves/WeierstrassFormalGroup/GroupLaw.lean`, sections `Domain` and `Assembly`,
declarations `subst_wSeries_ne_zero`, `fracCurve`, `rho_weierstrass`, `thetaPoint`,
`thetaPoint_add`, `thetaPoint_neg`, `thetaPoint_inj` and `pair_intercept_ne_zero_of_ne`, together
with the single-parameter helpers `single_u_mul`, `single_iota_eq`, `single_u_eq` and
`single_wIota` from `EllipticCurves/WeierstrassFormalGroup/ThirdPoint.lean`.

Two of those are proved differently here, because this repository already has the content in a
more usable form. `pair_intercept_ne_zero_of_ne` collapses the cross combination with the single
rewrite `subst_pair_formalIntercept_mul_sub` where the source combines its two intercept readings
by hand; and Stoll's `hA` step inside `thetaPoint_add` argues through the constant coefficient,
whereas `subst_pair_thirdRootDenom_mul` already exhibits an explicit inverse. The four
single-parameter helpers are likewise transports of the `FormalGroup/Inverse.lean` identities
along `PowerSeries.subst q`, not re-derivations of them.

The source's `wSeries` and `vSeries` are `formalW` and `formalU` here, continuing the renaming
this repository applies to that development, so `subst_wSeries_ne_zero` is
`subst_formalW_ne_zero`.

The `Universal` section of the same file (declarations `universal_Δ_ne_zero` and
`assoc_addSeries_universal`) is `fracCurve_universal_Δ_ne_zero` and `assoc_formalAdd_universal`
here. Four of that section's nine declarations are not ported, because this repository already
has them: `universal`, `exists_map_universal` and `universal_Δ_ne_zero` are `Universal.curve`,
`map_specialize` and `Universal.curve_Δ_ne_zero`, and the source's `X_ne_X` and `X_ne_zero'` are
Mathlib's `MvPowerSeries.X_inj` and `nonZeroDivisors.ne_zero MvPowerSeries.X_mem_nonzeroDivisors`.

The source's `interceptSeries_ne_zero` and `X_pair_intercept_ne_zero` have no counterpart. The
source needs them only because it supplies the nonvanishing intercept two different ways, an
elementary one at a pair of distinct variables and `pair_intercept_ne_zero_of_ne` elsewhere; here
`pair_intercept_ne_zero_of_ne` covers the variable pairs too, so `thetaPoint_add_of_ne` serves
all four chord additions of the assembly.

The assembly also runs two specializations of the three parameters where the source runs one.
The source separates the middle parameter from the third with `X_ne_X`, a syntactic argument; the
corresponding hypothesis here is `q₂ ≠ ι(q₃)`, which no syntactic argument reaches, so `χ'` sends
the middle parameter to `X` and the other two to `0` exactly as `χ` does for the first.

The statement is adapted rather than transcribed, because this repository states the `w`-equation
differently. Stoll carries a second copy of the equation as a private `def mvWStepAt` and phrases
the fixed-point property as `subst_wSeries_fix`; here `wEquationRHS` is already stated over an
arbitrary algebra, so reading it in `KK` *is* that definition, and `subst_formalW_wEquation`
supplies the fixed-point property. Stoll's proof is `congrArg` followed by unfolding `mvWStepAt`;
the corresponding step here has to move the coefficients across the base change instead, which is
what `fracCurve` in the statement records.
-/

public section

namespace WeierstrassCurve

open MvPowerSeries

variable {O : Type*} [CommRing O]


/-- The curve `W` base changed to a commutative ring `KK` over the series ring
`MvPowerSeries σ O`. The parameters of the chord construction are series, so the group law they
satisfy is the group law of this curve; the group-law arguments below specialize `KK` to a fraction
field of the series ring, which is where the chord construction needs division, but the base change
itself asks only for a commutative algebra. There is no `Algebra O KK` to run
`WeierstrassCurve.baseChange` along, so this is the composite `map`, and it is Mathlib's `map_*`
lemmas that unfolding it exposes. -/
private noncomputable def fracCurve (W : WeierstrassCurve O) (σ : Type*) (KK : Type*)
    [CommRing KK] [Algebra (MvPowerSeries σ O) KK] : WeierstrassCurve KK :=
  W.map <| (algebraMap (MvPowerSeries σ O) KK).comp (algebraMap O (MvPowerSeries σ O))

variable (W : WeierstrassCurve O) {σ : Type*} {KK : Type*} [Field KK]
  [Algebra (MvPowerSeries σ O) KK]

/-- The `w`-expansion read at a substitutable parameter still solves the `w`-equation after being
pushed into `KK`, where the equation is the one of `fracCurve W`.

`subst_formalW_wEquation` is the same fixed point one level down, over `MvPowerSeries σ O`; here
the parameter and the solution are both read in `KK`, so the coefficients travel across the base
change too and the curve on the right is `fracCurve W σ KK` rather than `W`. Consumers such as
`chord_point_nonsingular` want the equation written out, so this is normally applied through
`simpa [wEquationRHS_def] using …`. -/
private theorem algebraMap_subst_formalW_wEquation {q : MvPowerSeries σ O}
    (hq : PowerSeries.HasSubst q) :
    algebraMap (MvPowerSeries σ O) KK (PowerSeries.subst q (formalW W)) = wEquationRHS
      (fracCurve W σ KK) (algebraMap (MvPowerSeries σ O) KK q)
      (algebraMap (MvPowerSeries σ O) KK (PowerSeries.subst q (formalW W))) := by
  conv_lhs => rw [subst_formalW_wEquation W hq]
  simp [fracCurve, wEquationRHS_def]

/-! ### The formal inverse at a parameter -/

/-- The denominator of the formal inverse, read at a parameter, still multiplies its `invOfUnit`
to `1`: substituting is a ring map, so it carries `mul_invOfUnit_formalInverseDenom` along. -/
private theorem subst_formalInverseDenom_mul {q : MvPowerSeries σ O}
    (hq : PowerSeries.HasSubst q) :
    PowerSeries.subst q (formalInverseDenom W) *
        PowerSeries.subst q (PowerSeries.invOfUnit (formalInverseDenom W) 1) = 1 := by
  have h := congrArg (PowerSeries.substAlgHom hq) (mul_invOfUnit_formalInverseDenom W)
  simp only [map_mul, map_one] at h
  simpa only [PowerSeries.coe_substAlgHom hq] using h

/-- The formal inverse read at a parameter: `ι(q) = -(q * u(q)⁻¹)`. -/
private theorem subst_formalInverse_eq {q : MvPowerSeries σ O} (hq : PowerSeries.HasSubst q) :
    PowerSeries.subst q (formalInverse W) =
      -(q * PowerSeries.subst q (PowerSeries.invOfUnit (formalInverseDenom W) 1)) := by
  rw [formalInverse_def, ← PowerSeries.coe_substAlgHom hq]
  simp only [map_neg, map_mul]
  rw [PowerSeries.coe_substAlgHom hq, PowerSeries.subst_X hq]

/-- The denominator of the formal inverse read at a parameter, written out. -/
private theorem subst_formalInverseDenom_eq {q : MvPowerSeries σ O}
    (hq : PowerSeries.HasSubst q) :
    PowerSeries.subst q (formalInverseDenom W) =
      1 - C W.a₁ * q - C W.a₃ * PowerSeries.subst q (formalW W) := by
  rw [formalInverseDenom_def, ← PowerSeries.coe_substAlgHom hq]
  simp only [map_sub, map_one, map_mul, PowerSeries.substAlgHom_X,
    PowerSeries.coe_substAlgHom, PowerSeries.subst_C]

/-- The `w`-expansion at the inverted parameter: `w(ι(q)) = -(w(q) * u(q)⁻¹)`.

This is the one-variable `subst_formalInverse_formalW` carried through the substitution `q`. -/
private theorem subst_formalW_subst_formalInverse {q : MvPowerSeries σ O}
    (hq : PowerSeries.HasSubst q) :
    PowerSeries.subst (PowerSeries.subst q (formalInverse W)) (formalW W) =
      -(PowerSeries.subst q (formalW W) *
        PowerSeries.subst q (PowerSeries.invOfUnit (formalInverseDenom W) 1)) := by
  rw [← PowerSeries.subst_comp_subst_apply (hasSubst_formalInverse W) hq,
    subst_formalInverse_formalW, ← PowerSeries.coe_substAlgHom hq]
  simp only [map_neg, map_mul]

/-- The addition series read at a pair of variables again has vanishing constant coefficient, so
it is itself a legitimate parameter — which is what lets the associativity argument feed one
bracketed sum into another. -/
private theorem constantCoeff_subst_pair_X_formalAdd {σ' : Type*} (s₁ s₂ : σ') :
    constantCoeff (subst (Sum.elim (fun _ ↦ (X s₁ : MvPowerSeries σ' O)) (fun _ ↦ X s₂) :
      Unit ⊕ Unit → MvPowerSeries σ' O) (formalAdd W)) = 0 :=
  constantCoeff_subst_eq_zero (hasSubst_pair (constantCoeff_X _) (constantCoeff_X _))
    (by rintro (j | j) <;> simp) (constantCoeff_formalAdd W)

/-- Base change commutes with reading the addition series at a pair of variables: the variables
are fixed by `MvPowerSeries.map`, so only `map_formalAdd` is doing any work. -/
private theorem map_subst_pair_X_formalAdd {σ' S : Type*} [CommRing S] (φ : O →+* S)
    (s₁ s₂ : σ') :
    MvPowerSeries.map φ (subst (Sum.elim (fun _ ↦ (X s₁ : MvPowerSeries σ' O)) (fun _ ↦ X s₂) :
        Unit ⊕ Unit → MvPowerSeries σ' O) (formalAdd W)) =
      subst (Sum.elim (fun _ ↦ (X s₁ : MvPowerSeries σ' S)) (fun _ ↦ X s₂) :
        Unit ⊕ Unit → MvPowerSeries σ' S) (formalAdd (W.map φ)) := by
  rw [MvPowerSeries.map_subst (hasSubst_pair (constantCoeff_X _) (constantCoeff_X _)),
    map_formalAdd]
  congr 1
  funext i
  rcases i with u | u <;> simp

/-! ### Reading a pair through a further substitution -/

/-- The addition series at a pair, read through a further substitution `g` that sends the first
parameter to `X` and the second to `0`: the right unit law makes the result `X`. -/
private theorem subst_subst_pair_formalAdd_eq_X {σ' : Type*}
    {g : σ' → MvPowerSeries Unit O} (hg : HasSubst g) {a b : MvPowerSeries σ' O}
    (ha : constantCoeff a = 0) (hb : constantCoeff b = 0)
    (hga : subst g a = PowerSeries.X) (hgb : subst g b = 0) :
    subst g (subst (Sum.elim (fun _ ↦ a) (fun _ ↦ b) : Unit ⊕ Unit → MvPowerSeries σ' O)
      (formalAdd W)) = PowerSeries.X := by
  -- The composite family is pointwise `X` and `0`, but only pointwise: the reshape below is
  -- `funext`, not a definitional equality, and it is needed because `subst_unitR_formalAdd` is
  -- stated for the `Sum.elim` spelling that `rw` must match syntactically.
  rw [subst_comp_subst_apply (hasSubst_pair ha hb) hg,
    show (fun s : Unit ⊕ Unit ↦ subst g (Sum.elim (fun _ ↦ a) (fun _ ↦ b) s)) =
      (Sum.elim X (fun _ ↦ 0) : Unit ⊕ Unit → MvPowerSeries Unit O) from
      funext fun s ↦ by rcases s with u | u; exacts [hga, hgb]]
  exact subst_unitR_formalAdd W

/-- The addition series at a pair, read through a further substitution `g` that kills both
parameters: the result vanishes, since the series has no constant term. -/
private theorem subst_subst_pair_formalAdd_eq_zero {σ' : Type*}
    {g : σ' → MvPowerSeries Unit O} (hg : HasSubst g) {a b : MvPowerSeries σ' O}
    (ha : constantCoeff a = 0) (hb : constantCoeff b = 0)
    (hga : subst g a = 0) (hgb : subst g b = 0) :
    subst g (subst (Sum.elim (fun _ ↦ a) (fun _ ↦ b) : Unit ⊕ Unit → MvPowerSeries σ' O)
      (formalAdd W)) = 0 := by
  -- As above, the reshape is `funext` rather than defeq: `g` kills both components pointwise,
  -- and the zero family is what `subst_zero_of_constantCoeff_zero` is stated against.
  rw [subst_comp_subst_apply (hasSubst_pair ha hb) hg,
    show (fun s : Unit ⊕ Unit ↦ subst g (Sum.elim (fun _ ↦ a) (fun _ ↦ b) s)) =
      (0 : Unit ⊕ Unit → MvPowerSeries Unit O) from
      funext fun s ↦ by rcases s with u | u; exacts [hga, hgb]]
  exact subst_zero_of_constantCoeff_zero (constantCoeff_formalAdd W)

/-- The formal inverse at a parameter, read through a further substitution `g` that kills that
parameter: the result vanishes, since the inverse has no constant term. -/
private theorem subst_subst_formalInverse_eq_zero {σ' : Type*}
    {g : σ' → MvPowerSeries Unit O} (hg : HasSubst g) {a : MvPowerSeries σ' O}
    (ha : constantCoeff a = 0) (hga : subst g a = 0) :
    subst g (subst (fun _ : Unit ↦ a) (formalInverse W)) = 0 := by
  -- `funext` again, on the one-variable family this time.
  rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero fun _ ↦ ha) hg,
    show (fun _ : Unit ↦ subst g a) = (0 : Unit → MvPowerSeries Unit O) from
      funext fun _ ↦ hga]
  exact subst_zero_of_constantCoeff_zero (constantCoeff_formalInverse W)

/-! ### The parametrized point -/

variable [IsDomain O]

/-- Over a domain the `w`-expansion at a nonzero parameter with vanishing constant coefficient is
itself nonzero: it factors as `q ^ 3 * u(q)`, and `u` has constant coefficient `1`. -/
private theorem subst_formalW_ne_zero {q : MvPowerSeries σ O} (hq : constantCoeff q = 0)
    (hq0 : q ≠ 0) : PowerSeries.subst q (formalW W) ≠ 0 := by
  have hs : PowerSeries.HasSubst q := PowerSeries.HasSubst.of_constantCoeff_zero hq
  have hexp : PowerSeries.subst q (formalW W) = q ^ 3 * PowerSeries.subst q (formalU W) := by
    conv_lhs => rw [formalW_eq_X_pow_mul_formalU]
    rw [← PowerSeries.coe_substAlgHom hs, map_mul, map_pow, PowerSeries.coe_substAlgHom hs,
      PowerSeries.subst_X hs]
  rw [hexp]
  refine mul_ne_zero (pow_ne_zero 3 hq0) fun h ↦ ?_
  have hc := congrArg constantCoeff h
  rw [map_zero, PowerSeries.constantCoeff_subst hs] at hc
  rw [finsum_eq_single _ 0 fun d hd ↦ ?_] at hc
  · rw [PowerSeries.coeff_zero_eq_constantCoeff, constantCoeff_formalU, pow_zero, map_one,
      smul_eq_mul, mul_one] at hc
    exact one_ne_zero hc
  · rw [map_pow, hq, zero_pow hd, smul_zero]

variable [IsFractionRing (MvPowerSeries σ O) KK]

/-- The `w`-expansion at a nonzero parameter stays nonzero after being pushed into `KK`: the
localization map of a fraction field is injective, so it cannot introduce a zero.

Every parametrized point of this file needs its `w`-coordinate invertible in `KK`, so this is the
form `subst_formalW_ne_zero` is actually used in. -/
private theorem algebraMap_subst_formalW_ne_zero {q : MvPowerSeries σ O}
    (hq : constantCoeff q = 0) (hq0 : q ≠ 0) :
    algebraMap (MvPowerSeries σ O) KK (PowerSeries.subst q (formalW W)) ≠ 0 := fun h ↦
  W.subst_formalW_ne_zero hq hq0
    (IsFractionRing.injective (MvPowerSeries σ O) KK (by rw [h, map_zero]))

/-- The point of the base-changed curve carried by the parameter `q`: the solution `(q, w(q))` of
the `w`-equation, read in `KK` and in the affine coordinates `(q / w, -1 / w)` of the chart. -/
private noncomputable def thetaPoint (hΔ : (fracCurve W σ KK).Δ ≠ 0)
    {q : MvPowerSeries σ O} (hq : constantCoeff q = 0) (hq0 : q ≠ 0) :
    (fracCurve W σ KK).toAffine.Point :=
  Affine.Point.some _ _ (chord_point_nonsingular (fracCurve W σ KK)
    (by
      simpa [wEquationRHS_def] using
        W.algebraMap_subst_formalW_wEquation (KK := KK)
          (PowerSeries.HasSubst.of_constantCoeff_zero hq))
    (W.algebraMap_subst_formalW_ne_zero hq hq0)
    hΔ)

variable [DecidableEq KK] in
/-- **The chord addition of parametrized points**: `θ(q₁) + θ(q₂) = θ(F(q₁, q₂))`.

The two parametrized points lie on `fracCurve W`, the chord through them meets the curve again at
the parameter `z₃`, and the addition series is exactly the reflection of that third point. So the
group law of an honest Weierstrass curve, applied to the two points, computes `F(q₁, q₂)`. -/
private theorem thetaPoint_add (hΔ : (fracCurve W σ KK).Δ ≠ 0)
    {q₁ q₂ : MvPowerSeries σ O} (h₁ : constantCoeff q₁ = 0) (h₂ : constantCoeff q₂ = 0)
    (hq₁0 : q₁ ≠ 0) (hq₂0 : q₂ ≠ 0)
    (hN : subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) : Unit ⊕ Unit → MvPowerSeries σ O)
      (formalIntercept W) ≠ 0)
    (hx : q₁ * PowerSeries.subst q₂ (formalW W) - q₂ * PowerSeries.subst q₁ (formalW W) ≠ 0)
    (hF : constantCoeff (subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) :
      Unit ⊕ Unit → MvPowerSeries σ O) (formalAdd W)) = 0)
    (hF0 : subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) : Unit ⊕ Unit → MvPowerSeries σ O)
      (formalAdd W) ≠ 0) :
    W.thetaPoint hΔ h₁ hq₁0 + W.thetaPoint hΔ h₂ hq₂0 = W.thetaPoint hΔ hF hF0 := by
  classical
  set ρ := algebraMap (MvPowerSeries σ O) KK with hρ
  have hinj : Function.Injective ρ := IsFractionRing.injective (MvPowerSeries σ O) KK
  set Λp := subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) :
    Unit ⊕ Unit → MvPowerSeries σ O) (formalSlope W) with hΛp
  set Np := subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) :
    Unit ⊕ Unit → MvPowerSeries σ O) (formalIntercept W) with hNp
  set Tp := subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) :
    Unit ⊕ Unit → MvPowerSeries σ O) (formalThirdRoot W) with hTp
  set w₁ := PowerSeries.subst q₁ (formalW W) with hw₁'
  set w₂ := PowerSeries.subst q₂ (formalW W) with hw₂'
  set wT := PowerSeries.subst Tp (formalW W) with hwT'
  -- the chord identities, read in `KK`
  have hslope : ρ Λp * (ρ q₂ - ρ q₁) = ρ w₂ - ρ w₁ := by
    rw [← map_sub, ← map_sub, ← map_mul]
    exact congrArg ρ (subst_pair_formalSlope_mul W h₁ h₂)
  have hNint : ρ Np = ρ w₁ - ρ Λp * ρ q₁ := by
    rw [← map_mul, ← map_sub]
    exact congrArg ρ (subst_pair_formalIntercept_eq_inl W h₁ h₂)
  have hwTeq : ρ wT = ρ Λp * ρ Tp + ρ Np := by
    have h := congrArg ρ (subst_pair_formalThirdRoot_formalW W h₁ h₂)
    simp only [map_add, map_mul] at h
    exact h
  have hT₃ : (1 + (fracCurve W σ KK).a₂ * ρ Λp + (fracCurve W σ KK).a₄ * ρ Λp ^ 2 +
      (fracCurve W σ KK).a₆ * ρ Λp ^ 3) * (ρ Tp + ρ q₁ + ρ q₂) =
      -((fracCurve W σ KK).a₁ * ρ Λp + (fracCurve W σ KK).a₂ * ρ Np +
        (fracCurve W σ KK).a₃ * ρ Λp ^ 2 + 2 * (fracCurve W σ KK).a₄ * ρ Λp * ρ Np +
        3 * (fracCurve W σ KK).a₆ * ρ Λp ^ 2 * ρ Np) := by
    have h := congrArg ρ (subst_pair_formalThirdRoot_relation W h₁ h₂)
    simp only [map_add, map_mul, map_neg, map_pow, map_one, map_ofNat] at h
    simpa [fracCurve, MvPowerSeries.c_eq_algebraMap] using h
  -- nonvanishing
  have hA : (1 + (fracCurve W σ KK).a₂ * ρ Λp + (fracCurve W σ KK).a₄ * ρ Λp ^ 2 +
      (fracCurve W σ KK).a₆ * ρ Λp ^ 3) ≠ 0 := by
    intro h
    refine subst_pair_thirdRootDenom_ne_zero W h₁ h₂ (hinj ?_)
    simpa [fracCurve, MvPowerSeries.c_eq_algebraMap, map_zero] using h
  have hTp0 : Tp ≠ 0 := subst_pair_formalThirdRoot_ne_zero W h₁ h₂ hN
  have hw₁0 : ρ w₁ ≠ 0 := W.algebraMap_subst_formalW_ne_zero h₁ hq₁0
  have hw₂0 : ρ w₂ ≠ 0 := W.algebraMap_subst_formalW_ne_zero h₂ hq₂0
  have hTc : constantCoeff Tp = 0 := constantCoeff_subst_pair_formalThirdRoot W h₁ h₂
  have hwT0 : ρ wT ≠ 0 := W.algebraMap_subst_formalW_ne_zero hTc hTp0
  have hxρ : ρ q₁ * ρ w₂ - ρ q₂ * ρ w₁ ≠ 0 := by
    rw [← map_mul, ← map_mul, ← map_sub]
    exact fun h ↦ hx (hinj (by rw [h, map_zero]))
  -- the two parametrized points satisfy the Weierstrass equation of `fracCurve W`
  have hwq₁ := by
    simpa [wEquationRHS_def] using
      W.algebraMap_subst_formalW_wEquation (KK := KK)
        (PowerSeries.HasSubst.of_constantCoeff_zero h₁)
  have hwq₂ := by
    simpa [wEquationRHS_def] using
      W.algebraMap_subst_formalW_wEquation (KK := KK)
        (PowerSeries.HasSubst.of_constantCoeff_zero h₂)
  -- the honest group law of `fracCurve W`, applied to the two points
  obtain ⟨h₃, hadd⟩ := chord_point_add (fracCurve W σ KK) hwq₁ hwq₂ hslope hNint hT₃ hwTeq hA
    hw₁0 hw₂0 hwT0 hxρ
    (chord_point_nonsingular (fracCurve W σ KK) hwq₁ hw₁0 hΔ)
    (chord_point_nonsingular (fracCurve W σ KK) hwq₂ hw₂0 hΔ)
  -- `hadd` is stated with the coordinates written out, and `thetaPoint` is *by definition* that
  -- `Affine.Point.some`, so this folds the definition back. Unlike the reshapes above this one
  -- really is a definitional equality, and it breaks if `thetaPoint` is ever restated.
  refine Eq.trans (show W.thetaPoint hΔ h₁ hq₁0 + W.thetaPoint hΔ h₂ hq₂0 =
    Affine.Point.some _ _ h₃ from hadd) ?_
  -- identify the third point with the point of parameter `F(q₁, q₂)`
  set sp := PowerSeries.subst Tp (PowerSeries.invOfUnit (formalInverseDenom W) 1) with hsp'
  have hu : ρ (PowerSeries.subst Tp (formalInverseDenom W)) * ρ sp = 1 := by
    rw [← map_mul, ← map_one ρ]
    exact congrArg ρ (subst_pair_formalInverseDenom_mul W h₁ h₂)
  have hueq : ρ (PowerSeries.subst Tp (formalInverseDenom W)) =
      1 - (fracCurve W σ KK).a₁ * ρ Tp - (fracCurve W σ KK).a₃ * ρ wT := by
    have h := congrArg ρ (subst_pair_formalInverseDenom_eq W h₁ h₂)
    simp only [map_sub, map_mul, map_one, MvPowerSeries.c_eq_algebraMap] at h
    exact h
  have hsp0 : ρ sp ≠ 0 := by
    intro h
    rw [h, mul_zero] at hu
    exact one_ne_zero hu.symm
  have hFeq : ρ (subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) :
      Unit ⊕ Unit → MvPowerSeries σ O) (formalAdd W)) = -(ρ Tp * ρ sp) := by
    have h := congrArg ρ (subst_pair_formalAdd_eq W h₁ h₂)
    simp only [map_neg, map_mul] at h
    exact h
  have hwFeq : ρ (PowerSeries.subst (subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) :
      Unit ⊕ Unit → MvPowerSeries σ O) (formalAdd W)) (formalW W)) = -(ρ wT * ρ sp) := by
    have h := congrArg ρ (subst_pair_formalW_formalAdd W h₁ h₂)
    simp only [map_neg, map_mul] at h
    exact h
  rw [thetaPoint]
  simp only [Affine.Point.some.injEq]
  constructor
  · rw [hFeq, hwFeq]
    field_simp
  · rw [hwFeq, div_eq_div_iff hwT0 (neg_ne_zero.mpr (mul_ne_zero hwT0 hsp0))]
    linear_combination (-(ρ wT)) * hu + (ρ wT * ρ sp) * hueq

/-- **The parametrized point of the inverted parameter is the negative**: `θ(ι(q)) = -θ(q)`.

The formal inverse was built to be the parameter of the reflected point, so this identifies that
construction with the group inverse of `fracCurve W`. Both coordinates come out of the two
readings of the inverse, `ι(q) = -(q * u(q)⁻¹)` and `w(ι(q)) = -(w(q) * u(q)⁻¹)`. -/
private theorem thetaPoint_neg (hΔ : (fracCurve W σ KK).Δ ≠ 0)
    {q : MvPowerSeries σ O} (hq : constantCoeff q = 0) (hq0 : q ≠ 0)
    (hi : constantCoeff (PowerSeries.subst q (formalInverse W)) = 0)
    (hi0 : PowerSeries.subst q (formalInverse W) ≠ 0) :
    W.thetaPoint hΔ hi hi0 = -W.thetaPoint hΔ hq hq0 := by
  classical
  set ρ := algebraMap (MvPowerSeries σ O) KK with hρ
  have hs : PowerSeries.HasSubst q := PowerSeries.HasSubst.of_constantCoeff_zero hq
  have hu : ρ (PowerSeries.subst q (formalInverseDenom W)) *
      ρ (PowerSeries.subst q (PowerSeries.invOfUnit (formalInverseDenom W) 1)) = 1 := by
    rw [← map_mul, ← map_one ρ]
    exact congrArg ρ (W.subst_formalInverseDenom_mul hs)
  have hsp0 : ρ (PowerSeries.subst q (PowerSeries.invOfUnit (formalInverseDenom W) 1)) ≠ 0 := by
    intro h
    rw [h, mul_zero] at hu
    exact one_ne_zero hu.symm
  have hIeq : ρ (PowerSeries.subst q (formalInverse W)) =
      -(ρ q * ρ (PowerSeries.subst q (PowerSeries.invOfUnit (formalInverseDenom W) 1))) := by
    have h := congrArg ρ (W.subst_formalInverse_eq hs)
    simpa only [map_neg, map_mul] using h
  have hwIeq : ρ (PowerSeries.subst (PowerSeries.subst q (formalInverse W)) (formalW W)) =
      -(ρ (PowerSeries.subst q (formalW W)) *
        ρ (PowerSeries.subst q (PowerSeries.invOfUnit (formalInverseDenom W) 1))) := by
    have h := congrArg ρ (W.subst_formalW_subst_formalInverse hs)
    simpa only [map_neg, map_mul] using h
  have hueq : ρ (PowerSeries.subst q (formalInverseDenom W)) =
      1 - (fracCurve W σ KK).a₁ * ρ q -
        (fracCurve W σ KK).a₃ * ρ (PowerSeries.subst q (formalW W)) := by
    have h := congrArg ρ (W.subst_formalInverseDenom_eq hs)
    simp only [map_sub, map_mul, map_one, MvPowerSeries.c_eq_algebraMap] at h
    exact h
  have hw0 : ρ (PowerSeries.subst q (formalW W)) ≠ 0 :=
    W.algebraMap_subst_formalW_ne_zero hq hq0
  simp only [thetaPoint, Affine.Point.neg_some, Affine.Point.some.injEq]
  simp only [← hρ]
  constructor
  · rw [hIeq, hwIeq]
    field_simp
  · rw [hwIeq, Affine.negY]
    field_simp
    linear_combination
      ρ (PowerSeries.subst q (PowerSeries.invOfUnit (formalInverseDenom W) 1)) * hueq - hu

/-- **The parametrized point determines the parameter**: `θ` is injective.

The `y`-coordinate `-1 / w(q)` already pins down `w(q)`, and the `x`-coordinate `q / w(q)` then
pins down `q`. -/
private theorem thetaPoint_inj (hΔ : (fracCurve W σ KK).Δ ≠ 0)
    {q₁ q₂ : MvPowerSeries σ O} (h₁ : constantCoeff q₁ = 0) (h₂ : constantCoeff q₂ = 0)
    (hq₁0 : q₁ ≠ 0) (hq₂0 : q₂ ≠ 0)
    (h : W.thetaPoint hΔ h₁ hq₁0 = W.thetaPoint hΔ h₂ hq₂0) : q₁ = q₂ := by
  classical
  set ρ := algebraMap (MvPowerSeries σ O) KK with hρ
  have hinj : Function.Injective ρ := IsFractionRing.injective (MvPowerSeries σ O) KK
  simp only [thetaPoint, Affine.Point.some.injEq] at h
  simp only [← hρ] at h
  have hw₁0 : ρ (PowerSeries.subst q₁ (formalW W)) ≠ 0 :=
    W.algebraMap_subst_formalW_ne_zero h₁ hq₁0
  have hw₂0 : ρ (PowerSeries.subst q₂ (formalW W)) ≠ 0 :=
    W.algebraMap_subst_formalW_ne_zero h₂ hq₂0
  have hw : ρ (PowerSeries.subst q₁ (formalW W)) = ρ (PowerSeries.subst q₂ (formalW W)) := by
    have h2 := h.2
    field_simp at h2
    linear_combination h2
  refine hinj ?_
  have h1 := h.1
  rw [div_eq_div_iff hw₁0 hw₂0, hw] at h1
  exact mul_right_cancel₀ hw₂0 h1

/-- The intercept at a pair is nonzero as soon as the two parameters are distinct and not
mutually inverse.

If the intercept vanished, the cross combination `q₁ w(q₂) - q₂ w(q₁)` would vanish with it, so
the two parametrized points would share an `x`-coordinate and hence agree up to sign. Injectivity
of `θ` then contradicts one of the two hypotheses. -/
private theorem pair_intercept_ne_zero_of_ne (hΔ : (fracCurve W σ KK).Δ ≠ 0)
    {q₁ q₂ : MvPowerSeries σ O} (h₁ : constantCoeff q₁ = 0) (h₂ : constantCoeff q₂ = 0)
    (hq₁0 : q₁ ≠ 0) (hq₂0 : q₂ ≠ 0) (hne₁ : q₁ ≠ q₂)
    (hne₂ : q₁ ≠ PowerSeries.subst q₂ (formalInverse W)) :
    subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) : Unit ⊕ Unit → MvPowerSeries σ O)
      (formalIntercept W) ≠ 0 := by
  classical
  intro h0
  set ρ := algebraMap (MvPowerSeries σ O) KK with hρ
  have hinj : Function.Injective ρ := IsFractionRing.injective (MvPowerSeries σ O) KK
  have hs₂ : PowerSeries.HasSubst q₂ := PowerSeries.HasSubst.of_constantCoeff_zero h₂
  -- a vanishing intercept collapses the cross combination, so the `x`-coordinates agree
  have hqw : q₁ * PowerSeries.subst q₂ (formalW W) -
      q₂ * PowerSeries.subst q₁ (formalW W) = 0 := by
    rw [subst_pair_formalIntercept_mul_sub W h₁ h₂, h0, zero_mul]
  have hw₁0 : ρ (PowerSeries.subst q₁ (formalW W)) ≠ 0 :=
    W.algebraMap_subst_formalW_ne_zero h₁ hq₁0
  have hw₂0 : ρ (PowerSeries.subst q₂ (formalW W)) ≠ 0 :=
    W.algebraMap_subst_formalW_ne_zero h₂ hq₂0
  have hx : ρ q₁ / ρ (PowerSeries.subst q₁ (formalW W)) =
      ρ q₂ / ρ (PowerSeries.subst q₂ (formalW W)) := by
    rw [div_eq_div_iff hw₁0 hw₂0, ← map_mul, ← map_mul]
    exact congrArg ρ (by linear_combination hqw)
  have hcase := (Affine.Point.X_eq_iff
    (h₁ := chord_point_nonsingular (fracCurve W σ KK)
      (by
        simpa [wEquationRHS_def] using W.algebraMap_subst_formalW_wEquation (KK := KK)
          (PowerSeries.HasSubst.of_constantCoeff_zero h₁))
      hw₁0 hΔ)
    (h₂ := chord_point_nonsingular (fracCurve W σ KK)
      (by simpa [wEquationRHS_def] using W.algebraMap_subst_formalW_wEquation (KK := KK) hs₂)
      hw₂0 hΔ)).mp hx
  -- the data carried by the inverted parameter
  have hs0 : PowerSeries.subst q₂ (PowerSeries.invOfUnit (formalInverseDenom W) 1) ≠ 0 := by
    intro hh
    have hmul := W.subst_formalInverseDenom_mul hs₂
    rw [hh, mul_zero] at hmul
    exact one_ne_zero hmul.symm
  have hi : constantCoeff (PowerSeries.subst q₂ (formalInverse W)) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero h₂ (formalInverse W) (constantCoeff_formalInverse W)
  have hi0 : PowerSeries.subst q₂ (formalInverse W) ≠ 0 := by
    rw [W.subst_formalInverse_eq hs₂]
    exact neg_ne_zero.mpr (mul_ne_zero hq₂0 hs0)
  rcases hcase with hc | hc
  · exact hne₁ (W.thetaPoint_inj hΔ h₁ h₂ hq₁0 hq₂0 hc)
  · -- `hc` comes out of `X_eq_iff` with `thetaPoint` unfolded, so fold it back before rewriting
    have hc' : W.thetaPoint hΔ h₁ hq₁0 = -W.thetaPoint hΔ h₂ hq₂0 := hc
    rw [← W.thetaPoint_neg hΔ h₂ hq₂0 hi hi0] at hc'
    exact hne₂ (W.thetaPoint_inj hΔ h₁ hi hq₁0 hi0 hc')

variable [DecidableEq KK] in
/-- **The chord addition of parametrized points, from distinctness alone**: `θ(q₁) + θ(q₂) =
θ(F(q₁, q₂))` as soon as `q₁` is neither `q₂` nor its formal inverse.

This is the form the associativity argument uses. Both nondegeneracy hypotheses of
`thetaPoint_add` come out of those two: the intercept is nonzero by
`pair_intercept_ne_zero_of_ne`, and the cross combination is then nonzero too, since
`subst_pair_formalIntercept_mul_sub` factors it as `ν(q₁, q₂) (q₁ - q₂)`. -/
private theorem thetaPoint_add_of_ne (hΔ : (fracCurve W σ KK).Δ ≠ 0)
    {q₁ q₂ : MvPowerSeries σ O} (h₁ : constantCoeff q₁ = 0) (h₂ : constantCoeff q₂ = 0)
    (hq₁0 : q₁ ≠ 0) (hq₂0 : q₂ ≠ 0) (hne₁ : q₁ ≠ q₂)
    (hne₂ : q₁ ≠ PowerSeries.subst q₂ (formalInverse W))
    (hF : constantCoeff (subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) :
      Unit ⊕ Unit → MvPowerSeries σ O) (formalAdd W)) = 0)
    (hF0 : subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) : Unit ⊕ Unit → MvPowerSeries σ O)
      (formalAdd W) ≠ 0) :
    W.thetaPoint hΔ h₁ hq₁0 + W.thetaPoint hΔ h₂ hq₂0 = W.thetaPoint hΔ hF hF0 := by
  have hN := W.pair_intercept_ne_zero_of_ne hΔ h₁ h₂ hq₁0 hq₂0 hne₁ hne₂
  refine W.thetaPoint_add hΔ h₁ h₂ hq₁0 hq₂0 hN ?_ hF hF0
  rw [subst_pair_formalIntercept_mul_sub W h₁ h₂]
  exact mul_ne_zero hN (sub_ne_zero.mpr hne₁)


variable [DecidableEq KK] in
/-- **The chord addition of parametrized points, from a separating substitution.**

A single substitution sending `q₁` to `X` and `q₂` to `0` supplies both distinctness hypotheses of
`thetaPoint_add_of_ne` at once: `q₁ ≠ q₂` directly, and `q₁ ≠ ι(q₂)` because the formal inverse of
`q₂` has no constant term either, so the substitution kills it too. This is the form the
associativity assembly uses, where the separating substitution is a `coordSpecialize`. -/
private theorem thetaPoint_add_of_subst_separates (hΔ : (fracCurve W σ KK).Δ ≠ 0)
    {g : σ → MvPowerSeries Unit O} (hg : HasSubst g)
    {q₁ q₂ : MvPowerSeries σ O} (h₁ : constantCoeff q₁ = 0) (h₂ : constantCoeff q₂ = 0)
    (hq₁0 : q₁ ≠ 0) (hq₂0 : q₂ ≠ 0)
    (hg₁ : subst g q₁ = PowerSeries.X) (hg₂ : subst g q₂ = 0)
    (hF : constantCoeff (subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) :
      Unit ⊕ Unit → MvPowerSeries σ O) (formalAdd W)) = 0)
    (hF0 : subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) : Unit ⊕ Unit → MvPowerSeries σ O)
      (formalAdd W) ≠ 0) :
    W.thetaPoint hΔ h₁ hq₁0 + W.thetaPoint hΔ h₂ hq₂0 = W.thetaPoint hΔ hF hF0 :=
  W.thetaPoint_add_of_ne hΔ h₁ h₂ hq₁0 hq₂0 (ne_of_subst_eq_X_of_subst_eq_zero hg₁ hg₂)
    (ne_of_subst_eq_X_of_subst_eq_zero hg₁ (subst_subst_formalInverse_eq_zero W hg h₂ hg₂)) hF hF0

/-! ### Associativity -/

/-- The universal curve stays nonsingular over the fraction field of its series ring: `Δ` is a
nonzero polynomial, and both `C` and the localization map are injective. -/
private theorem fracCurve_universal_Δ_ne_zero (KK : Type*) [Field KK]
    [Algebra (MvPowerSeries (Unit ⊕ Unit ⊕ Unit) (MvPolynomial Coeff ℤ)) KK]
    [IsFractionRing (MvPowerSeries (Unit ⊕ Unit ⊕ Unit) (MvPolynomial Coeff ℤ)) KK] :
    (fracCurve Universal.curve (Unit ⊕ Unit ⊕ Unit) KK).Δ ≠ 0 := by
  rw [fracCurve, map_Δ]
  intro h
  rw [RingHom.comp_apply] at h
  have h1 : (MvPowerSeries.C Universal.curve.Δ :
      MvPowerSeries (Unit ⊕ Unit ⊕ Unit) (MvPolynomial Coeff ℤ)) = 0 := by
    refine IsFractionRing.injective (MvPowerSeries (Unit ⊕ Unit ⊕ Unit) (MvPolynomial Coeff ℤ))
      KK ?_
    rw [map_zero]
    simpa [MvPowerSeries.c_eq_algebraMap] using h
  exact Universal.curve_Δ_ne_zero (MvPowerSeries.C_injective (h1.trans (map_zero _).symm))

/-- **Associativity of the addition series for the universal curve.**

The three parameters are the three coordinate variables of
`ℤ[A₁, ⋯, A₆]⟦t₁, t₂, t₃⟧`, and the two ways of bracketing them are compared as points of the
honest elliptic curve `fracCurve Universal.curve` over that ring's fraction field: `θ` turns each
bracketing into a sum of three points, `thetaPoint_add_of_ne` computes both, associativity of the
curve's group law identifies them, and `thetaPoint_inj` brings the equality back to the series. -/
private theorem assoc_formalAdd_universal :
    subst (Sum.elim
        (fun _ ↦ subst (Sum.elim
            (fun _ ↦ (X (Sum.inl ()) :
              MvPowerSeries (Unit ⊕ Unit ⊕ Unit) (MvPolynomial Coeff ℤ)))
            (fun _ ↦ X (Sum.inr (Sum.inl ()))) :
              Unit ⊕ Unit → MvPowerSeries (Unit ⊕ Unit ⊕ Unit) (MvPolynomial Coeff ℤ))
          (formalAdd Universal.curve))
        (fun _ ↦ X (Sum.inr (Sum.inr ()))) :
          Unit ⊕ Unit → MvPowerSeries (Unit ⊕ Unit ⊕ Unit) (MvPolynomial Coeff ℤ))
      (formalAdd Universal.curve) =
    subst (Sum.elim
        (fun _ ↦ (X (Sum.inl ()) :
          MvPowerSeries (Unit ⊕ Unit ⊕ Unit) (MvPolynomial Coeff ℤ)))
        (fun _ ↦ subst (Sum.elim
            (fun _ ↦ (X (Sum.inr (Sum.inl ())) :
              MvPowerSeries (Unit ⊕ Unit ⊕ Unit) (MvPolynomial Coeff ℤ)))
            (fun _ ↦ X (Sum.inr (Sum.inr ()))) :
              Unit ⊕ Unit → MvPowerSeries (Unit ⊕ Unit ⊕ Unit) (MvPolynomial Coeff ℤ))
          (formalAdd Universal.curve)) :
          Unit ⊕ Unit → MvPowerSeries (Unit ⊕ Unit ⊕ Unit) (MvPolynomial Coeff ℤ))
      (formalAdd Universal.curve) := by
  classical
  set R := MvPolynomial Coeff ℤ with hR
  set KK := FractionRing (MvPowerSeries (Unit ⊕ Unit ⊕ Unit) R) with hKK
  -- the specialization separating the first parameter from the other two
  set χ := coordSpecialize (O := R) (Sum.inl () : Unit ⊕ Unit ⊕ Unit) with hχdef
  have hχ : HasSubst χ := hasSubst_coordSpecialize _
  have hΔ := fracCurve_universal_Δ_ne_zero KK
  have hc₁ : constantCoeff (X (Sum.inl ()) : MvPowerSeries (Unit ⊕ Unit ⊕ Unit) R) = 0 :=
    constantCoeff_X _
  have hc₂ : constantCoeff (X (Sum.inr (Sum.inl ())) : MvPowerSeries (Unit ⊕ Unit ⊕ Unit) R) = 0 :=
    constantCoeff_X _
  have hc₃ : constantCoeff (X (Sum.inr (Sum.inr ())) : MvPowerSeries (Unit ⊕ Unit ⊕ Unit) R) = 0 :=
    constantCoeff_X _
  have h10 : (X (Sum.inl ()) : MvPowerSeries (Unit ⊕ Unit ⊕ Unit) R) ≠ 0 :=
    nonZeroDivisors.ne_zero X_mem_nonzeroDivisors
  have h20 : (X (Sum.inr (Sum.inl ())) : MvPowerSeries (Unit ⊕ Unit ⊕ Unit) R) ≠ 0 :=
    nonZeroDivisors.ne_zero X_mem_nonzeroDivisors
  have h30 : (X (Sum.inr (Sum.inr ())) : MvPowerSeries (Unit ⊕ Unit ⊕ Unit) R) ≠ 0 :=
    nonZeroDivisors.ne_zero X_mem_nonzeroDivisors
  have hχ1 := subst_coordSpecialize_X_self (O := R) (Sum.inl () : Unit ⊕ Unit ⊕ Unit)
  have hχ2 := subst_coordSpecialize_X_of_ne (O := R)
    (i := (Sum.inl () : Unit ⊕ Unit ⊕ Unit)) (j := Sum.inr (Sum.inl ())) (by simp)
  have hχ3 := subst_coordSpecialize_X_of_ne (O := R)
    (i := (Sum.inl () : Unit ⊕ Unit ⊕ Unit)) (j := Sum.inr (Sum.inr ())) (by simp)
  have hχ0 : subst χ (0 : MvPowerSeries (Unit ⊕ Unit ⊕ Unit) R) = 0 := by
    rw [← coe_substAlgHom hχ, map_zero]
  -- the second specialization, which separates the middle parameter from the third
  -- the specialization separating the middle parameter from the other two
  set χ' := coordSpecialize (O := R) (Sum.inr (Sum.inl ()) : Unit ⊕ Unit ⊕ Unit) with hχ'def
  have hχ' : HasSubst χ' := hasSubst_coordSpecialize _
  have hχ'2 := subst_coordSpecialize_X_self (O := R) (Sum.inr (Sum.inl ()) : Unit ⊕ Unit ⊕ Unit)
  have hχ'3 := subst_coordSpecialize_X_of_ne (O := R)
    (i := (Sum.inr (Sum.inl ()) : Unit ⊕ Unit ⊕ Unit)) (j := Sum.inr (Sum.inr ())) (by simp)
  -- the two inner sums
  set F₁₂ := subst (Sum.elim (fun _ ↦ (X (Sum.inl ()) : MvPowerSeries (Unit ⊕ Unit ⊕ Unit) R))
    (fun _ ↦ X (Sum.inr (Sum.inl ()))) : Unit ⊕ Unit → MvPowerSeries (Unit ⊕ Unit ⊕ Unit) R)
    (formalAdd Universal.curve) with hF₁₂def
  set F₂₃ := subst (Sum.elim
    (fun _ ↦ (X (Sum.inr (Sum.inl ())) : MvPowerSeries (Unit ⊕ Unit ⊕ Unit) R))
    (fun _ ↦ X (Sum.inr (Sum.inr ()))) : Unit ⊕ Unit → MvPowerSeries (Unit ⊕ Unit ⊕ Unit) R)
    (formalAdd Universal.curve) with hF₂₃def
  have hF₁₂c : constantCoeff F₁₂ = 0 :=
    constantCoeff_subst_pair_X_formalAdd Universal.curve _ _
  have hF₂₃c : constantCoeff F₂₃ = 0 :=
    constantCoeff_subst_pair_X_formalAdd Universal.curve _ _
  have hχF₁₂ : subst χ F₁₂ = PowerSeries.X :=
    subst_subst_pair_formalAdd_eq_X Universal.curve hχ hc₁ hc₂ hχ1 hχ2
  have hχF₂₃ : subst χ F₂₃ = 0 :=
    subst_subst_pair_formalAdd_eq_zero Universal.curve hχ hc₂ hc₃ hχ2 hχ3
  -- each inner sum is nonzero: the specialization that separates its own two parameters
  -- sends it to `X`, and `X ≠ 0`
  have hχ'0 : subst χ' (0 : MvPowerSeries (Unit ⊕ Unit ⊕ Unit) R) = 0 := by
    rw [← coe_substAlgHom hχ', map_zero]
  have hF₁₂0 : F₁₂ ≠ 0 := ne_of_subst_eq_X_of_subst_eq_zero hχF₁₂ hχ0
  have hF₂₃0 : F₂₃ ≠ 0 := ne_of_subst_eq_X_of_subst_eq_zero
    (subst_subst_pair_formalAdd_eq_X Universal.curve hχ' hc₂ hc₃ hχ'2 hχ'3) hχ'0
  -- the two bracketed sums are again legitimate parameters
  have hLc := constantCoeff_subst_eq_zero (hasSubst_pair hF₁₂c hc₃)
    (by rintro (j | j) <;> simp [hF₁₂c]) (constantCoeff_formalAdd Universal.curve)
  have hRc := constantCoeff_subst_eq_zero (hasSubst_pair hc₁ hF₂₃c)
    (by rintro (j | j) <;> simp [hF₂₃c]) (constantCoeff_formalAdd Universal.curve)
  have hL0 := ne_of_subst_eq_X_of_subst_eq_zero
    (subst_subst_pair_formalAdd_eq_X Universal.curve hχ hF₁₂c hc₃ hχF₁₂ hχ3) hχ0
  have hR0 := ne_of_subst_eq_X_of_subst_eq_zero
    (subst_subst_pair_formalAdd_eq_X Universal.curve hχ hc₁ hF₂₃c hχ1 hχF₂₃) hχ0
  -- the θ-chain: both bracketings compute the same sum of three points, each addition licensed
  -- by the specialization that separates its two summands
  have e₁₂ := thetaPoint_add_of_subst_separates Universal.curve (KK := KK) hΔ hχ hc₁ hc₂ h10 h20
    hχ1 hχ2 hF₁₂c hF₁₂0
  have e₂₃ := thetaPoint_add_of_subst_separates Universal.curve (KK := KK) hΔ hχ' hc₂ hc₃ h20 h30
    hχ'2 hχ'3 hF₂₃c hF₂₃0
  have eL := thetaPoint_add_of_subst_separates Universal.curve (KK := KK) hΔ hχ hF₁₂c hc₃ hF₁₂0
    h30 hχF₁₂ hχ3 hLc hL0
  have eR := thetaPoint_add_of_subst_separates Universal.curve (KK := KK) hΔ hχ hc₁ hF₂₃c h10
    hF₂₃0 hχ1 hχF₂₃ hRc hR0
  have hpts : Universal.curve.thetaPoint hΔ hLc hL0 = Universal.curve.thetaPoint hΔ hRc hR0 := by
    rw [← eL, ← e₁₂, ← eR, ← e₂₃, add_assoc]
  exact thetaPoint_inj Universal.curve hΔ hLc hRc hL0 hR0 hpts

omit [IsDomain O] in
/-- **Associativity of the chord addition series**, for every Weierstrass curve over every
commutative ring: `F(F(t₁, t₂), t₃) = F(t₁, F(t₂, t₃))`.

The chord construction proves this only where the curve has a group law to borrow, so the
identity is proved for the universal curve — whose base `ℤ[A₁, ⋯, A₆]` is a domain, and whose
series ring therefore has a fraction field — and `map_specialize` carries it to every `W`.

The three variables are indexed by `Unit ⊕ Unit ⊕ Unit`, with the two bracketings written as
nested substitutions of `formalAdd` into itself. -/
theorem formalAdd_assoc :
    subst (Sum.elim
        (fun _ ↦ subst (Sum.elim
            (fun _ ↦ (X (Sum.inl ()) : MvPowerSeries (Unit ⊕ Unit ⊕ Unit) O))
            (fun _ ↦ X (Sum.inr (Sum.inl ()))) :
              Unit ⊕ Unit → MvPowerSeries (Unit ⊕ Unit ⊕ Unit) O)
          (formalAdd W))
        (fun _ ↦ X (Sum.inr (Sum.inr ()))) :
          Unit ⊕ Unit → MvPowerSeries (Unit ⊕ Unit ⊕ Unit) O)
      (formalAdd W) =
    subst (Sum.elim
        (fun _ ↦ (X (Sum.inl ()) : MvPowerSeries (Unit ⊕ Unit ⊕ Unit) O))
        (fun _ ↦ subst (Sum.elim
            (fun _ ↦ (X (Sum.inr (Sum.inl ())) : MvPowerSeries (Unit ⊕ Unit ⊕ Unit) O))
            (fun _ ↦ X (Sum.inr (Sum.inr ()))) :
              Unit ⊕ Unit → MvPowerSeries (Unit ⊕ Unit ⊕ Unit) O)
          (formalAdd W)) :
          Unit ⊕ Unit → MvPowerSeries (Unit ⊕ Unit ⊕ Unit) O)
      (formalAdd W) := by
  have h := congrArg (MvPowerSeries.map W.specialize) assoc_formalAdd_universal
  rw [MvPowerSeries.map_subst (hasSubst_pair
      (constantCoeff_subst_pair_X_formalAdd Universal.curve _ _) (constantCoeff_X _)),
    MvPowerSeries.map_subst (hasSubst_pair (constantCoeff_X _)
      (constantCoeff_subst_pair_X_formalAdd Universal.curve _ _)),
    ← map_formalAdd] at h
  refine .trans ?_ (.trans h ?_)
  all_goals
    congr 1
    · funext i
      rcases i with u | u <;> simp [map_subst_pair_X_formalAdd, map_specialize]
    · simp [map_specialize]

end WeierstrassCurve

end
