/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.WExpansion
public import TauCeti.RingTheory.MvPowerSeries.Equiv
public import TauCeti.RingTheory.MvPowerSeries.Inverse
public import TauCeti.RingTheory.MvPowerSeries.NonZeroDivisors

/-!
# The chord through two points of a Weierstrass curve near the origin

The `w`-expansion of `WeierstrassCurve.formalW` lives in the coordinates `z = -x/y`, `w = -1/y`
obtained from the affine coordinates of `W` by `x = z / w`, `y = -1 / w`. In those coordinates
the point at infinity is the origin, and the curve is parametrised near it by `z ↦ (z, w(z))`,
where `w(z)` solves the transformed Weierstrass equation. The `(z, w)` here are therefore *not*
the affine coordinates of `W`; everything below happens in the transformed chart.

The substitution turns an affine line of `W` into a relation `w = λ z + ν`, so the chord through
the two parameters `z₁` and `z₂` is described by a slope and an intercept, as power series in
`R⟦z₁, z₂⟧` — variables indexed by `Unit ⊕ Unit`, as in Mathlib's formal-group-law conventions.
Substituting `w = λ z + ν` into the transformed equation leaves a cubic in `z`, whose three roots
are the parameters of the three points in which the chord meets the curve; the third of them is
`formalThirdRoot`.

Together these are the data of the chord construction: the formal group law of `W` is obtained
from `formalThirdRoot` by composing with the formal inverse, which is left to a later file.

## Main definitions

* `WeierstrassCurve.formalSlope`: the slope `λ(z₁, z₂) = (w(z₂) - w(z₁)) / (z₂ - z₁)` of the
  chord, defined through its coefficients rather than as a quotient.
* `WeierstrassCurve.formalIntercept`: the intercept `ν(z₁, z₂) = w(z₁) - λ(z₁, z₂) z₁`.
* `WeierstrassCurve.formalThirdRoot`: the parameter `z₃(z₁, z₂)` of the third point in which
  the chord meets the curve, obtained from Vieta's formulas.

## Main results

* `WeierstrassCurve.coeff_formalSlope`, `WeierstrassCurve.formalIntercept_def` and
  `WeierstrassCurve.formalThirdRoot_def`: the defining formulas, as named lemmas. Rewrite with
  these rather than unfolding the definitions.
* `WeierstrassCurve.formalSlope_mul_sub`: the defining property `λ · (z₂ - z₁) = w(z₂) - w(z₁)`
  of the slope, which is what justifies calling it a divided difference.
* `WeierstrassCurve.rename_swap_formalSlope`, `_formalIntercept`, `_formalThirdRoot`: all three
  series are invariant under exchanging the two parameters, so the chord depends on the two
  points and not on their order. This is what makes the eventual group law commutative.
* `WeierstrassCurve.formalIntercept_eq_inr`: the intercept computed from the second point.
* `WeierstrassCurve.constantCoeff_formalSlope`, `_formalIntercept`, `_formalThirdRoot`: all
  three series vanish at the origin.
* `WeierstrassCurve.subst_formalThirdRoot_formalW`: the third point really lies on the chord —
  reading the `w`-expansion at `formalThirdRoot` returns the chord line read there. This is what
  makes the third root the parameter of an intersection point rather than merely a root of the
  cubic.

## Implementation notes

`formalSlope` is defined by the coefficient formula rather than as a quotient of power series:
`z₂ - z₁` is not a unit in `R⟦z₁, z₂⟧`, so the divided difference has to be written down
directly and `formalSlope_mul_sub` recovers the property that names it.

The slope and its coefficients need no subtraction, so they are stated over a `CommSemiring`,
matching `formalW`. Everything from `formalSlope_mul_sub` onwards subtracts, and so is stated
over a `CommRing`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1.

## Provenance

Adapted from Michael Stoll's `EllipticCurves` project
(`github.com/MichaelStollBayreuth/EllipticCurves`, Apache-2.0, pinned by
`TauCetiRoadmap/EllipticCurves/README.md` at `66889eada51a`),
`EllipticCurves/WeierstrassFormalGroup/Chord.lean`, its `Chord` section down to the third-root
series together with the swap-invariance block — declarations `slopeSeries`, `coeff_slopeSeries`,
`slopeSeries_mul_sub`, `interceptSeries`, `interceptSeries_eq`, `constantCoeff_slopeSeries`,
`constantCoeff_interceptSeries`, `thirdRootSeries`, `constantCoeff_thirdRootSeries`,
`rename_swap_slopeSeries`, `rename_swap_interceptSeries` and `rename_swap_thirdRootSeries`.
The source's `rename_swap_invOfUnit` is not ported: it is the general
`MvPowerSeries.ringHom_invOfUnit` specialised to `rename Sum.swap`, and is used as such.

The source's `wSeries` and `vSeries` are `formalW` and `formalU`, so neither is re-ported and
everything here is stated over the existing `w`-expansion API. Where
the source writes `MvPowerSeries.rename (fun _ => i)`, this file uses the equal Mathlib map
`PowerSeries.toMvPowerSeries i`.

The on-line section is adapted from the same project's
`EllipticCurves/WeierstrassFormalGroup/GroupLaw.lean`, its `Domain` section — declarations
`line_at_thirdRoot` and `subst_thirdRootSeries_wSeries`. Four of that section's steps are not
ported. `X_inl_ne_X_inr` is not needed at all: the cancellation runs through
`MvPowerSeries.X_sub_X_mem_nonZeroDivisors`, which never separates the two variables. The other
three this repository already has — `line_left` and `line_right` are `formalIntercept_def` and
`formalIntercept_eq_inr` with the terms moved across the equals sign, and `wsAt_rename` is
`subst_formalW_wEquation` read through Mathlib's `PowerSeries.toMvPowerSeries_eq_subst`; all
three are inlined at their single use site. The source's `LowVanish` hypotheses have no counterpart
here at all, since `eq_of_wEquation_mvPowerSeries` takes vanishing constant coefficients
directly.

The source guards `line_at_thirdRoot` with `set_option maxRecDepth 4000 in`. That is not ported:
TauCeti's CI forbids `set_option` under `TauCeti/`, and the proof elaborates at the default
depth here, so the guard was never load-bearing for this statement.
-/

public section

namespace WeierstrassCurve

open MvPowerSeries

private theorem eq_single_inr_iff (d : Unit ⊕ Unit →₀ ℕ) :
    d = Finsupp.single (Sum.inr ()) (d (Sum.inr ())) ↔ d (Sum.inl ()) = 0 := by
  refine ⟨fun h => by rw [h]; simp, fun h => ?_⟩
  ext t
  match t with
  | .inl () => simpa using h
  | .inr () => simp

private theorem eq_single_inl_iff (d : Unit ⊕ Unit →₀ ℕ) :
    d = Finsupp.single (Sum.inl ()) (d (Sum.inl ())) ↔ d (Sum.inr ()) = 0 := by
  refine ⟨fun h => by rw [h]; simp, fun h => ?_⟩
  ext t
  match t with
  | .inl () => simp
  | .inr () => simpa using h

section CommSemiring

variable {R : Type*} [CommSemiring R] (W : WeierstrassCurve R)

/-! ### The slope of the chord -/

/-- The slope of the chord through the points with parameters `z₁` and `z₂`, that is, the
divided difference `λ(z₁, z₂) = (w(z₂) - w(z₁)) / (z₂ - z₁)`.

It is defined through its coefficients: the coefficient of `z₁ ^ i * z₂ ^ j` is the coefficient
of `z ^ (i + j + 1)` in `w(z)`. See `formalSlope_mul_sub` for the property this encodes. -/
noncomputable def formalSlope : MvPowerSeries (Unit ⊕ Unit) R :=
  fun d => PowerSeries.coeff (d (Sum.inl ()) + d (Sum.inr ()) + 1) (formalW W)

/-- The defining formula for `formalSlope`: the coefficient of `z₁ ^ i * z₂ ^ j` in the slope is
the coefficient of `z ^ (i + j + 1)` in `w(z)`. -/
@[simp]
theorem coeff_formalSlope (d : Unit ⊕ Unit →₀ ℕ) :
    coeff d (formalSlope W) =
      PowerSeries.coeff (d (Sum.inl ()) + d (Sum.inr ()) + 1) (formalW W) :=
  (rfl)

/-- The slope of the chord vanishes at the origin. -/
@[simp]
theorem constantCoeff_formalSlope : constantCoeff (formalSlope W) = 0 := by
  have h : constantCoeff (formalSlope W) =
      PowerSeries.coeff ((0 : Unit ⊕ Unit →₀ ℕ) (Sum.inl ()) +
        (0 : Unit ⊕ Unit →₀ ℕ) (Sum.inr ()) + 1) (formalW W) :=
    coeff_formalSlope W 0
  rw [h, coeff_formalW]
  exact formalWCoeff_eq_zero_of_lt W (by simp)

/-- The slope is unchanged by exchanging the two parameters: it depends on the pair of points
and not on their order. -/
theorem rename_swap_formalSlope : rename Sum.swap (formalSlope W) = formalSlope W := by
  ext d
  have hswap : (⇑(Equiv.sumComm Unit Unit).toEmbedding ∘ Sum.swap) = id := by
    ext s
    match s with
    | .inl () => rfl
    | .inr () => rfl
  have hd : d = Finsupp.embDomain (Equiv.sumComm Unit Unit).toEmbedding
      (Finsupp.mapDomain Sum.swap d) := by
    rw [Finsupp.embDomain_eq_mapDomain, ← Finsupp.mapDomain_comp, hswap, Finsupp.mapDomain_id]
  have hinl : Finsupp.mapDomain Sum.swap d (Sum.inl ()) = d (Sum.inr ()) := by
    rw [show (Sum.inl () : Unit ⊕ Unit) = (Equiv.sumComm Unit Unit) (Sum.inr ()) from rfl]
    exact (Finsupp.mapDomain_equiv_apply (f := Equiv.sumComm Unit Unit) d _).trans (by rfl)
  have hinr : Finsupp.mapDomain Sum.swap d (Sum.inr ()) = d (Sum.inl ()) := by
    rw [show (Sum.inr () : Unit ⊕ Unit) = (Equiv.sumComm Unit Unit) (Sum.inl ()) from rfl]
    exact (Finsupp.mapDomain_equiv_apply (f := Equiv.sumComm Unit Unit) d _).trans (by rfl)
  calc coeff d (rename Sum.swap (formalSlope W))
      = coeff (Finsupp.mapDomain Sum.swap d) (formalSlope W) := by
        conv_lhs => rw [hd]
        exact coeff_embDomain_rename _ _ _
    _ = coeff d (formalSlope W) := by
        rw [coeff_formalSlope, coeff_formalSlope, hinl, hinr, add_comm (d (Sum.inr ()))]

end CommSemiring

section CommRing

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- The defining property of the slope: `λ(z₁, z₂) * (z₂ - z₁) = w(z₂) - w(z₁)`. -/
theorem formalSlope_mul_sub :
    formalSlope W * (X (Sum.inr ()) - X (Sum.inl ())) =
      (formalW W).toMvPowerSeries (Sum.inr ()) - (formalW W).toMvPowerSeries (Sum.inl ()) := by
  ext d
  set i := d (Sum.inl ()) with hi
  set j := d (Sum.inr ()) with hj
  rw [mul_sub, map_sub, map_sub, X_def (Sum.inr ()), X_def (Sum.inl ()),
    coeff_mul_monomial, coeff_mul_monomial, PowerSeries.coeff_toMvPowerSeries,
    PowerSeries.coeff_toMvPowerSeries]
  have hsubr : 1 ≤ j → (d - Finsupp.single (Sum.inr ()) 1 : Unit ⊕ Unit →₀ ℕ) (Sum.inl ()) +
      (d - Finsupp.single (Sum.inr ()) 1 : Unit ⊕ Unit →₀ ℕ) (Sum.inr ()) + 1 = i + j := by
    intro h
    simp only [Finsupp.tsub_apply, Finsupp.single_apply]
    simp
    omega
  have hsubl : 1 ≤ i → (d - Finsupp.single (Sum.inl ()) 1 : Unit ⊕ Unit →₀ ℕ) (Sum.inl ()) +
      (d - Finsupp.single (Sum.inl ()) 1 : Unit ⊕ Unit →₀ ℕ) (Sum.inr ()) + 1 = i + j := by
    intro h
    simp only [Finsupp.tsub_apply, Finsupp.single_apply]
    simp
    omega
  simp only [mul_one, eq_single_inr_iff, eq_single_inl_iff, Finsupp.single_le_iff,
    coeff_formalSlope]
  split_ifs with h1 h2 h3 h4 <;> grind

/-! ### The intercept of the chord -/

/-- The intercept `ν(z₁, z₂) = w(z₁) - λ(z₁, z₂) z₁` of the chord through the points with
parameters `z₁` and `z₂`. -/
noncomputable def formalIntercept : MvPowerSeries (Unit ⊕ Unit) R :=
  (formalW W).toMvPowerSeries (Sum.inl ()) - formalSlope W * X (Sum.inl ())

/-- The defining formula for `formalIntercept`, in terms of the first point. -/
theorem formalIntercept_def :
    formalIntercept W =
      (formalW W).toMvPowerSeries (Sum.inl ()) - formalSlope W * X (Sum.inl ()) :=
  (rfl)

/-- The intercept computed from the second point is the same series. -/
theorem formalIntercept_eq_inr :
    formalIntercept W =
      (formalW W).toMvPowerSeries (Sum.inr ()) - formalSlope W * X (Sum.inr ()) := by
  have h := formalSlope_mul_sub W
  rw [formalIntercept_def]
  linear_combination h

/-- The intercept of the chord vanishes at the origin. -/
@[simp]
theorem constantCoeff_formalIntercept : constantCoeff (formalIntercept W) = 0 := by
  -- `constantCoeff_formalW` is stated for the `PowerSeries` spelling of the same map, so it is
  -- transported here by definitional equality rather than by a public restatement.
  have hW : constantCoeff (formalW W) = 0 := constantCoeff_formalW W
  rw [formalIntercept_def]
  simp [PowerSeries.toMvPowerSeries_apply, constantCoeff_rename, hW]

/-- The intercept is unchanged by exchanging the two parameters. -/
theorem rename_swap_formalIntercept :
    rename Sum.swap (formalIntercept W) = formalIntercept W := by
  rw [formalIntercept_def, map_sub, map_mul, rename_swap_formalSlope,
    MvPowerSeries.rename_toMvPowerSeries, rename_X]
  exact (formalIntercept_eq_inr W).symm

/-! ### The third point of the chord -/

/-- The denominator `1 + a₂λ + a₄λ² + a₆λ³` of Vieta's formula for the third root is `1` at the
origin, hence a unit. This is what lets `formalThirdRoot` divide by it, and it is recorded here
rather than reproved at each use. -/
@[simp]
theorem constantCoeff_formalThirdRootDenom :
    constantCoeff (1 + C W.a₂ * formalSlope W + C W.a₄ * formalSlope W ^ 2 +
      C W.a₆ * formalSlope W ^ 3) = 1 := by
  simp

/-- The parameter `z₃(z₁, z₂)` of the third point in which the chord through the points with
parameters `z₁` and `z₂` meets the curve.

Substituting `w = λ z + ν` into the transformed Weierstrass equation gives a cubic in `z` whose
roots are the three parameters, so by Vieta's formulas
`z₃ = -z₁ - z₂ - (a₁λ + a₂ν + a₃λ² + 2a₄λν + 3a₆λ²ν) / (1 + a₂λ + a₄λ² + a₆λ³)`,
the denominator being a unit because `λ` has vanishing constant coefficient. -/
noncomputable def formalThirdRoot : MvPowerSeries (Unit ⊕ Unit) R :=
  -X (Sum.inl ()) - X (Sum.inr ()) -
    (C W.a₁ * formalSlope W + C W.a₂ * formalIntercept W + C W.a₃ * formalSlope W ^ 2 +
        2 * C W.a₄ * formalSlope W * formalIntercept W +
        3 * C W.a₆ * formalSlope W ^ 2 * formalIntercept W) *
      invOfUnit (1 + C W.a₂ * formalSlope W + C W.a₄ * formalSlope W ^ 2 +
        C W.a₆ * formalSlope W ^ 3) 1

/-- The defining formula for `formalThirdRoot`, as read off Vieta's formulas. -/
theorem formalThirdRoot_def :
    formalThirdRoot W =
      -X (Sum.inl ()) - X (Sum.inr ()) -
        (C W.a₁ * formalSlope W + C W.a₂ * formalIntercept W + C W.a₃ * formalSlope W ^ 2 +
            2 * C W.a₄ * formalSlope W * formalIntercept W +
            3 * C W.a₆ * formalSlope W ^ 2 * formalIntercept W) *
          invOfUnit (1 + C W.a₂ * formalSlope W + C W.a₄ * formalSlope W ^ 2 +
            C W.a₆ * formalSlope W ^ 3) 1 :=
  (rfl)

/-- The parameter of the third point of the chord vanishes at the origin. -/
@[simp]
theorem constantCoeff_formalThirdRoot : constantCoeff (formalThirdRoot W) = 0 := by
  rw [formalThirdRoot_def]
  simp

/-- The third point of the chord is unchanged by exchanging the two parameters. This is what
makes the formal group law commutative. -/
theorem rename_swap_formalThirdRoot :
    rename Sum.swap (formalThirdRoot W) = formalThirdRoot W := by
  have hD := constantCoeff_formalThirdRootDenom W
  have hD' : constantCoeff (rename Sum.swap (1 + C W.a₂ * formalSlope W +
      C W.a₄ * formalSlope W ^ 2 + C W.a₆ * formalSlope W ^ 3)) = 1 := by
    rw [constantCoeff_rename]; exact hD
  rw [formalThirdRoot_def]
  simp only [map_sub, map_neg, map_add, map_mul, map_pow, map_one, map_ofNat, rename_X,
    rename_C, rename_swap_formalSlope, rename_swap_formalIntercept,
    MvPowerSeries.ringHom_invOfUnit (u := 1) (v := 1) (rename Sum.swap) hD hD']
  simp only [show Sum.swap (Sum.inl () : Unit ⊕ Unit) = Sum.inr () from rfl,
    show Sum.swap (Sum.inr () : Unit ⊕ Unit) = Sum.inl () from rfl]
  ring

/-- The two-variable family that substitutes `formalThirdRoot` for the single variable of a
one-variable series. Stated here, beside `formalThirdRoot` itself, because the substitution it
witnesses is used from this file onwards. -/
theorem hasSubst_formalThirdRoot :
    HasSubst (fun _ : Unit ↦ formalThirdRoot W) :=
  hasSubst_of_constantCoeff_zero fun _ ↦ constantCoeff_formalThirdRoot W

/-! ### The third point lies on the chord

Vieta's formulas produce `formalThirdRoot` from the coefficients of the chord cubic, which by
itself says nothing about where the curve meets that chord: it is an identity between series, not
a statement that the point with parameter `z₃` lies on the line `w = λ z + ν`. It does, and the
argument is the classical one — the cubic already has `z₁` and `z₂` among its roots, so cancelling
`z₁ - z₂` from the difference of the two identities pins the third.

That cancellation needs no hypothesis on `R`. The difference of two distinct variables is a
non-zero-divisor of `MvPowerSeries (Unit ⊕ Unit) R` over an arbitrary commutative ring
(`MvPowerSeries.X_sub_X_mem_nonZeroDivisors`), because the coefficient recursion behind it never
cancels anything in `R`.
-/

/-- The chord line, read at the third root, satisfies the `w`-equation at that parameter.

This is Vieta's formula in the form the uniqueness of the `w`-expansion can consume: the third
root is characterised here by *solving the equation*, not by its coefficient formula. -/
private theorem line_at_thirdRoot :
    formalSlope W * formalThirdRoot W + formalIntercept W =
      wEquationRHS W (formalThirdRoot W)
        (formalSlope W * formalThirdRoot W + formalIntercept W) := by
  -- The curve meets the chord at each of the two given parameters. Both are the `w`-equation at
  -- a variable, which is `subst_formalW_wEquation` read through `toMvPowerSeries`.
  have hline : ∀ i : Unit ⊕ Unit,
      (formalW W).toMvPowerSeries i =
        wEquationRHS W (X i) ((formalW W).toMvPowerSeries i) := by
    intro i
    rw [PowerSeries.toMvPowerSeries_eq_subst]
    exact subst_formalW_wEquation W (PowerSeries.HasSubst.X i)
  -- The chord passes through both of its own endpoints. `Unit ⊕ Unit` has exactly the two
  -- elements `inl ()` and `inr ()`, so the case split is exhaustive and the two endpoints share
  -- one argument: `formalIntercept` is defined from the first point and `formalIntercept_eq_inr`
  -- says the second point gives the same series.
  have hchord : ∀ i : Unit ⊕ Unit,
      formalSlope W * X i + formalIntercept W = (formalW W).toMvPowerSeries i := by
    rintro (⟨⟩ | ⟨⟩)
    · rw [formalIntercept_def]; ring
    · rw [formalIntercept_eq_inr]; ring
  have hC : ∀ i : Unit ⊕ Unit, formalSlope W * X i + formalIntercept W =
      wEquationRHS W (X i) (formalSlope W * X i + formalIntercept W) := fun i =>
    (hchord i).trans ((hline i).trans (by rw [hchord i]))
  have hC1 := hC (Sum.inl ())
  have hC2 := hC (Sum.inr ())
  have hAd : (1 + C W.a₂ * formalSlope W + C W.a₄ * formalSlope W ^ 2 +
      C W.a₆ * formalSlope W ^ 3) *
      invOfUnit (1 + C W.a₂ * formalSlope W + C W.a₄ * formalSlope W ^ 2 +
        C W.a₆ * formalSlope W ^ 3) 1 = 1 :=
    mul_invOfUnit _ 1 (by simp)
  simp only [wEquationRHS_def, ← c_eq_algebraMap] at hC1 hC2 ⊢
  rw [formalThirdRoot_def]
  set Λ := formalSlope W
  set N := formalIntercept W
  set t₁ := (X (Sum.inl ()) : MvPowerSeries (Unit ⊕ Unit) R) with ht₁
  set t₂ := (X (Sum.inr ()) : MvPowerSeries (Unit ⊕ Unit) R) with ht₂
  set d := invOfUnit (1 + C W.a₂ * Λ + C W.a₄ * Λ ^ 2 + C W.a₆ * Λ ^ 3) 1
  -- Cancel `t₁ - t₂` from the difference of the two identities: what survives is the linear
  -- coefficient of the chord cubic, which is what Vieta's formula divides by the leading one.
  have hsub : (t₁ - t₂) * (-(1 + C W.a₂ * Λ + C W.a₄ * Λ ^ 2 + C W.a₆ * Λ ^ 3) *
      (t₁ ^ 2 + t₁ * t₂ + t₂ ^ 2) -
      (C W.a₁ * Λ + C W.a₂ * N + C W.a₃ * Λ ^ 2 + 2 * C W.a₄ * Λ * N +
        3 * C W.a₆ * Λ ^ 2 * N) * (t₁ + t₂) +
      (Λ - (C W.a₁ * N + 2 * C W.a₃ * Λ * N + C W.a₄ * N ^ 2 +
        3 * C W.a₆ * Λ * N ^ 2))) = 0 := by
    linear_combination hC1 - hC2
  have hreg : ∀ x : MvPowerSeries (Unit ⊕ Unit) R, (t₁ - t₂) * x = 0 → x = 0 := by
    rw [ht₁, ht₂]
    exact (X_sub_X_mem_nonZeroDivisors (by simp)).1
  have hE1 := hreg _ hsub
  clear_value Λ N t₁ t₂ d
  set B := C W.a₁ * Λ + C W.a₂ * N + C W.a₃ * Λ ^ 2 + 2 * C W.a₄ * Λ * N +
    3 * C W.a₆ * Λ ^ 2 * N with hB
  set T := -t₁ - t₂ - B * d with hT
  clear_value B T
  linear_combination hC1 + (T - t₁) * hE1 + ((T - t₁) * (T - t₂) * B) * hAd -
    ((T - t₁) * (T - t₂) * (1 + C W.a₂ * Λ + C W.a₄ * Λ ^ 2 + C W.a₆ * Λ ^ 3)) * hT +
    (T ^ 2 - t₁ ^ 2) * hB

/-- **The third intersection point lies on the chord.** Reading the `w`-expansion at the third
root gives the chord line read there: `w(z₃(z₁, z₂)) = λ(z₁, z₂) · z₃(z₁, z₂) + ν(z₁, z₂)`.

This is what makes `formalThirdRoot` the parameter of an actual third intersection point rather
than merely the third root of a cubic, and it is the identity the addition series is built on. -/
@[simp]
theorem subst_formalThirdRoot_formalW :
    subst (fun _ : Unit ↦ formalThirdRoot W) (formalW W) =
      formalSlope W * formalThirdRoot W + formalIntercept W := by
  refine eq_of_wEquation_mvPowerSeries W (constantCoeff_formalThirdRoot W) ?_ ?_ ?_
    (line_at_thirdRoot W)
  · exact constantCoeff_subst_eq_zero (hasSubst_formalThirdRoot W)
      (fun _ ↦ constantCoeff_formalThirdRoot W) (constantCoeff_formalW W)
  · simp
  · exact subst_formalW_wEquation W (PowerSeries.HasSubst.of_constantCoeff_zero
      (constantCoeff_formalThirdRoot W))


/-! ### Base change

The chord data is built from `formalW` and the coefficients by ring operations, so it commutes
with base change; `WExpansion.lean` has the corresponding statement for the `w`-expansion itself.
-/

section BaseChange

variable {S : Type*} [CommRing S] (φ : R →+* S)

/-- The slope of the chord commutes with base change. -/
@[simp]
theorem map_formalSlope :
    formalSlope (W.map φ) = MvPowerSeries.map φ (formalSlope W) := by
  ext d
  rw [MvPowerSeries.coeff_map, coeff_formalSlope, coeff_formalSlope, map_formalW W φ,
    PowerSeries.coeff_map]

/-- The intercept of the chord commutes with base change. -/
@[simp]
theorem map_formalIntercept :
    formalIntercept (W.map φ) = MvPowerSeries.map φ (formalIntercept W) := by
  rw [formalIntercept_def, formalIntercept_def, map_sub, map_mul, MvPowerSeries.map_X,
    map_formalSlope W φ, map_formalW W φ, PowerSeries.map_toMvPowerSeries]

/-- The parameter of the third point of the chord commutes with base change. -/
@[simp]
theorem map_formalThirdRoot :
    formalThirdRoot (W.map φ) = MvPowerSeries.map φ (formalThirdRoot W) := by
  have hinv := MvPowerSeries.ringHom_invOfUnit (σ := Unit ⊕ Unit) (τ := Unit ⊕ Unit)
    (MvPowerSeries.map φ)
    (D := 1 + C W.a₂ * formalSlope W + C W.a₄ * formalSlope W ^ 2 + C W.a₆ * formalSlope W ^ 3)
    (u := 1) (v := 1) (constantCoeff_formalThirdRootDenom W)
    (by rw [MvPowerSeries.constantCoeff_map, constantCoeff_formalThirdRootDenom]; simp)
  rw [formalThirdRoot_def, formalThirdRoot_def]
  simp only [map_sub, map_neg, map_add, map_one, map_mul, map_pow, map_ofNat,
    MvPowerSeries.map_X, MvPowerSeries.map_C, map_formalSlope W φ, map_formalIntercept W φ,
    hinv, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆]

end BaseChange

end CommRing

end WeierstrassCurve
