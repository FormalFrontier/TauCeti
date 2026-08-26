/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.WExpansion
public import TauCeti.RingTheory.MvPowerSeries.Equiv

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
`rename_swap_slopeSeries`, `rename_swap_interceptSeries`, `rename_swap_invOfUnit` and
`rename_swap_thirdRootSeries`. The source's `wSeries` and `vSeries` are `formalW` and `formalU`,
so neither is re-ported and everything here is stated over the existing `w`-expansion API. Where
the source writes `MvPowerSeries.rename (fun _ => i)`, this file uses the equal Mathlib map
`PowerSeries.toMvPowerSeries i`.
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

/-- Renaming commutes with `invOfUnit` on a series with constant coefficient `1`. -/
private theorem rename_swap_invOfUnit {D : MvPowerSeries (Unit ⊕ Unit) R}
    (hD : constantCoeff D = 1) :
    rename Sum.swap (invOfUnit D 1) = invOfUnit (rename Sum.swap D) 1 := by
  have h1 : rename Sum.swap D * rename Sum.swap (invOfUnit D 1) = 1 := by
    rw [← map_mul, mul_invOfUnit D 1 (by rw [hD]; rfl), map_one]
  have h2 : rename Sum.swap D * invOfUnit (rename Sum.swap D) 1 = 1 :=
    mul_invOfUnit _ 1 (by rw [constantCoeff_rename, hD]; rfl)
  calc rename Sum.swap (invOfUnit D 1)
      = rename Sum.swap (invOfUnit D 1) *
        (rename Sum.swap D * invOfUnit (rename Sum.swap D) 1) := by rw [h2, mul_one]
    _ = (rename Sum.swap D * rename Sum.swap (invOfUnit D 1)) *
        invOfUnit (rename Sum.swap D) 1 := by ring
    _ = invOfUnit (rename Sum.swap D) 1 := by rw [h1, one_mul]

/-- The third point of the chord is unchanged by exchanging the two parameters. This is what
makes the formal group law commutative. -/
theorem rename_swap_formalThirdRoot :
    rename Sum.swap (formalThirdRoot W) = formalThirdRoot W := by
  have hD : constantCoeff (1 + C W.a₂ * formalSlope W + C W.a₄ * formalSlope W ^ 2 +
      C W.a₆ * formalSlope W ^ 3) = 1 := by
    simp
  rw [formalThirdRoot_def]
  simp only [map_sub, map_neg, map_add, map_mul, map_pow, map_one, map_ofNat, rename_X,
    rename_C, rename_swap_formalSlope, rename_swap_formalIntercept, rename_swap_invOfUnit hD]
  simp only [show Sum.swap (Sum.inl () : Unit ⊕ Unit) = Sum.inr () from rfl,
    show Sum.swap (Sum.inr () : Unit ⊕ Unit) = Sum.inl () from rfl]
  ring

end CommRing

end WeierstrassCurve
