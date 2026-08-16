/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.FieldTheory.RatFunc.Valuation
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.Norm

/-!
# The valuation at infinity on the function field of a Weierstrass curve

The function field `F(W)` of an affine Weierstrass curve is a quadratic extension of the rational
function field `F(x)` (`WeierstrassCurve.Affine.finrank_functionField`), so every function has an
algebra norm there. Composing that norm with Mathlib's place at infinity of `F(x)` gives the place
at infinity of the curve: `ord_∞ f = -deg N f`, the place where `x` and `y` have their poles.

## Main definitions

* `WeierstrassCurve.Affine.infinityPlace`: the valuation at infinity,
  `Valuation W.FunctionField (WithZero (Multiplicative ℤ))`, as `RatFunc.inftyValuation` composed
  with `Algebra.norm`.

## Main results

The valuation's `map_add_le_max'` rests on an ultrametric inequality in degree form, proved here;
the other three axioms are the norm's multiplicativity and Mathlib's place at infinity.
* `WeierstrassCurve.Affine.infinityPlace.X`,
  `WeierstrassCurve.Affine.infinityPlace.mk_Y`: `v_∞ x = exp 2` and `v_∞ y = exp 3` — the double
  and triple poles at infinity, `ord_∞ x = -2` and `ord_∞ y = -3`, which is what Layer 0 asks for
  by name. They read this file's two `natDegree_norm_*` helpers through
  `Algebra.norm_localization` and Mathlib's polynomial valuation.
* `WeierstrassCurve.Affine.infinityPlace.algebraMap_eq_sq`: restricting along
  `RatFunc F → W.FunctionField` squares `RatFunc.inftyValuation`, so the place at infinity is
  ramified of index two over the infinite place of `F(x)`.
* `WeierstrassCurve.Affine.infinityPlace.C`: the valuation is trivial on the base field — a
  nonzero constant has value `1`, the constant case of the previous result. The
  `Valuation.IsTrivialOn F` and `Valuation.IsNontrivial` instances follow, so the place is usable
  through Mathlib's standard valuation API.
* `WeierstrassCurve.Affine.infinityPlace.X_div_mk_Y` and
  `WeierstrassCurve.Affine.infinityPlace.isUniformizer_X_div_mk_Y`: **`x / y` is a uniformiser at
  infinity.** Its value is `exp (-1)`, and it is a uniformiser in Mathlib's
  `Valuation.IsUniformizer` sense. That the place is discrete of rank one needs no proof here — its
  value group is a nontrivial subgroup of the cyclic `ℤᵐ⁰ˣ`, so Mathlib's `IsRankOneDiscrete`
  instance fires by itself — but the *generator* does: discreteness alone permits `exp (-n)` with
  `n ≥ 1`, and the proper subgroup `2ℤ` genuinely occurs, being the value group of the restriction
  of `v_∞` to `F(x)`. One element of value `exp (-1)` settles it, which is what the value above is.
* `WeierstrassCurve.Affine.infinityPlace_ne_heightOneSpectrum_valuation`: the place at infinity is
  distinct from the valuation of every height-one prime of the coordinate ring — the affine places.
  With `CoordinateRing.pointPlace_eq_iff` that makes the whole point-to-place assignment injective,
  the point at infinity included.

The two coordinate-function values each come in a second `@[simp]` form, stated in the shape simp
actually normalises them to (the note above `infinityPlace.X` explains why the coordinate forms
cannot carry the tag themselves). The quotient value gets no restatement of its own: `map_div₀`
is a simp lemma, so simp decomposes the quotient through the two atomic restatements. The
machinery that builds the ultrametric inequality is `private`, and the norm-degree theory it
rests on lives in `FunctionField/Norm.lean`.

## Roadmap

`TauCetiRoadmap/EllipticCurves/README.md`, **Layer 0** (the function field, places, and divisors),
whose §Places asks for the one further place `W.infinityPlace` beyond the affine ones, sitting
"where `x` and `y` have their poles", with `ord_∞ x = -2`, `ord_∞ y = -3`. This file supplies the
valuation, those two degrees, and the **uniformiser** `x / y` — §Places lists "`ord_v`,
uniformisers, residue fields, the degree `deg v`" as the API the later layers consume.
`Suggested.lean` seeds no declaration it competes with, recording that the function-field layer's
"types are new API and are built there, not pinned here".

## Provenance

The route is that of the AINTLIB `HasseWeil` project (`github.com/CBirkbeck/AINTLIB`, Apache-2.0,
`dev/hasse-weil` at `a582951fe96b`), `HasseWeil/Curves/Infinity.lean`: `normAsRatFunc`,
`ordAtInfty`, `ordAtInfty_mul`, `ordAtInfty_add_ge_min` (tagged T-ORD-ARITH-12) and
`ordAtInfty_coordX`/`ordAtInfty_coordY`.

The ramification statement corresponds to that project's `Curves/OrdAtInftyRamification.lean` and
`Curves/RamificationAtInfinity.lean`; there it is an order identity for a `WithTop ℤ`-valued
`ordAtInfty` over the `SmoothPlaneCurve` wrapper, where here it is an equality of Mathlib
`Valuation`s and follows from `Algebra.norm_algebraMap` with `finrank_functionField`.

Changes from the source. There `ordAtInfty` is a definition of its own, valued in `WithTop ℤ`, built
over a `SmoothPlaneCurve` structure wrapping `WeierstrassCurve.Affine`, with multiplicativity,
vanishing and the ultrametric bound all proved by hand. Here the norm is Mathlib's `Algebra.norm`
and the target is Mathlib's `ℤᵐ⁰`, so the result is a genuine `Valuation` uniform with
`RatFunc.inftyValuation` and `IsDedekindDomain.HeightOneSpectrum.valuation`; multiplicativity and
vanishing are `map_mul` and `Algebra.norm_zero`, and only the ultrametric inequality is
reproved.

The uniformiser corresponds to that project's
`projects/HasseWeil/HasseWeil/Foundation/LocalExpansion.lean` at `main` `1c1c7466`, `localParam` —
the local parameter `t = -x/y` at `O` (Silverman IV.1) — whose uniformising property is recorded
there through a Laurent-series embedding (`localExpand_localParam`), over a `SmoothPlaneCurve` and
that development's own `WithTop ℤ`-valued `ordAtInfty`. None of that apparatus is needed here: the
value of `x / y` is two rewrites from the two pole orders, and Mathlib's
`Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_mem_range` turns that single value into the
generator, so the conclusion is Mathlib's `Valuation.IsUniformizer` directly. The sign is dropped,
`x / y` and `-x / y` having the same valuation.
-/

public section

open Polynomial WeierstrassCurve

open scoped Polynomial.Bivariate RatFunc

namespace WeierstrassCurve.Affine


section Nontrivial

variable {R : Type*} [CommRing R] [Nontrivial R] (W : WeierstrassCurve.Affine R)

/-- The norm of the coordinate function `x` has degree `2`: it is `x ^ 2`. Private: it exists to
compute `infinityPlace.X`, and Mathlib's `Algebra.norm_algebraMap` is the general fact. -/
private theorem natDegree_norm_X :
    (Algebra.norm R[X] (algebraMap R[X] W.CoordinateRing Polynomial.X)).natDegree = 2 := by
  rw [Algebra.norm_algebraMap, finrank_coordinateRing, natDegree_X_pow]

/-- The norm of the coordinate function `y` has degree `3`: it is `-(X³ + a₂X² + a₄X + a₆)`.
Private: it exists to compute `infinityPlace.mk_Y`. Unlike `x`, the function `y` does not come
from `R[X]`, so the general fact is the basis decomposition `CoordinateRing.norm_smul_basis`. -/
private theorem natDegree_norm_mk_Y :
    (Algebra.norm R[X] (CoordinateRing.mk W Y)).natDegree = 3 := by
  have hY : CoordinateRing.mk W Y = (0 : R[X]) • 1 + (1 : R[X]) • CoordinateRing.mk W Y := by simp
  rw [hY, CoordinateRing.norm_smul_basis]
  compute_degree!

end Nontrivial


section DomainCore

variable {R : Type*} [CommRing R] [IsDomain R] (W : WeierstrassCurve.Affine R)

/-- **The ultrametric inequality at the polynomial level**: the norm degree of a sum of two
basis-decomposed elements is at most the larger of the two. No denominators, no case analysis —
`degree` in `WithBot` handles the zero cases. -/
private theorem degree_norm_add_le (a₁ b₁ a₂ b₂ : R[X]) :
    (Algebra.norm R[X] ((a₁ + a₂) • (1 : W.CoordinateRing)
        + (b₁ + b₂) • CoordinateRing.mk W Y)).degree
      ≤ max (Algebra.norm R[X] (a₁ • 1 + b₁ • CoordinateRing.mk W Y)).degree
            (Algebra.norm R[X] (a₂ • 1 + b₂ • CoordinateRing.mk W Y)).degree := by
  rw [CoordinateRing.degree_norm_smul_basis, CoordinateRing.degree_norm_smul_basis,
    CoordinateRing.degree_norm_smul_basis, max_max_max_comm, max_add_add_right,
    ← smul_max_of_nonneg (Nat.zero_le 2), ← smul_max_of_nonneg (Nat.zero_le 2)]
  gcongr <;> exact degree_add_le _ _

/-- The `natDegree` form, and it needs no nonzero hypotheses at all: `natDegree_le_natDegree`
carries the `WithBot` bound across, and `natDegree 0 = 0` makes the zero cases hold anyway. -/
private theorem natDegree_norm_add_le (a₁ b₁ a₂ b₂ : R[X]) :
    (Algebra.norm R[X] ((a₁ + a₂) • (1 : W.CoordinateRing)
        + (b₁ + b₂) • CoordinateRing.mk W Y)).natDegree
      ≤ max (Algebra.norm R[X] (a₁ • 1 + b₁ • CoordinateRing.mk W Y)).natDegree
            (Algebra.norm R[X] (a₂ • 1 + b₂ • CoordinateRing.mk W Y)).natDegree :=
  le_max_iff.2 <| (le_max_iff.1 <| degree_norm_add_le W a₁ b₁ a₂ b₂).imp natDegree_le_natDegree
    natDegree_le_natDegree

end DomainCore


variable {F : Type*} [Field F] (W : WeierstrassCurve.Affine F)

/-- **Two functions over a common denominator**: `f = (a₁ + b₁ y) / p` and `g = (a₂ + b₂ y) / p`
with `p ≠ 0` — the form the degree formula consumes: numerators in the `1, Y` basis, one shared
polynomial denominator. -/
private theorem exists_common_smul_basis_div (f g : W.FunctionField) :
    ∃ a₁ b₁ a₂ b₂ p : F[X], p ≠ 0 ∧
      f * algebraMap F[X] W.FunctionField p =
        algebraMap W.CoordinateRing W.FunctionField (a₁ • 1 + b₁ • CoordinateRing.mk W Y) ∧
      g * algebraMap F[X] W.FunctionField p =
        algebraMap W.CoordinateRing W.FunctionField (a₂ • 1 + b₂ • CoordinateRing.mk W Y) := by
  obtain ⟨u₁, u₂, ⟨-, p, hp, rfl⟩, h₁, h₂⟩ := IsLocalization.surj₂
    (Algebra.algebraMapSubmonoid W.CoordinateRing (nonZeroDivisors F[X])) W.FunctionField f g
  obtain ⟨a₁, b₁, rfl⟩ := CoordinateRing.exists_smul_basis_eq u₁
  obtain ⟨a₂, b₂, rfl⟩ := CoordinateRing.exists_smul_basis_eq u₂
  rw [← IsScalarTower.algebraMap_apply F[X] W.CoordinateRing W.FunctionField] at h₁ h₂
  exact ⟨a₁, b₁, a₂, b₂, p, nonZeroDivisors.ne_zero hp, h₁, h₂⟩

/-- **The ultrametric inequality on the function field.** -/
private theorem intDegree_norm_add_le {f g : W.FunctionField} (hf : f ≠ 0) (hg : g ≠ 0)
    (hfg : f + g ≠ 0) : (Algebra.norm (RatFunc F) (f + g)).intDegree
      ≤ max (Algebra.norm (RatFunc F) f).intDegree (Algebra.norm (RatFunc F) g).intDegree := by
  obtain ⟨a₁, b₁, a₂, b₂, p, hp, h₁, h₂⟩ := exists_common_smul_basis_div W f g
  have h₃ : (f + g) * algebraMap F[X] W.FunctionField p =
      algebraMap W.CoordinateRing W.FunctionField
        ((a₁ + a₂) • 1 + (b₁ + b₂) • CoordinateRing.mk W Y) := by grind [add_smul]
  rw [intDegree_norm_of_mul_eq W hf hp h₁, intDegree_norm_of_mul_eq W hg hp h₂,
    intDegree_norm_of_mul_eq W hfg hp h₃]
  grind [natDegree_norm_add_le]

open scoped Classical in
/-- The ultrametric inequality for the composite `RatFunc.inftyValuation ∘ Algebra.norm`, which is
`infinityPlace`'s `map_add_le_max'`. Split out to keep the definition short. -/
private theorem infinityPlace_add_le_max (x y : W.FunctionField) :
    RatFunc.inftyValuation F (Algebra.norm (RatFunc F) (x + y))
      ≤ max (RatFunc.inftyValuation F (Algebra.norm (RatFunc F) x))
            (RatFunc.inftyValuation F (Algebra.norm (RatFunc F) y)) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  rcases eq_or_ne (x + y) 0 with hxy | hxy
  · simp [hxy]
  have hN {f : W.FunctionField} (hf : f ≠ 0) : Algebra.norm (RatFunc F) f ≠ 0 :=
    (Algebra.norm_ne_zero_iff (R := RatFunc F)).mpr hf
  simp only [RatFunc.inftyValuation_apply, RatFunc.inftyValuation_of_nonzero F (hN hx),
    RatFunc.inftyValuation_of_nonzero F (hN hy), RatFunc.inftyValuation_of_nonzero F (hN hxy)]
  exact le_max_iff.2 <| (le_max_iff.1 <| intDegree_norm_add_le W hx hy hxy).imp
    WithZero.exp_le_exp.2 WithZero.exp_le_exp.2

open scoped Classical in
/-- **The valuation at infinity on the function field of a Weierstrass curve**: Mathlib's place at
infinity of `F(x)`, composed with the algebra norm. -/
noncomputable def infinityPlace : Valuation W.FunctionField (WithZero (Multiplicative ℤ)) where
  toFun f := RatFunc.inftyValuation F (Algebra.norm (RatFunc F) f)
  map_zero' := by rw [Algebra.norm_zero, map_zero]
  map_one' := by rw [map_one, map_one]
  map_mul' x y := by rw [map_mul, map_mul]
  map_add_le_max' := infinityPlace_add_le_max W


open scoped Classical in
/-- The evaluation rule for `infinityPlace`: it is `RatFunc.inftyValuation` applied to the algebra
norm of the function. The definition's body is not exposed across the module boundary, so this is
how downstream modules compute with it. Deliberately not `@[simp]`: unfolding the valuation would
defeat the special-value lemmas below, which are the normal forms automation should reach. -/
theorem infinityPlace_apply (f : W.FunctionField) :
    infinityPlace W f = RatFunc.inftyValuation F (Algebra.norm (RatFunc F) f) := (rfl)

open scoped Classical in
/-- The value of `infinityPlace` on a coordinate-ring element whose polynomial norm has positive
degree `n` is `exp n`: the norm commutes with the localization, and Mathlib values a nonzero
polynomial at its degree. The two pole orders below are its instances. -/
private theorem infinityPlace_algebraMap_of_natDegree_norm {u : W.CoordinateRing} {n : ℕ}
    (hn : n ≠ 0) (h : (Algebra.norm F[X] u).natDegree = n) :
    infinityPlace W (algebraMap W.CoordinateRing W.FunctionField u) = WithZero.exp (n : ℤ) := by
  rw [infinityPlace_apply, RatFunc.inftyValuation_apply,
    Algebra.norm_localization (M := nonZeroDivisors F[X]),
    RatFunc.inftyValuation.polynomial F (ne_zero_of_natDegree_gt (Nat.pos_of_ne_zero (h ▸ hn))),
    h]

-- NB `infinityPlace.X` and `infinityPlace.mk_Y` (and this file's two `natDegree_norm_*`
-- helpers) are deliberately NOT `@[simp]`: their left-hand sides are not in
-- simp-normal form — simp rewrites `algebraMap F[X] W.CoordinateRing X` to `AdjoinRoot.of` and
-- `CoordinateRing.mk W Y` to `AdjoinRoot.root` — so tagging them fails the repository's simpNF
-- lint gate. Stating them in that normal form instead would remove every mention of the curve's
-- coordinate functions, which is the whole content of the lemmas.
/-- **`x` has a double pole at infinity**: `v_∞ x = exp 2`, which is `ord_∞ x = -2`. -/
theorem infinityPlace.X :
    infinityPlace W (algebraMap W.CoordinateRing W.FunctionField
      (algebraMap F[X] W.CoordinateRing Polynomial.X)) = WithZero.exp 2 := by
  simpa using infinityPlace_algebraMap_of_natDegree_norm W two_ne_zero (natDegree_norm_X W)

/-- **`y` has a triple pole at infinity**: `v_∞ y = exp 3`, which is `ord_∞ y = -3`. -/
theorem infinityPlace.mk_Y :
    infinityPlace W (algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W Y))
      = WithZero.exp 3 := by
  simpa using infinityPlace_algebraMap_of_natDegree_norm W three_ne_zero (natDegree_norm_mk_Y W)


open scoped Classical in
/-- **The place at infinity lies over the infinite place of `F(x)`, with ramification index two.**
On a rational function of `x` the value is the square of Mathlib's infinite valuation, the extension
`F(W) / F(x)` being quadratic. -/
@[simp]
theorem infinityPlace.algebraMap_eq_sq (r : RatFunc F) :
    infinityPlace W (algebraMap (RatFunc F) W.FunctionField r)
      = RatFunc.inftyValuation F r ^ 2 := by
  rw [infinityPlace_apply, Algebra.norm_algebraMap, finrank_functionField, map_pow]

open scoped Classical in
/-- **The valuation is trivial on the base field**: a nonzero constant has value `1`, so `v_∞`
restricted to `F` is trivial. The analogue of `RatFunc.inftyValuation.C`. -/
theorem infinityPlace.C {c : F} (hc : c ≠ 0) :
    infinityPlace W (algebraMap (RatFunc F) W.FunctionField (RatFunc.C c)) = 1 := by
  rw [infinityPlace.algebraMap_eq_sq, RatFunc.inftyValuation.C F hc, one_pow]


/-- **The valuation at infinity is trivial on the base field.** -/
instance : (infinityPlace W).IsTrivialOn F where
  eq_one c hc :=
    IsScalarTower.algebraMap_apply F (RatFunc F) W.FunctionField c ▸ infinityPlace.C W hc

/-- **The valuation at infinity is nontrivial**: `x` has value `exp 2`. -/
instance : (infinityPlace W).IsNontrivial :=
  ⟨algebraMap W.CoordinateRing W.FunctionField (algebraMap F[X] W.CoordinateRing Polynomial.X),
    infinityPlace.X W ▸ ⟨WithZero.exp_ne_zero, by simp⟩⟩


/-- The simp-normal form of `infinityPlace.X`, stated for `AdjoinRoot.of`, which is what simp
rewrites the coordinate function to. -/
@[simp]
theorem infinityPlace.adjoinRoot_of_X :
    infinityPlace W (algebraMap W.CoordinateRing W.FunctionField
      (AdjoinRoot.of W.polynomial Polynomial.X)) = WithZero.exp 2 :=
  infinityPlace.X W

/-- The simp-normal form of `infinityPlace.mk_Y`, stated for `AdjoinRoot.root`. -/
@[simp]
theorem infinityPlace.adjoinRoot_root :
    infinityPlace W (algebraMap W.CoordinateRing W.FunctionField
      (AdjoinRoot.root W.polynomial)) = WithZero.exp 3 :=
  infinityPlace.mk_Y W


/-- **`x / y` is a uniformiser at infinity**: `v_∞ (x / y) = exp (-1)`, that is
`ord_∞ (x / y) = 1`, a simple zero at the point at infinity. The double pole of `x` and the triple
pole of `y` differ by one, which is what makes the quotient a uniformiser. -/
theorem infinityPlace.X_div_mk_Y :
    infinityPlace W (algebraMap W.CoordinateRing W.FunctionField
        (algebraMap F[X] W.CoordinateRing Polynomial.X) /
      algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W Y)) = WithZero.exp (-1) := by
  rw [map_div₀, infinityPlace.X, infinityPlace.mk_Y, ← WithZero.exp_sub]
  norm_num

-- The place is discrete of rank one for free — its value group is a subgroup of the cyclic group
-- `ℤᵐ⁰ˣ`, nontrivial by the instance above — but discreteness alone leaves the generator as
-- `exp (-n)` for an unspecified `n ≥ 1`, and the proper subgroup genuinely occurs: the restriction
-- of `v_∞` to `F(x)` has value group `2ℤ` by `infinityPlace.algebraMap_eq_sq`. What pins the
-- generator to `exp (-1)` is a single element of that value, so `X_div_mk_Y` is exactly the witness
-- Mathlib's `generator_eq_exp_neg_one_of_mem_range` asks for.
/-- **`x / y` is a uniformiser at the place at infinity**, in Mathlib's sense: its value generates
the value group and is `< 1`. -/
theorem infinityPlace.isUniformizer_X_div_mk_Y :
    (infinityPlace W).IsUniformizer (algebraMap W.CoordinateRing W.FunctionField
        (algebraMap F[X] W.CoordinateRing Polynomial.X) /
      algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W Y)) := by
  rw [Valuation.IsUniformizer.iff,
    Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_mem_range
      ⟨_, infinityPlace.X_div_mk_Y W⟩]
  exact infinityPlace.X_div_mk_Y W


/-- **The place at infinity is distinct from every affine place.** Together with
`CoordinateRing.pointPlace_eq_iff` this gives the injectivity of the whole point-to-place
assignment, the point at infinity included. -/
@[simp]
theorem infinityPlace_ne_heightOneSpectrum_valuation [IsDedekindDomain W.CoordinateRing]
    (P : IsDedekindDomain.HeightOneSpectrum W.CoordinateRing) :
    infinityPlace W ≠ P.valuation W.FunctionField := by
  intro heq
  -- `x` lies in the coordinate ring, so an affine place values it at most `1`, while it has a
  -- double pole at infinity
  have hx := P.valuation_le_one (K := W.FunctionField)
    (algebraMap F[X] W.CoordinateRing Polynomial.X)
  rw [← heq, infinityPlace.X, ← WithZero.exp_zero, WithZero.exp_le_exp] at hx
  lia

end WeierstrassCurve.Affine

end
