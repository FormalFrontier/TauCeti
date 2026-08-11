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
  `WeierstrassCurve.Affine.infinityPlace.mk_Y`
* `WeierstrassCurve.Affine.infinityPlace.C`: the valuation is trivial on the base field — a
  nonzero constant has value `1`. The `Valuation.IsTrivialOn F` and `Valuation.IsNontrivial`
  instances follow, so the place is usable through Mathlib's standard valuation
  API: `v_∞ x = exp 2` and `v_∞ y = exp 3` —
  the double and triple poles at infinity, `ord_∞ x = -2` and `ord_∞ y = -3`, which is what Layer 0
  asks for by name. They read the norm degrees of `FunctionField/Norm.lean` through the valuation.

Each special value comes in two forms: one stated about the curve's coordinate functions, and a
`@[simp]` restatement in the shape simp actually normalises them to. The machinery that builds the
ultrametric inequality is `private`, and the norm-degree theory it rests on lives in
`FunctionField/Norm.lean`.

## Roadmap

`TauCetiRoadmap/EllipticCurves/README.md`, **Layer 0** (the function field, places, and divisors),
whose §Places asks for the one further place `W.infinityPlace` beyond the affine ones, sitting
"where `x` and `y` have their poles", with `ord_∞ x = -2`, `ord_∞ y = -3`. This file supplies the
valuation and those two degrees; `Suggested.lean` seeds no declaration it competes with, recording
that the function-field layer's "types are new API and are built there, not pinned here".

## Provenance

The route is that of the AINTLIB `HasseWeil` project (`github.com/CBirkbeck/AINTLIB`, Apache-2.0,
`dev/hasse-weil` at `a582951fe96b`), `HasseWeil/Curves/Infinity.lean`: `normAsRatFunc`,
`ordAtInfty`, `ordAtInfty_mul`, `ordAtInfty_add_ge_min` (tagged T-ORD-ARITH-12) and
`ordAtInfty_coordX`/`ordAtInfty_coordY`.

Changes from the source. There `ordAtInfty` is a definition of its own, valued in `WithTop ℤ`, built
over a `SmoothPlaneCurve` structure wrapping `WeierstrassCurve.Affine`, with multiplicativity,
vanishing and the ultrametric bound all proved by hand. Here the norm is Mathlib's `Algebra.norm`
and the target is Mathlib's `ℤᵐ⁰`, so the result is a genuine `Valuation` uniform with
`RatFunc.inftyValuation` and `IsDedekindDomain.HeightOneSpectrum.valuation`; multiplicativity and
vanishing are `map_mul` and `Algebra.norm_eq_zero_iff`, and only the ultrametric inequality is
reproved.
-/

public section

open Polynomial WeierstrassCurve

open scoped Polynomial.Bivariate RatFunc

namespace WeierstrassCurve.Affine


section Nontrivial

variable {R : Type*} [CommRing R] [Nontrivial R] (W : WeierstrassCurve.Affine R)

/-- The norm of the coordinate function `x` has degree `2`: it is `x ^ 2`. Private: it exists to
compute `infinityPlace.X`, and Mathlib's `CoordinateRing.norm_smul_basis` is the general fact. -/
private theorem natDegree_norm_X :
    (Algebra.norm R[X] (algebraMap R[X] W.CoordinateRing Polynomial.X)).natDegree = 2 := by
  have hX : algebraMap R[X] W.CoordinateRing Polynomial.X =
      (Polynomial.X : R[X]) • (1 : W.CoordinateRing) + (0 : R[X]) • CoordinateRing.mk W Y := by
    rw [zero_smul, add_zero, Algebra.smul_def, mul_one]
  rw [hX, CoordinateRing.norm_smul_basis]
  simp

/-- The norm of the coordinate function `y` has degree `3`. Private, as above. -/
private theorem natDegree_norm_mk_Y :
    (Algebra.norm R[X] (CoordinateRing.mk W Y)).natDegree = 3 := by
  have hY : CoordinateRing.mk W Y = (0 : R[X]) • 1 + (1 : R[X]) • CoordinateRing.mk W Y := by simp
  rw [hY, CoordinateRing.norm_smul_basis]
  compute_degree!

end Nontrivial


variable {F : Type*} [Field F] (W : WeierstrassCurve.Affine F)

/-- Every function is `(a + b y) / p` with `a b p` polynomials, `p ≠ 0` — the form the degree
formula consumes: numerator in the `1, Y` basis, denominator a polynomial. -/
private theorem exists_smul_basis_div (f : W.FunctionField) :
    ∃ a b p : F[X], p ≠ 0 ∧
      f * algebraMap F[X] W.FunctionField p =
        algebraMap W.CoordinateRing W.FunctionField (a • 1 + b • CoordinateRing.mk W Y) := by
  obtain ⟨⟨u, ⟨d, _hd⟩⟩, hf⟩ := IsLocalization.mk'_surjective
    (Algebra.algebraMapSubmonoid W.CoordinateRing (nonZeroDivisors F[X])) f
  obtain ⟨p, hp, rfl⟩ := _hd
  obtain ⟨a, b, rfl⟩ := CoordinateRing.exists_smul_basis_eq u
  refine ⟨a, b, p, nonZeroDivisors.ne_zero hp, ?_⟩
  rw [← hf, IsScalarTower.algebraMap_apply F[X] W.CoordinateRing W.FunctionField]
  exact IsLocalization.mk'_spec W.FunctionField _ _

/-- Scaling a decomposition by a polynomial: `(a + by)/p = (ac + bcy)/(pc)`. -/
private theorem smul_basis_div_mul {f : W.FunctionField} {a b p : F[X]}
    (h : f * algebraMap F[X] W.FunctionField p =
      algebraMap W.CoordinateRing W.FunctionField (a • 1 + b • CoordinateRing.mk W Y)) (c : F[X]) :
    f * algebraMap F[X] W.FunctionField (p * c) =
      algebraMap W.CoordinateRing W.FunctionField
        ((a * c) • 1 + (b * c) • CoordinateRing.mk W Y) := by
  have : (a * c) • (1 : W.CoordinateRing) + (b * c) • CoordinateRing.mk W Y
      = (a • 1 + b • CoordinateRing.mk W Y) * algebraMap F[X] W.CoordinateRing c := by
    simp only [Algebra.smul_def, map_mul]; ring
  rw [this, map_mul, map_mul,
    ← IsScalarTower.algebraMap_apply F[X] W.CoordinateRing W.FunctionField, ← h]
  ring

/-- **Two functions over a common denominator.** -/
private theorem exists_common_smul_basis_div (f g : W.FunctionField) :
    ∃ a₁ b₁ a₂ b₂ p : F[X], p ≠ 0 ∧
      f * algebraMap F[X] W.FunctionField p =
        algebraMap W.CoordinateRing W.FunctionField (a₁ • 1 + b₁ • CoordinateRing.mk W Y) ∧
      g * algebraMap F[X] W.FunctionField p =
        algebraMap W.CoordinateRing W.FunctionField (a₂ • 1 + b₂ • CoordinateRing.mk W Y) := by
  obtain ⟨a₁, b₁, p₁, hp₁, h₁⟩ := exists_smul_basis_div W f
  obtain ⟨a₂, b₂, p₂, hp₂, h₂⟩ := exists_smul_basis_div W g
  refine ⟨a₁ * p₂, b₁ * p₂, a₂ * p₁, b₂ * p₁, p₁ * p₂, mul_ne_zero hp₁ hp₂,
    smul_basis_div_mul W h₁ p₂, ?_⟩
  rw [mul_comm p₁ p₂]
  exact smul_basis_div_mul W h₂ p₁

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
    CoordinateRing.degree_norm_smul_basis]
  refine max_le ?_ ?_
  · calc (2 : ℕ) • (a₁ + a₂).degree ≤ 2 • max a₁.degree a₂.degree := by
          gcongr; exact degree_add_le a₁ a₂
    _ ≤ _ := by
          rcases max_cases a₁.degree a₂.degree with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> simp
  · calc (2 : ℕ) • (b₁ + b₂).degree + 3 ≤ 2 • max b₁.degree b₂.degree + 3 := by
          gcongr; exact degree_add_le b₁ b₂
    _ ≤ _ := by
          rcases max_cases b₁.degree b₂.degree with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> simp

/-- The `natDegree` form, and it needs no nonzero hypotheses at all: `natDegree_le_natDegree`
carries the `WithBot` bound across, and `natDegree 0 = 0` makes the zero cases hold anyway. -/
private theorem natDegree_norm_add_le (a₁ b₁ a₂ b₂ : R[X]) :
    (Algebra.norm R[X] ((a₁ + a₂) • (1 : W.CoordinateRing)
        + (b₁ + b₂) • CoordinateRing.mk W Y)).natDegree
      ≤ max (Algebra.norm R[X] (a₁ • 1 + b₁ • CoordinateRing.mk W Y)).natDegree
            (Algebra.norm R[X] (a₂ • 1 + b₂ • CoordinateRing.mk W Y)).natDegree := by
  have hd := degree_norm_add_le W a₁ b₁ a₂ b₂
  rcases max_cases
      (Algebra.norm R[X] (a₁ • (1 : W.CoordinateRing) + b₁ • CoordinateRing.mk W Y)).degree
      (Algebra.norm R[X] (a₂ • (1 : W.CoordinateRing) + b₂ • CoordinateRing.mk W Y)).degree with
    ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] at hd
  · exact le_max_of_le_left (natDegree_le_natDegree hd)
  · exact le_max_of_le_right (natDegree_le_natDegree hd)

end DomainCore

/-- **The ultrametric inequality on the function field.** -/
private theorem intDegree_norm_add_le {f g : W.FunctionField} (hf : f ≠ 0) (hg : g ≠ 0)
    (hfg : f + g ≠ 0) :
    (Algebra.norm (RatFunc F) (f + g)).intDegree
      ≤ max (Algebra.norm (RatFunc F) f).intDegree (Algebra.norm (RatFunc F) g).intDegree := by
  obtain ⟨a₁, b₁, a₂, b₂, p, hp, h₁, h₂⟩ := exists_common_smul_basis_div W f g
  have h₃ : (f + g) * algebraMap F[X] W.FunctionField p =
      algebraMap W.CoordinateRing W.FunctionField
        ((a₁ + a₂) • 1 + (b₁ + b₂) • CoordinateRing.mk W Y) := by
    rw [add_mul, h₁, h₂, ← map_add]
    congr 1
    simp only [add_smul]
    ring
  rw [intDegree_norm_of_mul_eq W hf hp h₁, intDegree_norm_of_mul_eq W hg hp h₂,
    intDegree_norm_of_mul_eq W hfg hp h₃]
  have := natDegree_norm_add_le W a₁ b₁ a₂ b₂
  omega

/-- The norm of `0` is `0`: the extension is nontrivial, so `Algebra.norm_eq_zero_iff` applies. -/
private theorem norm_zero_eq_zero :
    Algebra.norm (RatFunc F) (0 : W.FunctionField) = 0 :=
  (Algebra.norm_eq_zero_iff (R := RatFunc F)).mpr rfl

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
  · rw [hxy, norm_zero_eq_zero W, map_zero]
    exact zero_le
  have hNx : Algebra.norm (RatFunc F) x ≠ 0 :=
    fun h => hx ((Algebra.norm_eq_zero_iff (R := RatFunc F)).mp h)
  have hNy : Algebra.norm (RatFunc F) y ≠ 0 :=
    fun h => hy ((Algebra.norm_eq_zero_iff (R := RatFunc F)).mp h)
  have hNxy : Algebra.norm (RatFunc F) (x + y) ≠ 0 :=
    fun h => hxy ((Algebra.norm_eq_zero_iff (R := RatFunc F)).mp h)
  rw [RatFunc.inftyValuation_apply, RatFunc.inftyValuation_apply, RatFunc.inftyValuation_apply,
    RatFunc.inftyValuation_of_nonzero F hNx, RatFunc.inftyValuation_of_nonzero F hNy,
    RatFunc.inftyValuation_of_nonzero F hNxy]
  rcases max_cases (Algebra.norm (RatFunc F) x).intDegree
      (Algebra.norm (RatFunc F) y).intDegree with ⟨h, _⟩ | ⟨h, _⟩
  · refine le_trans ?_ (le_max_left _ _)
    rw [WithZero.exp_le_exp]
    exact le_trans (intDegree_norm_add_le W hx hy hxy) (le_of_eq h)
  · refine le_trans ?_ (le_max_right _ _)
    rw [WithZero.exp_le_exp]
    exact le_trans (intDegree_norm_add_le W hx hy hxy) (le_of_eq h)

open scoped Classical in
/-- **The valuation at infinity on the function field of a Weierstrass curve**: Mathlib's place at
infinity of `F(x)`, composed with the algebra norm. -/
noncomputable def infinityPlace : Valuation W.FunctionField (WithZero (Multiplicative ℤ)) where
  toFun f := RatFunc.inftyValuation F (Algebra.norm (RatFunc F) f)
  map_zero' := by
    rw [norm_zero_eq_zero W, map_zero]
  map_one' := by rw [map_one, map_one]
  map_mul' x y := by rw [map_mul, map_mul]
  map_add_le_max' := infinityPlace_add_le_max W


open scoped Classical in
/-- The evaluation rule for `infinityPlace`: it is `RatFunc.inftyValuation` applied to the algebra
norm of the function. Deliberately not `@[simp]`: unfolding the valuation would defeat the
special-value lemmas below, which are the normal forms automation should reach. -/
theorem infinityPlace_apply (f : W.FunctionField) :
    infinityPlace W f = RatFunc.inftyValuation F (Algebra.norm (RatFunc F) f) := by
  simp [infinityPlace]

/-- A coordinate-ring element whose polynomial norm has positive degree has nonzero norm over
`RatFunc F`: a zero polynomial would have degree zero. -/
private theorem norm_ne_zero_of_natDegree_ne_zero {u : W.CoordinateRing}
    (h : (Algebra.norm F[X] u).natDegree ≠ 0) :
    Algebra.norm (RatFunc F) (algebraMap W.CoordinateRing W.FunctionField u) ≠ 0 := by
  rw [Algebra.norm_localization (R := F[X]) (M := nonZeroDivisors F[X]) (S := W.CoordinateRing)]
  refine RatFunc.algebraMap_ne_zero fun hz => h ?_
  rw [hz, natDegree_zero]

open scoped Classical in
-- NB `inftyValuation_X` and `inftyValuation_mk_Y` (and the two `natDegree_norm_*` in
-- `FunctionField/Norm.lean`) are deliberately NOT `@[simp]`: their left-hand sides are not in
-- simp-normal form — simp rewrites `algebraMap F[X] W.CoordinateRing X` to `AdjoinRoot.of` and
-- `CoordinateRing.mk W Y` to `AdjoinRoot.root` — so tagging them fails the repository's simpNF
-- lint gate. Stating them in that normal form instead would remove every mention of the curve's
-- coordinate functions, which is the whole content of the lemmas.
/-- **`x` has a double pole at infinity**: `v_∞ x = exp 2`, which is `ord_∞ x = -2`. -/
theorem infinityPlace.X :
    infinityPlace W (algebraMap W.CoordinateRing W.FunctionField
      (algebraMap F[X] W.CoordinateRing Polynomial.X)) = WithZero.exp 2 := by
  rw [infinityPlace_apply, RatFunc.inftyValuation_apply,
    RatFunc.inftyValuation_of_nonzero F
      (norm_ne_zero_of_natDegree_ne_zero W
        (u := algebraMap F[X] W.CoordinateRing Polynomial.X)
        (by rw [natDegree_norm_X]; norm_num)),
    intDegree_norm_algebraMap_coordinateRing, natDegree_norm_X]
  norm_num

open scoped Classical in
/-- **`y` has a triple pole at infinity**: `v_∞ y = exp 3`, which is `ord_∞ y = -3`. -/
theorem infinityPlace.mk_Y :
    infinityPlace W (algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W Y))
      = WithZero.exp 3 := by
  rw [infinityPlace_apply, RatFunc.inftyValuation_apply,
    RatFunc.inftyValuation_of_nonzero F
      (norm_ne_zero_of_natDegree_ne_zero W (u := CoordinateRing.mk W Y)
        (by rw [natDegree_norm_mk_Y]; norm_num)),
    intDegree_norm_algebraMap_coordinateRing, natDegree_norm_mk_Y]
  norm_num


open scoped Classical in
/-- **The valuation is trivial on the base field**: a nonzero constant has value `1`, so `v_∞`
restricted to `F` is trivial. The analogue of `RatFunc.inftyValuation.C`. -/
theorem infinityPlace.C {c : F} (hc : c ≠ 0) :
    infinityPlace W (algebraMap (RatFunc F) W.FunctionField (RatFunc.C c)) = 1 := by
  rw [infinityPlace_apply, Algebra.norm_algebraMap, finrank_functionField W (RatFunc F), map_pow,
    RatFunc.inftyValuation.C (F := F) hc, one_pow]


open scoped Classical in
/-- **The valuation at infinity is trivial on the base field.** -/
instance instIsTrivialOn : (infinityPlace W).IsTrivialOn F where
  eq_one c hc := by
    rw [IsScalarTower.algebraMap_apply F (RatFunc F) W.FunctionField]
    exact infinityPlace.C W hc

/-- **The valuation at infinity is nontrivial**: `x` has value `exp 2`. -/
instance instIsNontrivial : (infinityPlace W).IsNontrivial where
  exists_val_nontrivial :=
    ⟨algebraMap W.CoordinateRing W.FunctionField (algebraMap F[X] W.CoordinateRing Polynomial.X),
      by rw [infinityPlace.X]; exact ⟨WithZero.exp_ne_zero, by simp⟩⟩


open scoped Classical in
/-- The simp-normal form of `infinityPlace.X`, stated for `AdjoinRoot.of`, which is what simp
rewrites the coordinate function to. -/
@[simp]
theorem infinityPlace.adjoinRoot_of_X :
    infinityPlace W (algebraMap W.CoordinateRing W.FunctionField
      (AdjoinRoot.of W.polynomial Polynomial.X)) = WithZero.exp 2 :=
  infinityPlace.X W

open scoped Classical in
/-- The simp-normal form of `infinityPlace.mk_Y`, stated for `AdjoinRoot.root`. -/
@[simp]
theorem infinityPlace.adjoinRoot_root :
    infinityPlace W (algebraMap W.CoordinateRing W.FunctionField
      (AdjoinRoot.root W.polynomial)) = WithZero.exp 3 :=
  infinityPlace.mk_Y W

end WeierstrassCurve.Affine

end
