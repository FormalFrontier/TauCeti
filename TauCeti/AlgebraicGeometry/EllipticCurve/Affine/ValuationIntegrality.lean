/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
public import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.Valuation.Integral
import TauCeti.AlgebraicGeometry.EllipticCurve.Integrality
import TauCeti.RingTheory.Valuation.RootMonic

/-!
# Integral points of a Weierstrass curve over a valued field

Let `F` be a field, let `v` be a valuation on `F`, let `O` be the valuation subring of `v`, and
let `W` be a Weierstrass curve over `F` admitting a model over `O`. This file records the
valuation estimates that such a model forces, and the dichotomy they produce for the coordinates
of an affine point.

The dichotomy is the sharp one: `v(x)` is never `exp 1`. Either the point is integral,
`v(x) ≤ 1` and `v(y) ≤ 1`, or it is a pole of order at least two in `x`, `exp 2 ≤ v(x)`. There is
nothing in between: at a pole `v(y)² = v(x)³`, and `exp 3` is not a square, which rules out the
one intermediate value. Only pole order one is excluded here — the general statement that every
pole order is even is not proved.

The two halves need different hypotheses, and are stated that way. The coefficient bounds — and
the estimates on the two sides of the Weierstrass equation — never look at the value group, so
they are stated for an arbitrary `Γ₀`. Only the dichotomy needs `Γ₀ = ℤᵐ⁰`, because the parity
argument that rules out `v(x) = exp 1` is about the exponent being an integer.

The valuation is taken as an explicit argument rather than through `Valued F Γ₀`. Nothing here
uses a topology, and a fixed field carries many valuations at once — the intended consumers are
the `IsDedekindDomain.HeightOneSpectrum.valuation` of a varying prime, which cannot all be
`Valued` instances on `F` simultaneously.

## Main results

* `WeierstrassCurve.Affine.valuation_a₁_le_one` and its `a₂`, `a₃`, `a₄`, `a₆` companions: the
  coefficients of a curve with an integral model are integral, over any value group.
* `WeierstrassCurve.Affine.valuation_x_le_one_and_valuation_y_le_one_of_valuation_x_lt_exp_two`:
  an affine point whose `x`-coordinate has a pole of order less than two has both coordinates
  integral.

## Implementation notes

The hypothesis "`W` has a model over `O`" is Mathlib's `WeierstrassCurve.IsIntegral O W`, and the
model itself is `WeierstrassCurve.integralModel O W`; the coefficient bounds are then Mathlib's
`WeierstrassCurve.integralModel_aᵢ_eq` composed with membership in `O`.

The `y`-half of the dichotomy is not reproved by a valuation computation. Once `x` is known to be
integral, `TauCeti.WeierstrassCurve.isIntegral_y_of_equation_of_isIntegral_x` gives that `y` is
integral over `O` from the curve equation alone, over any algebra and with no valuation in sight;
`O` is a valuation subring, hence integrally closed in `F`, so integrality over it is membership.
That is how the main theorem discharges its `y`-half. Only the `x`-half — the parity argument that
rules out `v(x) = exp 1` — is genuinely about the valuation, and it is the only half that needs
the estimates below.

## Placement

Every declaration here lives in `WeierstrassCurve.Affine`, and the file's content is the
integrality of an affine point; `exp_one_pow` is a local `WithZero.exp` helper with no curve
content. The file sits in `EllipticCurve/Affine/` with the rest of the affine-point API.

It is not under `FormalGroup/`, although the formal group is what makes these estimates wanted:
they are what identifies the kernel of reduction, on which the formal group converges, as the
locus `exp 2 ≤ v(x)`. But nothing here mentions a power series. No `FormalGroup/` file imports
this module today — the milestones below are the future consumers.

This supplies the valuation substrate for the formal-group milestones of
`TauCetiRoadmap/EllipticCurves/README.md`, Layer 1, item "The formal group — four milestones
with four different hypothesis sets, not one" (README:572): milestone (iii), convergence over a
complete valued field, and milestone (iv), the identification with the kernel of reduction for an
integral model.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VII.2 — the characterisation
  of `E₁(K)` that this dichotomy underlies.

## Provenance

Adapted from the Stoll `EllipticCurves` development
(`github.com/MichaelStollBayreuth/EllipticCurves`, Apache-2.0, pinned by
`TauCetiRoadmap/EllipticCurves/README.md` at `66889eada51a`),
`EllipticCurves/WeierstrassFormalGroup/Foundations.lean`: `valued_a₁`–`valued_a₄` (:125–:128),
`valued_a₆` (:129), `valued_lhs_eq_rhs` (:72), `valued_rhs_eq` (:132), `valued_lhs_eq` (:164),
`valued_lhs_le` (:185), `valued_ne_exp_one` (:202) and `integral_of_not_mem` (:264), which is
`valuation_x_le_one_and_valuation_y_le_one_of_valuation_x_lt_exp_two` here.

Five departures. The source's private `coe_a₁`–`coe_a₆` (:110–:122) are not ported: they restate
the structure map for a model carried in the signature, whereas the model here is Mathlib's
`integralModel`, so the five coefficient bounds are `integralModel_aᵢ_eq` plus membership in `O`.
The setting is more general: the source works over `v.adicCompletion K` and
`v.adicCompletionIntegers K`, whereas no step uses completeness, the Dedekind hypothesis, or a
topology, so the results are stated for a bare `(v : Valuation F Γ₀)` and its valuation subring —
a weaker hypothesis set that still covers the source's case, `adicCompletionIntegers` being by
definition the valuation subring of `Valued.v`. `valuation_a₆_le_one` is public here although the
source's `valued_a₆` (:129) is private: the five coefficient bounds are one API, and a consumer
holding an integral model needs all five. The hypothesis is stated positively as `v x < exp 2`
rather than the source's `¬ exp 2 ≤ v x`. And the `y`-half is proved by reuse rather than by the
source's valuation computation: the source derives it from a `valued_rhs_le` bound (:151), whereas
here `isIntegral_y_of_equation_of_isIntegral_x` plus integral closedness of `O` gives it directly,
so that bound has no consumer and is not ported.
-/

public section

open WithZero

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F]

/-! ### The coefficient bounds, over an arbitrary value group

Nothing in this section looks at the value group: an integral model bounds the coefficients, and
the two sides of the Weierstrass equation are estimated, for any `Γ₀`. Only the dichotomy below
needs `Γ₀ = ℤᵐ⁰`.

`Field F` cannot be weakened here: `Valuation.valuationSubring` is defined only for a field
(`Mathlib/RingTheory/Valuation/ValuationSubring.lean:33`). -/

section Coefficients

variable {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation F Γ₀) {W : Affine F}

/-- The two sides of the Weierstrass equation have the same valuation, for any point on the
curve. -/
private lemma valuation_lhs_eq_rhs {x y : F} (hxy : W.Equation x y) :
    v (y ^ 2 + (W.a₁ * x * y + W.a₃ * y)) = v (x ^ 3 + (W.a₂ * x ^ 2 + (W.a₄ * x + W.a₆))) :=
  congrArg v (by linear_combination (W.equation_iff x y).mp hxy)

section Integral

variable [WeierstrassCurve.IsIntegral v.valuationSubring W]

/-- The `a₁`-coefficient of a curve with an integral model is integral. -/
theorem valuation_a₁_le_one : v W.a₁ ≤ 1 := by
  rw [← integralModel_a₁_eq v.valuationSubring W]; exact (integralModel v.valuationSubring W).a₁.2

/-- The `a₂`-coefficient of a curve with an integral model is integral. -/
theorem valuation_a₂_le_one : v W.a₂ ≤ 1 := by
  rw [← integralModel_a₂_eq v.valuationSubring W]; exact (integralModel v.valuationSubring W).a₂.2

/-- The `a₃`-coefficient of a curve with an integral model is integral. -/
theorem valuation_a₃_le_one : v W.a₃ ≤ 1 := by
  rw [← integralModel_a₃_eq v.valuationSubring W]; exact (integralModel v.valuationSubring W).a₃.2

/-- The `a₄`-coefficient of a curve with an integral model is integral. -/
theorem valuation_a₄_le_one : v W.a₄ ≤ 1 := by
  rw [← integralModel_a₄_eq v.valuationSubring W]; exact (integralModel v.valuationSubring W).a₄.2

/-- The `a₆`-coefficient of a curve with an integral model is integral. -/
theorem valuation_a₆_le_one : v W.a₆ ≤ 1 := by
  rw [← integralModel_a₆_eq v.valuationSubring W]; exact (integralModel v.valuationSubring W).a₆.2

/-- For `v(x) > 1`, the right-hand side of the Weierstrass equation has valuation `v(x)³`: the
`x³` term strictly dominates the rest. This is `Valuation.map_cubic_eq_of_one_lt` at the
coefficients `a₂`, `a₄`, `a₆`, whose integrality the model supplies. -/
private lemma valuation_rhs_eq {x : F} (hA1 : 1 < v x) :
    v (x ^ 3 + (W.a₂ * x ^ 2 + (W.a₄ * x + W.a₆))) = v x ^ 3 := by
  convert v.map_cubic_eq_of_one_lt (valuation_a₂_le_one (W := W) v)
    (valuation_a₄_le_one (W := W) v) (valuation_a₆_le_one (W := W) v) hA1 using 2
  ring

/-- When `v(y)` dominates `v(x)` and exceeds `1`, the left-hand side of the Weierstrass equation
has valuation `v(y)²`: the `y²` term strictly dominates the rest. -/
private lemma valuation_lhs_eq {x y : F} (hAB : v x < v y) (hB1 : 1 < v y) :
    v (y ^ 2 + (W.a₁ * x * y + W.a₃ * y)) = v y ^ 2 := by
  set B := v y
  have h2 : v (W.a₁ * x * y) < B ^ 2 := by
    rw [map_mul, map_mul]
    calc v W.a₁ * v x * B ≤ 1 * v x * B :=
        mul_le_mul' (mul_le_mul' (valuation_a₁_le_one v) le_rfl) le_rfl
      _ = v x * B := by rw [one_mul]
      _ < B * B := mul_lt_mul_of_pos_right hAB (zero_lt_one.trans hB1)
      _ = B ^ 2 := (sq B).symm
  have h3 : v (W.a₃ * y) < B ^ 2 := by
    rw [map_mul]
    calc v W.a₃ * B ≤ 1 * B := mul_le_mul' (valuation_a₃_le_one v) le_rfl
      _ = B ^ 1 := by rw [one_mul, pow_one]
      _ < B ^ 2 := pow_lt_pow_right₀ hB1 (by lia)
  rw [Valuation.map_add_eq_of_lt_left _ (by rw [map_pow]; exact v.map_add_lt h2 h3), map_pow]

/-- A common bound `C ≥ 1` on `v(x)` and `v(y)` bounds the left-hand side of the Weierstrass
equation by `C²`. -/
private lemma valuation_lhs_le {x y : F} {C : Γ₀} (hxC : v x ≤ C) (hyC : v y ≤ C) (h1C : 1 ≤ C) :
    v (y ^ 2 + (W.a₁ * x * y + W.a₃ * y)) ≤ C ^ 2 := by
  refine v.map_add_le ?_ (v.map_add_le ?_ ?_)
  · rw [map_pow]
    exact pow_le_pow_left' hyC 2
  · rw [map_mul, map_mul]
    calc v W.a₁ * v x * v y ≤ 1 * C * C :=
        mul_le_mul' (mul_le_mul' (valuation_a₁_le_one v) hxC) hyC
      _ = C ^ 2 := by rw [one_mul, sq]
  · rw [map_mul]
    calc v W.a₃ * v y ≤ 1 * C := mul_le_mul' (valuation_a₃_le_one v) hyC
      _ = C := one_mul C
      _ ≤ C ^ 2 := le_self_pow h1C (by lia)

end Integral

end Coefficients

/-! ### The dichotomy, over a discretely valued field

This is where `Γ₀ = ℤᵐ⁰` is used: the parity argument that rules out `v(x) = exp 1` needs the
value group to be `ℤ`. The bounds above are applied at `Γ₀ := ℤᵐ⁰`. -/

section Discrete

variable (v : Valuation F ℤᵐ⁰) {W : Affine F}

-- Named rather than inlined because `exp` is not a `simp`-normal form here: the bounds produced
-- by `valuation_lhs_le` and `valuation_rhs_eq` are powers of `exp 1`, while the right-hand sides
-- are compared as `exp _`, and no ordinary rewrite bridges the two.
/-- A power of `exp 1` is `exp` of the exponent. -/
private lemma exp_one_pow (n : ℕ) : (exp (1 : ℤ) : ℤᵐ⁰) ^ n = exp (n : ℤ) := by
  rw [← exp_nsmul, nsmul_eq_mul, mul_one]

section Integral

variable [WeierstrassCurve.IsIntegral v.valuationSubring W]

/-- **No affine point has `v(x) = exp 1`**: the `x`-coordinate has no pole of order one.

If `v(x) = exp 1` then the right-hand side of the Weierstrass equation has valuation `exp 3`. The
left-hand side cannot match it: for `v(y) ≤ exp 1` it is bounded by `exp 2`, and for `v(y) > exp 1`
it equals `v(y)²`, which is an even power of `exp` and so is never `exp 3`. -/
private lemma valuation_ne_exp_one {x y : F} (hxy : W.Equation x y) : v x ≠ exp (1 : ℤ) := by
  intro hA1
  have hval := valuation_lhs_eq_rhs v hxy
  have hRHS : v (x ^ 3 + (W.a₂ * x ^ 2 + (W.a₄ * x + W.a₆))) = exp (3 : ℤ) := by
    rw [valuation_rhs_eq v (by simp [hA1]), hA1, exp_one_pow]
    norm_num
  rcases le_or_gt (v y) (exp 1) with hB1 | hB1
  · -- `v(y) ≤ exp 1` bounds the left-hand side by `exp 2 < exp 3`
    have hle := valuation_lhs_le (W := W) v hA1.le hB1 (by simp)
    rw [hval, hRHS, exp_one_pow, exp_le_exp] at hle
    lia
  · -- `v(y) > exp 1` gives `v(y)² = exp 3`, impossible by parity
    have hB3 : v y ^ 2 = exp (3 : ℤ) := by
      rw [← valuation_lhs_eq (W := W) v (hA1 ▸ hB1) ((by simp : (1 : ℤᵐ⁰) < exp (1 : ℤ)).trans hB1),
        hval,
        hRHS]
    obtain ⟨b, hb⟩ : ∃ b : ℤ, v y = exp b := ⟨_, (exp_log (exp_pos.trans hB1).ne').symm⟩
    rw [hb, ← exp_nsmul, exp_inj, nsmul_eq_mul] at hB3
    push_cast at hB3
    lia

/-- The `x`-half of the dichotomy: an `x`-coordinate whose pole has order less than two is
integral. Its valuation is a power of `exp`, the exponent is at most `1` by hypothesis, and
`valuation_ne_exp_one` rules the exponent `1` out. -/
private lemma valuation_x_le_one_of_lt_exp_two {x y : F} (hxy : W.Equation x y)
    (hx : v x < exp (2 : ℤ)) : v x ≤ 1 := by
  rcases eq_or_ne (v x) 0 with h0 | h0
  · exact h0 ▸ zero_le
  · obtain ⟨a, ha⟩ : ∃ a : ℤ, v x = exp a := ⟨_, (exp_log h0).symm⟩
    have ha1 : a ≤ 1 := by
      by_contra hlt
      exact absurd (ha ▸ exp_le_exp.mpr (by lia : (2 : ℤ) ≤ a)) (not_le.mpr hx)
    rcases eq_or_lt_of_le ha1 with h1 | h1
    · exact absurd (by rw [ha, h1]) (valuation_ne_exp_one v hxy)
    · rw [ha]
      exact exp_le_one_iff.mpr (by lia)

/-- **An affine point whose `x`-coordinate has pole order less than two is integral.**

The `x`-coordinate of an affine point of `W` is either integral or has a pole of order at least
two, and in the former case the `y`-coordinate is integral too. -/
theorem valuation_x_le_one_and_valuation_y_le_one_of_valuation_x_lt_exp_two {x y : F}
    (hxy : W.Equation x y) (hx : v x < exp (2 : ℤ)) : v x ≤ 1 ∧ v y ≤ 1 := by
  have hA1 := valuation_x_le_one_of_lt_exp_two v hxy hx
  refine ⟨hA1, ?_⟩
  -- `x` is integral, so the curve equation makes `y` integral over `O`
  -- (`isIntegral_y_of_equation_of_isIntegral_x`), and `O` is integrally closed in `F`.
  have hxy' : ((integralModel v.valuationSubring W).baseChange F).toAffine.Equation x y := by
    rw [baseChange_integralModel_eq]; exact hxy
  have hy : _root_.IsIntegral v.valuationSubring y :=
    _root_.TauCeti.WeierstrassCurve.isIntegral_y_of_equation_of_isIntegral_x _ hxy'
      (isIntegral_algebraMap
        (x := (⟨x, (Valuation.mem_valuationSubring_iff v x).mpr hA1⟩ : v.valuationSubring)))
  exact (Valuation.valuationSubring.integers v).isIntegral_iff_v_le_one.mp hy

end Integral

end Discrete

end WeierstrassCurve.Affine
