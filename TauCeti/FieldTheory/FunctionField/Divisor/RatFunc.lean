/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.RatFunc.IntermediateField
public import TauCeti.FieldTheory.FunctionField.Divisor.ProductFormula
public import TauCeti.FieldTheory.FunctionField.Place.RatFunc.Order

/-!
# Divisors of the rational function field

The rational function field `k(x)` is the base case of the theory of algebraic function fields,
and this file computes its principal divisors: the divisor of an irreducible polynomial, its
special case the divisor of `x`, and the degree of the pole divisor of an arbitrary rational
function.  It continues the rational-function-field thread begun in
`TauCeti.FieldTheory.FunctionField.Place.RatFunc.Basic`, where the places of `k(x)` are
classified, and its Riemann–Roch consequences are
`TauCeti.FieldTheory.FunctionField.RiemannRoch.RatFunc`.

Both calculations run on the classification of the places of `k(x)` together with the order
computations of `TauCeti.FieldTheory.FunctionField.Place.RatFunc.Order`: an irreducible `p` has a
simple zero at the place it defines, a pole of order `deg p` at infinity, and no other zeros or
poles.

## Main results

* `TauCeti.Divisor.principal_irreducible`: `div p = P_(p) - (deg p) · P_∞` for `p` irreducible,
  and its special case `TauCeti.Divisor.principal_X`: `div x = P_(X) - P_∞`.
* `TauCeti.Divisor.degree_poles_eq_max_natDegree`: the pole divisor of `z ∈ k(x)` has degree
  `max (deg z.num) (deg z.denom)`, which for nonconstant `z` is the degree of `k(x) / k(z)`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Sections I.2 and I.4.
-/

public section

noncomputable section

open IsDedekindDomain Polynomial

namespace TauCeti

open AlgebraicGeometry

variable {k : Type*} [Field k]

/-! ### The divisor of an irreducible polynomial -/

/-- **The divisor of an irreducible polynomial**: `div p = P_(p) - (deg p) · P_∞`.  An irreducible
`p` has a simple zero at the finite place it defines, a pole of order `deg p` at infinity, and no
other zeros or poles. -/
theorem Divisor.principal_irreducible {p : k[X]} (hp : Irreducible p) :
    Divisor.principal (IsFunctionField.ratFunc k)
        (Units.mk0 (algebraMap k[X] (RatFunc k) p)
          (RatFunc.algebraMap_ne_zero hp.ne_zero)) =
      WeilDivisor.ofPoint (Place.adicOfIrreducible hp) -
        p.natDegree • WeilDivisor.ofPoint (Place.infty k) := by
  refine WeilDivisor.ext fun P ↦ ?_
  rw [Divisor.coeff_principal, WeilDivisor.coeff_sub, Units.val_mk0]
  rcases Place.eq_infty_or_exists_eq_adicOfIrreducible P with rfl | ⟨q, hq, rfl⟩
  · simp [WeilDivisor.coeff_ofPoint_of_ne (Place.adicOfIrreducible_ne_infty hp).symm]
  · rw [Place.ord_adicOfIrreducible_algebraMap_irreducible hq hp]
    by_cases hqp : Associated q p
    · rw [(Place.adicOfIrreducible_eq_adicOfIrreducible_iff hq hp).mpr hqp]
      simp [WeilDivisor.coeff_ofPoint_of_ne (Place.adicOfIrreducible_ne_infty hp), hqp]
    · simp [WeilDivisor.coeff_ofPoint_of_ne (Place.adicOfIrreducible_ne_infty hq),
        WeilDivisor.coeff_ofPoint_of_ne fun h ↦
          hqp ((Place.adicOfIrreducible_eq_adicOfIrreducible_iff hq hp).mp h), hqp]

/-- **The divisor of `x`**: `div x = P_(X) - P_∞`.  The function `x` has a simple zero at the
place of the polynomial `X`, a simple pole at infinity, and no other zeros or poles. -/
theorem Divisor.principal_X :
    Divisor.principal (IsFunctionField.ratFunc k)
        (Units.mk0 (RatFunc.X : RatFunc k) RatFunc.X_ne_zero) =
      WeilDivisor.ofPoint (Place.adicOfIrreducible (irreducible_X (R := k))) -
        WeilDivisor.ofPoint (Place.infty k) := by
  have hX : Units.mk0 (RatFunc.X : RatFunc k) RatFunc.X_ne_zero =
      Units.mk0 (algebraMap k[X] (RatFunc k) X)
        (RatFunc.algebraMap_ne_zero (irreducible_X (R := k)).ne_zero) :=
    Units.ext RatFunc.algebraMap_X.symm
  rw [hX, Divisor.principal_irreducible, natDegree_X, one_nsmul]

/-! ### The degree of a rational map -/

/-- **Stichtenoth, Theorem 1.4.11 on `ℙ¹`**: the pole divisor of a rational function `z` has
degree `max (deg z.num) (deg z.denom)`.  For nonconstant `z` this is `[k(x) : k(z)]`, the degree
of the covering `ℙ¹ → ℙ¹` that `z` defines; a constant `z = c` is a unit at every place, and both
sides are `0`.  A rational function is transcendental over `k` exactly when it is not a constant,
by `RatFunc.transcendental_of_ne_C`. -/
theorem Divisor.degree_poles_eq_max_natDegree (z : (RatFunc k)ˣ) :
    Divisor.degree (Divisor.poles (IsFunctionField.ratFunc k) z) =
      max (z : RatFunc k).num.natDegree (z : RatFunc k).denom.natDegree := by
  by_cases hz : IsAlgebraic k (z : RatFunc k)
  · obtain ⟨c, hc⟩ := not_not.mp fun h ↦ RatFunc.transcendental_of_ne_C (z : RatFunc k) h hz
    have hpoles : Divisor.poles (IsFunctionField.ratFunc k) z = 0 :=
      WeilDivisor.ext fun P ↦ by simp [P.ord_eq_zero_of_isAlgebraic hz]
    rw [hpoles, hc]
    simp
  · rw [Divisor.degree_poles _ _ hz, RatFunc.finrank_eq_max_natDegree]

end TauCeti
