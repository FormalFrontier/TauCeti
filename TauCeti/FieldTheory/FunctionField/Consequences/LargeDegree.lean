/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.RiemannRoch.Uniqueness

/-!
# The large-degree regime of Riemann–Roch

Riemann's theorem bounds `ℓ(D)` from below by `deg D + 1 - g`, and Riemann–Roch corrects the
bound by `ℓ(W - D)` for a Riemann–Roch divisor `W`.  Once `deg D ≥ 2g - 1` the correction term
vanishes, because `deg (W - D) = (2g - 2) - deg D` is then negative, and Riemann's inequality
becomes the **identity**

`ℓ(D) = deg D + 1 - g` for `deg D ≥ 2g - 1`.

This is the workhorse computation of the theory: it evaluates `ℓ` outright, with no residual
term, on every divisor of large enough degree.  The bound `2g - 1` cannot be lowered, since `W`
itself has degree `2g - 2` and `ℓ(W) = g`, not `g - 1`.

Everything here is stated for a divisor `W` satisfying the Riemann–Roch identity
`ℓ(D) = deg D + 1 - g₀ + ℓ(W - D)`, in the form `TauCeti.Divisor.IsRiemannRochDivisor` that
`TauCeti/FieldTheory/FunctionField/RiemannRoch/Uniqueness.lean` introduces; by
`TauCeti.Divisor.IsRiemannRochDivisor.genus_eq` the value `g₀` is the genus of `F / k`, so these
really are statements about `g`.

## Main results

* `TauCeti.Divisor.IsRiemannRochDivisor.dim_eq_degree_add_one_sub`: **Stichtenoth,
  Theorem 1.5.17** — `ℓ(D) = deg D + 1 - g` as soon as `deg D ≥ 2g - 1`.
* `TauCeti.Divisor.IsRiemannRochDivisor.indexOfSpecialty_eq_zero`: equivalently, the index of
  specialty vanishes in that range, so such divisors are non-special.
* `TauCeti.Divisor.IsRiemannRochDivisor.dim_ne_degree_add_one_sub`: the bound is sharp — the
  identity fails at `W`, whose degree is `2g - 2`.
* `TauCeti.Divisor.IsRiemannRochDivisor.dim_zsmul_ofPoint`: the genus-one ladder
  `ℓ(n · P) = n` for `n ≥ 1` at a rational place `P`, the section-dimension count every
  Weierstrass-model argument runs on.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Theorem 1.5.17.
-/

public section

namespace TauCeti

open AlgebraicGeometry

variable {k F : Type*} [Field k] [Field F] [Algebra k F] {W : Divisor k F} {g₀ : ℕ}

/-- **Stichtenoth, Theorem 1.5.17**: Riemann's inequality is an equality
`ℓ(D) = deg D + 1 - g` on every divisor of degree at least `2g - 1`.

The correction term `ℓ(W - D)` of the Riemann–Roch identity vanishes there, because
`deg (W - D) = (2g - 2) - deg D` is negative. -/
theorem Divisor.IsRiemannRochDivisor.dim_eq_degree_add_one_sub (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (hW : W.IsRiemannRochDivisor g₀) {D : Divisor k F}
    (hD : 2 * (g₀ : ℤ) - 1 ≤ Divisor.degree D) :
    (Divisor.dim D : ℤ) = Divisor.degree D + 1 - g₀ := by
  have h := Divisor.isRiemannRochDivisor_iff.mp hW D
  have hdeg : Divisor.degree (W - D) < 0 := by
    rw [Divisor.degree_sub, hW.degree_eq hF hex]
    omega
  rw [Divisor.dim_eq_zero_of_degree_neg hF hdeg] at h
  simpa using h

/-- **Non-speciality in large degree**: the index of specialty `i(D)` vanishes as soon as
`deg D ≥ 2g - 1`.  This is `TauCeti.Divisor.IsRiemannRochDivisor.dim_eq_degree_add_one_sub`
read through the definition of `i(D)`. -/
theorem Divisor.IsRiemannRochDivisor.indexOfSpecialty_eq_zero (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (hW : W.IsRiemannRochDivisor g₀) {D : Divisor k F}
    (hD : 2 * (g₀ : ℤ) - 1 ≤ Divisor.degree D) :
    Divisor.indexOfSpecialty D = 0 := by
  have h := hW.dim_eq_degree_add_one_sub hF hex hD
  rw [Divisor.indexOfSpecialty_def, ← hW.genus_eq hF hex]
  omega

/-- **The bound `2g - 1` is sharp**: the identity `ℓ(D) = deg D + 1 - g` fails at `D = W`, a
divisor of degree `2g - 2`, where `ℓ(W) = g` rather than `g - 1`. -/
theorem Divisor.IsRiemannRochDivisor.dim_ne_degree_add_one_sub (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (hW : W.IsRiemannRochDivisor g₀) :
    (Divisor.dim W : ℤ) ≠ Divisor.degree W + 1 - g₀ := by
  rw [hW.dim_eq hF hex, hW.degree_eq hF hex]
  omega

/-- **The section-dimension ladder of a genus-one function field**: at a rational place `P` of a
function field of genus one, `ℓ(n · P) = n` for every `n ≥ 1`.

Every multiple `n · P` with `n ≥ 1` has degree `n ≥ 2g - 1 = 1`, so
`TauCeti.Divisor.IsRiemannRochDivisor.dim_eq_degree_add_one_sub` applies and evaluates
`ℓ(n · P) = n + 1 - 1`. -/
theorem Divisor.IsRiemannRochDivisor.dim_zsmul_ofPoint (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (hW : W.IsRiemannRochDivisor 1) {P : Place k F}
    (hP : P.degree = 1) {n : ℕ} (hn : 1 ≤ n) :
    Divisor.dim ((n : ℤ) • WeilDivisor.ofPoint P) = n := by
  have hdeg : Divisor.degree ((n : ℤ) • WeilDivisor.ofPoint P : Divisor k F) = n := by
    rw [Divisor.degree_zsmul, Divisor.degree_ofPoint, hP, Nat.cast_one, mul_one]
  have h := hW.dim_eq_degree_add_one_sub hF hex
    (D := ((n : ℤ) • WeilDivisor.ofPoint P : Divisor k F)) (by rw [hdeg]; push_cast; omega)
  rw [hdeg] at h
  omega

end TauCeti
