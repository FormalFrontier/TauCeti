/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
public import Mathlib.RingTheory.Localization.NumDen
import Mathlib.RingTheory.Localization.Rat

/-!
# Denominators of points on a Weierstrass curve over a unique factorization domain

Let `R` be a unique factorization domain with fraction field `K` and let `W : WeierstrassCurve R`
have coefficients in `R`. Writing a `K`-point of `W` as a pair of reduced fractions
`x = num x / den x` and `y = num y / den y` (Mathlib's `IsFractionRing.num` and
`IsFractionRing.den`), the Weierstrass equation forces the denominator of the `x`-coordinate to
be **powerful**: a prime dividing it divides it at least twice. In particular `den x` is never a
prime element — the form in which the Nagell–Lutz integrality argument uses it, where the rational
root theorem has already bounded `den x` by a prime.

This is weaker than the classical statement for a short model `y² = x³ + Ax + B` over `ℤ`, that
`den x = d²` and `den y = d³` for some `d`: that needs each `q`-adic valuation of `den x` to be
*even*, not merely at least `2`. For a short model that parity follows from comparing valuations
across `y² = x³ + Ax + B`; no such argument is carried out here, and the statement below is the
weaker one the Nagell–Lutz route consumes.

The proof is a descent in three steps. Clearing denominators in the Weierstrass equation gives an
identity in `R`; if a prime `q` divides `den x` exactly once, then dividing that identity by
successive powers of `q` forces `q ^ 2 ∣ den y` and then `q ∣ num y` — contradicting the reducedness
of `y`.

## Main results

* `TauCeti.WeierstrassCurve.sq_dvd_den_of_prime_of_dvd`: a prime dividing the denominator of the
  `x`-coordinate of a point divides it at least twice.
* `TauCeti.WeierstrassCurve.not_prime_den`: the denominator of the `x`-coordinate of a point is
  not a prime element.
* `TauCeti.WeierstrassCurve.isUnit_den_of_dvd_squarefree`: a squarefree bound on that denominator
  forces it to be a unit.
* `TauCeti.WeierstrassCurve.den_eq_one_of_dvd_squarefree`: the same over `ℤ`, where it says the
  rational `x`-coordinate is an integer — the conclusion the rational root theorem feeds into.

This is the denominator input to the Nagell–Lutz integrality milestone of
`TauCetiRoadmap/EllipticCurves/README.md`, Layer 6, item "The torsion subgroup and Nagell–Lutz".
No torsion hypothesis is needed here: the statements hold for every point.

## Provenance

Ported from the AINTLIB `NagellLutz` project (`github.com/CBirkbeck/AINTLIB`, Apache-2.0), pinned by
that roadmap at `dev/modular-curves @ 9fec8eba7652`: the descent follows
`LutzNagell/LutzNagellTheorem/PIDDenominators.lean`
(`den_no_simple_prime_factor_of_on_curve`, `den_not_prime_of_on_curve`) and its positive restatement
`den_powerful_of_on_curve` in `LutzNagell/LutzNagellTheorem/PIDMain.lean`.

The `ℚ`/`ℤ` conclusion follows `LutzNagell/LutzNagellTheorem/GeneralDenominators.lean`,
declaration `den_ne_prime_of_on_general_curve`. That source states the prime-denominator
exclusion — extra hypothesis `x.den = p` for a prime `p`, conclusion `False` — and names the
divisibility consequence in its docstring without stating it; `den_eq_one_of_dvd_squarefree` is
that consequence, with a squarefree bound in place of a prime one.
-/

public section

open IsFractionRing

namespace TauCeti

namespace WeierstrassCurve

section Descent

variable {R : Type*} [CommRing R] [NoZeroDivisors R]

/-- The descent behind the powerful-denominator theorem, over a commutative ring without zero
divisors — no fraction field, no curve.

The hypothesis is the Weierstrass equation of the point `(α / (q * u), γ / e)` with denominators
cleared, the cubic in the numerator of the `x`-coordinate split as `α ^ 3 + q * c`. Dividing by
`q ^ 2` and then by `q` in turn shows `q ^ 2 ∣ e` and then `q ∣ γ`, so `γ / e` is not in lowest
terms. -/
private lemma not_isRelPrime_of_cleared_equation {q u γ e α c A B : R} (hq : Prime q)
    (hu : ¬q ∣ u) (hα : ¬q ∣ α) (h : γ ^ 2 * (q * u) ^ 3 + A * (q * u) ^ 2 * e
      + B * (q * u) ^ 3 * e = e ^ 2 * (α ^ 3 + q * c)) : ¬IsRelPrime γ e := by
  have hS : ¬q ∣ α ^ 3 + q * c := fun hd ↦
    hα <| hq.dvd_of_dvd_pow <| (dvd_add_left (dvd_mul_right q c)).mp hd
  -- Every term on the left is divisible by `q`, hence so is `e`.
  have hdvd : q ∣ e ^ 2 * (α ^ 3 + q * c) := h ▸
    ⟨γ ^ 2 * (q ^ 2 * u ^ 3) + A * (q * u ^ 2) * e + B * (q ^ 2 * u ^ 3) * e, by ring⟩
  obtain ⟨e₁, he₁⟩ : q ∣ e := hq.dvd_of_dvd_pow ((hq.dvd_or_dvd hdvd).resolve_right hS)
  -- Divide the identity by `q ^ 2`; the left-hand side is still divisible by `q`.
  have h₂ : q * (γ ^ 2 * u ^ 3 + A * u ^ 2 * e₁ + B * q * u ^ 3 * e₁) =
      e₁ ^ 2 * (α ^ 3 + q * c) := by
    rw [he₁] at h
    exact mul_left_cancel₀ (pow_ne_zero 2 hq.ne_zero) (by linear_combination h)
  obtain ⟨e₂, he₂⟩ : q ∣ e₁ :=
    hq.dvd_of_dvd_pow <| (hq.dvd_or_dvd ⟨_, h₂.symm⟩).resolve_right hS
  -- Divide once more; now `q` divides `γ ^ 2 * u ^ 3`, and `q ∤ u`, so `q` divides `γ`.
  have h₃ : γ ^ 2 * u ^ 3 + q * (A * u ^ 2 * e₂ + B * q * u ^ 3 * e₂) =
      q * (e₂ ^ 2 * (α ^ 3 + q * c)) := by
    rw [he₂] at h₂
    exact mul_left_cancel₀ hq.ne_zero (by linear_combination h₂)
  have hγ : q ∣ γ := hq.dvd_of_dvd_pow <| (hq.dvd_or_dvd (a := γ ^ 2) (b := u ^ 3)
    ⟨e₂ ^ 2 * (α ^ 3 + q * c) - (A * u ^ 2 * e₂ + B * q * u ^ 3 * e₂),
      by linear_combination h₃⟩).resolve_right fun hd ↦ hu (hq.dvd_of_dvd_pow hd)
  exact fun hrel ↦ hq.not_isUnit (hrel hγ ⟨q * e₂, by rw [he₁, he₂]⟩)

end Descent

variable {R : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
variable (W : _root_.WeierstrassCurve R) {x y : K} {q : R}

/-- The Weierstrass equation with the denominators of the two coordinates cleared: an identity
in `R` between the numerators and denominators of a `K`-point. -/
private lemma num_den_equation (h : (W.baseChange K).toAffine.Equation x y) :
    num R y ^ 2 * (den R x : R) ^ 3 + W.a₁ * num R x * num R y * (den R x : R) ^ 2 * (den R y : R)
        + W.a₃ * num R y * (den R x : R) ^ 3 * (den R y : R) =
      (den R y : R) ^ 2 * (num R x ^ 3 + W.a₂ * num R x ^ 2 * (den R x : R)
        + W.a₄ * num R x * (den R x : R) ^ 2 + W.a₆ * (den R x : R) ^ 3) := by
  have hd : (algebraMap R K (den R x : R)) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (den R x).2
  have he : (algebraMap R K (den R y : R)) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (den R y).2
  apply IsFractionRing.injective R K
  rw [_root_.WeierstrassCurve.Affine.equation_iff, ← mk'_num_den' R x, ← mk'_num_den' R y] at h
  simp only [_root_.WeierstrassCurve.baseChange, _root_.WeierstrassCurve.map_a₁,
    _root_.WeierstrassCurve.map_a₂, _root_.WeierstrassCurve.map_a₃,
    _root_.WeierstrassCurve.map_a₄, _root_.WeierstrassCurve.map_a₆] at h
  push_cast
  field_simp at h ⊢
  linear_combination h

/-- **The denominator of the `x`-coordinate of a point is powerful.**

If `(x, y)` is a point of `W` over the fraction field `K` of a unique factorization domain `R`,
then a prime of `R` dividing the denominator of `x` divides it at least twice. -/
theorem sq_dvd_den_of_prime_of_dvd (h : (W.baseChange K).toAffine.Equation x y) (hq : Prime q)
    (hqd : q ∣ (den R x : R)) : q ^ 2 ∣ (den R x : R) := by
  by_contra hq2
  obtain ⟨u, hu⟩ := hqd
  have key := num_den_equation W h
  rw [hu] at key
  set α := num R x
  set γ := num R y
  set e := (den R y : R)
  have hu' : ¬q ∣ u := fun ⟨v, hv⟩ ↦ hq2 ⟨v, by rw [hu, hv]; ring⟩
  have hα : ¬q ∣ α := fun hd ↦ hq.not_isUnit (num_den_reduced R x hd ⟨u, hu⟩)
  have hcl : γ ^ 2 * (q * u) ^ 3 + W.a₁ * α * γ * (q * u) ^ 2 * e
      + W.a₃ * γ * (q * u) ^ 3 * e = e ^ 2 * (α ^ 3 +
        q * (W.a₂ * α ^ 2 * u + W.a₄ * α * u ^ 2 * q + W.a₆ * u ^ 3 * q ^ 2)) := by
    linear_combination key
  exact not_isRelPrime_of_cleared_equation hq hu' hα hcl (num_den_reduced R y)

/-- **A squarefree bound on the denominator forces it to be a unit.**

A prime dividing the denominator divides it twice (`sq_dvd_den_of_prime_of_dvd`), so it would
divide any bound twice as well; a squarefree bound admits no such prime, leaving the denominator
without prime factors. -/
theorem isUnit_den_of_dvd_squarefree (h : (W.baseChange K).toAffine.Equation x y) {m : R}
    (hsf : Squarefree m) (hdvd : (den R x : R) ∣ m) : IsUnit (den R x : R) := by
  by_contra hnu
  obtain ⟨q, hq_irr, hq_dvd⟩ := WfDvdMonoid.exists_irreducible_factor hnu
    (mem_nonZeroDivisors_iff_ne_zero.mp (den R x).2)
  have hq : Prime q := UniqueFactorizationMonoid.irreducible_iff_prime.mp hq_irr
  have hqq : q * q ∣ (den R x : R) := by
    rw [← pow_two]; exact sq_dvd_den_of_prime_of_dvd W h hq hq_dvd
  exact hq.not_isUnit (hsf q (hqq.trans hdvd))

/-- **The denominator of the `x`-coordinate of a point is not prime.**

The Nagell–Lutz form of `TauCeti.WeierstrassCurve.sq_dvd_den_of_prime_of_dvd`: a prime element is
not divisible by its own square, so it cannot be the denominator of the `x`-coordinate of a
point. -/
theorem not_prime_den (h : (W.baseChange K).toAffine.Equation x y) :
    ¬Prime (den R x : R) := fun hp ↦
  hp.not_isUnit <| hp.irreducible.squarefree _ <| by
    simpa [sq] using sq_dvd_den_of_prime_of_dvd W h hp dvd_rfl

/-- **A rational point whose `x`-denominator divides a squarefree number has an integral
`x`-coordinate.**

The `ℚ`/`ℤ` form of `isUnit_den_of_dvd_squarefree`, which is what the Nagell–Lutz integrality
argument consumes: the rational root theorem bounds `x.den`, and a squarefree bound leaves the
denominator a unit, hence `1`. Over `ℤ` the ring-theoretic denominator and the numeral agree up
to sign (`Rat.isFractionRingDen`). -/
theorem den_eq_one_of_dvd_squarefree {W : _root_.WeierstrassCurve ℤ} {x y : ℚ}
    (h : (W.baseChange ℚ).toAffine.Equation x y) {m : ℕ} (hsf : Squarefree m)
    (hdvd : x.den ∣ m) : x.den = 1 := by
  have hunit : IsUnit (den ℤ x : ℤ) := by
    refine isUnit_den_of_dvd_squarefree W h (m := (m : ℤ)) (Int.squarefree_natCast.mpr hsf) ?_
    rw [← Int.natAbs_dvd, Rat.isFractionRingDen x]
    exact Int.natCast_dvd_natCast.mpr hdvd
  rw [← Rat.isFractionRingDen x]
  exact Int.isUnit_iff_natAbs_eq.mp hunit

end WeierstrassCurve

end TauCeti
