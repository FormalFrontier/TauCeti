/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.RingTheory.Valuation.Basic

import Mathlib.Algebra.Order.Group.Basic
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.RingTheory.Polynomial.Subring
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.Tactic.ComputeDegree

/-!
# Valuations of roots of monic polynomials

Elementary estimates for a valuation `ν` on a commutative ring: a product of two `ν`-integral
elements that is a `ν`-unit has `ν`-unit factors, and for a monic polynomial `p` with
`ν`-integral coefficients the leading term dominates at any `t` with `1 < ν t`, so that
`ν (p.eval t) = ν t ^ p.natDegree`. Mathlib has the *inequality* that such an estimate gives, as
integral closedness of the valuation ring; the equality is what is added here, and
`le_one_of_root_monic` is Mathlib's statement in the coefficientwise form the callers use.

## Main results

* `Valuation.eq_one_of_mul_eq_one`: if `ν a ≤ 1`, `ν b ≤ 1` and `ν (a * b) = 1`, then `ν a = 1`.
* `Valuation.map_eval_eq_of_one_lt`: `ν (p.eval t) = ν t ^ p.natDegree` for monic `p` with
  `ν`-integral coefficients and `1 < ν t`.
* `Valuation.le_one_of_root_monic`: a root of a monic polynomial with `ν`-integral coefficients
  is `ν`-integral, from `Valuation.Integers.isIntegral_iff_v_le_one`.
* `Valuation.map_cubic_eq_of_one_lt` and `Valuation.le_one_of_root_cubic`: the two statements above
  for the monic cubic `t³ + at² + bt + c`, which is the shape a Weierstrass equation takes.

## Roadmap

`TauCetiRoadmap/EllipticCurves/README.md`, Layer 6 (Mordell–Weil): the `2`-descent has to see that
a root of the Weierstrass cubic is integral at every prime where the cubic's coefficients are, which
is `le_one_of_root_monic`. Nothing here mentions a curve, so it is stated for a bare valuation. The
companion estimate, for a polynomial *expression* in an element that is already integral, is
`TauCeti.RingTheory.Valuation.Polynomial`.

## Provenance

Adapted, with the author's proofs, from Michael Stoll's `EllipticCurves` project
(`github.com/MichaelStollBayreuth/EllipticCurves`, Apache-2.0, pinned by
`TauCetiRoadmap/EllipticCurves/README.md` at `66889eada51a`),
`EllipticCurves/Mathlib/Basic.lean`, section `Valuation`, together with the cubic specializations
from `EllipticCurves/WeakMordellWeil.lean`, section `Cubic`. The source is written against Lean
`v4.32.0`; this is a forward port.
-/

public section

namespace Valuation

open Polynomial

variable {L Γ : Type*} [CommRing L] [LinearOrderedCommGroupWithZero Γ] (ν : Valuation L Γ)
  {t a b : L}

/-- If a product of two integral elements is a unit, then each factor is a unit. -/
lemma eq_one_of_mul_eq_one (ha : ν a ≤ 1) (hb : ν b ≤ 1) (hab : ν (a * b) = 1) :
    ν a = 1 := by
  refine le_antisymm ha ?_
  calc (1 : Γ) = ν a * ν b := by rw [← map_mul, hab]
    _ ≤ ν a * 1 := by gcongr
    _ = ν a := mul_one _

/-- If `p` is monic with coefficients that are integral for the valuation `ν` and `1 < ν t`,
then the value of `p` at `t` is dominated by the leading term: `ν (p.eval t) = ν t ^ p.natDegree`.
In particular, `p.eval t ≠ 0`. -/
lemma map_eval_eq_of_one_lt {p : L[X]} (hp : p.Monic)
    (hcoeff : ∀ i < p.natDegree, ν (p.coeff i) ≤ 1) (ht : 1 < ν t) :
    ν (p.eval t) = ν t ^ p.natDegree := by
  set n := p.natDegree with hn
  have h0 : ν t ≠ 0 := (zero_lt_one.trans ht).ne'
  have heval : p.eval t = (∑ i ∈ Finset.range n, p.coeff i * t ^ i) + t ^ n := by
    rw [eval_eq_sum_range, Finset.sum_range_succ, hp.coeff_natDegree, one_mul]
  have hlt : ν (∑ i ∈ Finset.range n, p.coeff i * t ^ i) < ν (t ^ n) := by
    rw [map_pow]
    refine ν.map_sum_lt (pow_ne_zero n h0) fun i hi ↦ ?_
    rw [Finset.mem_range] at hi
    calc ν (p.coeff i * t ^ i) ≤ 1 * ν t ^ i := by
          rw [map_mul, map_pow]; gcongr; exact hcoeff i hi
      _ = ν t ^ i := one_mul _
      _ < ν t ^ n := pow_lt_pow_right₀ ht hi
  rw [heval, ν.map_add_eq_of_lt_right hlt, map_pow]

/-- A root of a monic polynomial whose coefficients are integral for the valuation `ν` is itself
integral: such a root is integral over `ν.integer`, and a valuation ring is integrally closed
(`Valuation.Integers.isIntegral_iff_v_le_one`). Stated in terms of the coefficients, which is how
the callers have the hypothesis. -/
lemma le_one_of_root_monic {p : L[X]} (hp : p.Monic)
    (hcoeff : ∀ i < p.natDegree, ν (p.coeff i) ≤ 1) (heq : p.eval t = 0) :
    ν t ≤ 1 := by
  have hsub : (↑p.coeffs : Set L) ⊆ ν.integer := by
    intro a ha
    obtain ⟨i, -, rfl⟩ := Polynomial.mem_coeffs_iff.mp ha
    rcases lt_trichotomy i p.natDegree with hi | hi | hi
    · exact hcoeff i hi
    · simp [hi, hp.coeff_natDegree]
    · simp [p.coeff_eq_zero_of_natDegree_lt hi]
  have hmap : (p.toSubring ν.integer hsub).map (algebraMap ν.integer L) = p :=
    Polynomial.map_toSubring p ν.integer hsub
  refine (Valuation.integer.integers ν).mem_of_integral
    ⟨p.toSubring _ hsub, (Polynomial.monic_toSubring _ _ _).mpr hp, ?_⟩
  rw [Polynomial.eval₂_eq_eval_map, hmap, heq]

section Cubic

variable {c : L}

-- `compute_degree!` and `monicity!` need `Nontrivial L` below, to know that the leading
-- coefficient `1` is nonzero and hence that the cubic really has degree `3`. Pulling `Nontrivial`
-- back along `ν` keeps it out of the signatures, which hold over any `L`: `(0 : L) = 1` would
-- force `(0 : Γ) = 1`, which a `LinearOrderedCommGroupWithZero` forbids.

/-- The non-leading coefficients of `X³ + aX² + bX + c` are `a`, `b`, `c` (and zeros), so they
are integral as soon as `a`, `b`, `c` are. This is the coefficient hypothesis that the general
lemmas above take. -/
private lemma cubic_coeff_le_one (ha : ν a ≤ 1) (hb : ν b ≤ 1) (hc : ν c ≤ 1) :
    ∀ i < (X ^ 3 + C a * X ^ 2 + C b * X + C c).natDegree,
      ν ((X ^ 3 + C a * X ^ 2 + C b * X + C c).coeff i) ≤ 1 := by
  have := domain_nontrivial ν ν.map_zero ν.map_one
  have hdeg : (X ^ 3 + C a * X ^ 2 + C b * X + C c).natDegree = 3 := by compute_degree!
  intro i hi
  rw [hdeg] at hi
  interval_cases i <;> simp [ha, hb, hc]

/-- A monic cubic with integral coefficients, evaluated at an element of value `> 1`, is
dominated by its leading term. -/
lemma map_cubic_eq_of_one_lt (ha : ν a ≤ 1) (hb : ν b ≤ 1) (hc : ν c ≤ 1) (ht : 1 < ν t) :
    ν (t ^ 3 + a * t ^ 2 + b * t + c) = ν t ^ 3 := by
  have := domain_nontrivial ν ν.map_zero ν.map_one
  have hp : (X ^ 3 + C a * X ^ 2 + C b * X + C c).Monic := by monicity!
  have hdeg : (X ^ 3 + C a * X ^ 2 + C b * X + C c).natDegree = 3 := by compute_degree!
  have h := ν.map_eval_eq_of_one_lt hp (cubic_coeff_le_one ν ha hb hc) ht
  rw [hdeg] at h
  simpa using h

/-- A root of a monic cubic with integral coefficients is integral. -/
lemma le_one_of_root_cubic (ha : ν a ≤ 1) (hb : ν b ≤ 1) (hc : ν c ≤ 1)
    (heq : t ^ 3 + a * t ^ 2 + b * t + c = 0) :
    ν t ≤ 1 := by
  have := domain_nontrivial ν ν.map_zero ν.map_one
  have hp : (X ^ 3 + C a * X ^ 2 + C b * X + C c).Monic := by monicity!
  refine ν.le_one_of_root_monic hp (cubic_coeff_le_one ν ha hb hc) ?_
  simpa using heq

end Cubic

end Valuation

end
