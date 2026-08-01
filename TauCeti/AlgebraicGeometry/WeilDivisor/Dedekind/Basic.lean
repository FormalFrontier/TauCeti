/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.WeilDivisor.Principal.Basic
public import Mathlib.RingTheory.ClassGroup.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation
public import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import Mathlib.RingTheory.DedekindDomain.SelmerGroup

/-!
# The order system of a Dedekind domain

The abstract `OrderSystem` of `TauCeti.AlgebraicGeometry.WeilDivisor.Principal.Basic` packages the
order-of-vanishing data needed to build principal divisors and the divisor class group. This
file supplies the roadmap's intended *concrete* instance of that data: a Dedekind domain `R`
with fraction field `K`. Its height-one spectrum `HeightOneSpectrum R` is the set of
codimension-one points of `Spec R` (an affine model of a curve, or the ring of integers of a
number field), and the `v`-adic valuation gives each point an order-of-vanishing homomorphism
on the multiplicative group `Kˣ` of nonzero rational functions.

Concretely we build:

* `adicOrd R K v : Additive Kˣ →+ ℤ`, the order of vanishing `ord_v(f) = -log v(f)` of a
  nonzero rational function `f` at the height-one prime `v` (the sign makes a uniformizer have
  order `+1`, i.e. a simple zero);
* `OrderSystem.ofDedekindDomain R K : OrderSystem (HeightOneSpectrum R) (Additive Kˣ)`, whose
  finiteness condition is exactly the statement that a nonzero rational function has zeros and
  poles at only finitely many primes;
* `(OrderSystem.ofDedekindDomain R K).ClassGroup`, the resulting Weil-divisor presentation of
  the class group (the quotient of Weil divisors by principal divisors; its isomorphism to
  `ClassGroup R` is not constructed here);
* the sanity check that the principal divisor of a nonzero *integral* element is effective
  (an element of `R` has no poles).

The roadmap explicitly anticipates this instantiation: "Instantiate `G` with `Additive Kˣ`
for the multiplicative group of a function field `K`: then `ord x` is the order of vanishing
`ord_x(f)`". This advances `TauCetiRoadmap/JacobianChallenge/README.md`, Layer A ("Divisors on
a curve: Weil divisors `⊕_x ℤ`", "principal divisors", "`Cl(X)`"), grounding the abstract
order-system API in Mathlib's Dedekind-domain adic valuations.

We do *not* claim the weighted-degree-zero property here: for a general Dedekind domain (e.g.
`ℤ`) there is no product formula, so a principal divisor need not have degree zero. That holds
only for proper curves over a field (and number fields with the archimedean places included),
and is later geometric input.

This reuses Mathlib's `IsDedekindDomain.HeightOneSpectrum.valuationOfNeZero` (the multiplicative
`v`-adic valuation `Kˣ →* Multiplicative ℤ`, whose multiplicativity `adicOrd` inherits), the
`WithZero.log` logarithm on `ℤᵐ⁰`, and `IsDedekindDomain.HeightOneSpectrum.Support.finite`
(finiteness of the support of a rational function); no external mathematics is vendored.
-/

public section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open scoped nonZeroDivisors

namespace TauCeti

namespace AlgebraicGeometry

namespace WeilDivisor

variable (R : Type*) [CommRing R] [IsDedekindDomain R]
variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

/-- The order of vanishing `ord_v(f) = -log v(f)` of a nonzero rational function `f : Kˣ` at a
height-one prime `v` of a Dedekind domain `R`, as a homomorphism `Additive Kˣ →+ ℤ`. It is the
additive, sign-flipped form of Mathlib's multiplicative valuation
`IsDedekindDomain.HeightOneSpectrum.valuationOfNeZero v : Kˣ →* Multiplicative ℤ`; the sign is
chosen so that a uniformizer at `v` has order `+1` (a simple zero) and a pole has negative
order. -/
noncomputable def adicOrd (v : HeightOneSpectrum R) : Additive Kˣ →+ ℤ :=
  -MonoidHom.toAdditiveLeft (v.valuationOfNeZero (K := K))

variable {R K}

/-- For a nonzero element `x : ℤᵐ⁰`, its logarithm vanishes exactly when `x = 1`. This is the
shared logarithm fact behind both the `≠ 1` step of the finiteness proof and the support
criterion `mem_support_principalDivisor_iff_valuation_ne_one`. -/
private lemma log_eq_zero_iff_eq_one {x : ℤᵐ⁰} (hx : x ≠ 0) :
    WithZero.log x = 0 ↔ x = 1 := by
  constructor
  · intro h
    have hx' := WithZero.exp_log hx
    rw [h, WithZero.exp_zero] at hx'
    exact hx'.symm
  · intro h
    rw [h, WithZero.log_one]

/-- The computational form of `adicOrd`: the order at `v` of an element `u : Additive Kˣ` is the
sign-flipped logarithm `-log v(u)` of its `v`-adic valuation, where the underlying rational
function is `(Additive.toMul u : Kˣ) : K`. The minus sign makes a uniformizer have order `+1`. -/
@[simp]
lemma adicOrd_apply (v : HeightOneSpectrum R) (u : Additive Kˣ) :
    adicOrd R K v u = -WithZero.log (v.valuation K ((Additive.toMul u : Kˣ) : K)) := by
  rw [adicOrd, AddMonoidHom.neg_apply, MonoidHom.coe_toAdditiveLeft, Function.comp_apply,
    Function.comp_apply, ← valuationOfNeZero_eq]
  rfl

/-- The computational form of `adicOrd` applied to `Additive.ofMul u` for a multiplicative unit
`u : Kˣ`: it is the sign-flipped logarithm `-log v(u)` of the `v`-adic valuation of `u : K`. -/
lemma adicOrd_ofMul (v : HeightOneSpectrum R) (u : Kˣ) :
    adicOrd R K v (Additive.ofMul u) = -WithZero.log (v.valuation K (u : K)) := by
  rw [adicOrd_apply]
  rfl

/-- The order `ord_v(f)` is nonnegative exactly when `f` is integral at `v`, i.e. has
valuation at most one. -/
lemma adicOrd_nonneg_iff (v : HeightOneSpectrum R) (u : Additive Kˣ) :
    0 ≤ adicOrd R K v u ↔ v.valuation K ((Additive.toMul u : Kˣ) : K) ≤ 1 := by
  have hu : v.valuation K ((Additive.toMul u : Kˣ) : K) ≠ 0 :=
    (v.valuation K).ne_zero_iff.mpr (Units.ne_zero _)
  rw [adicOrd_apply, neg_nonneg, ← WithZero.log_one (M := ℤ),
    WithZero.log_le_log hu one_ne_zero]

/-- A nonzero `v`-adic order means that `v` lies in the support of the function or of its
inverse. This is the implementation helper that drives the finiteness proof of
`OrderSystem.ofDedekindDomain`. -/
private lemma adicOrd_ne_zero_mem_support_union (v : HeightOneSpectrum R) (u : Additive Kˣ)
    (h : adicOrd R K v u ≠ 0) :
    v ∈ HeightOneSpectrum.Support R ((Additive.toMul u : Kˣ) : K) ∪
      HeightOneSpectrum.Support R (((Additive.toMul u : Kˣ) : K)⁻¹) := by
  set k : K := ((Additive.toMul u : Kˣ) : K) with hk
  have hk0 : k ≠ 0 := Units.ne_zero _
  have hlog : WithZero.log (v.valuation K k) ≠ 0 := by
    simpa [adicOrd_apply, ← hk, neg_ne_zero] using h
  have hval : v.valuation K k ≠ 0 := (v.valuation K).ne_zero_iff.mpr hk0
  have hne_one : v.valuation K k ≠ 1 := fun h => hlog ((log_eq_zero_iff_eq_one hval).2 h)
  rcases lt_or_gt_of_ne hne_one with hlt | hgt
  · refine Or.inr ?_
    rw [HeightOneSpectrum.Support, Set.mem_ofPred_eq, map_inv₀]
    exact (one_lt_inv₀ (WithZero.pos_iff_ne_zero.mpr hval)).mpr hlt
  · exact Or.inl hgt

private lemma toPrincipalIdeal_eq_spanSingleton_inv_mul_span_mk'_num (u : Kˣ) (n : R)
    (d : R⁰) (hnd : IsLocalization.mk' K n d = (u : K)) :
    (toPrincipalIdeal R K u : FractionalIdeal R⁰ K) =
      FractionalIdeal.spanSingleton R⁰ ((algebraMap R K) (d : R))⁻¹ *
        ↑(Ideal.span {n} : Ideal R) := by
  rw [coe_toPrincipalIdeal, ← hnd, IsFractionRing.mk'_eq_div,
    ← FractionalIdeal.spanSingleton_div_spanSingleton, FractionalIdeal.div_spanSingleton,
    FractionalIdeal.coeIdeal_span_singleton]

private lemma valuation_mk'_eq_intValuation_div (v : HeightOneSpectrum R) (n : R) (d : R⁰) :
    v.valuation K (IsLocalization.mk' K n d) =
      v.intValuation n / v.intValuation (d : R) :=
  v.valuation_of_mk'

private lemma fractionalIdeal_count_spanSingleton_eq_neg_log_intValuation
    (v : HeightOneSpectrum R) (r : R) (hr : r ≠ 0) :
    FractionalIdeal.count K v (FractionalIdeal.spanSingleton R⁰ (algebraMap R K r)) =
      -WithZero.log (v.intValuation r) := by
  have hspan : (Ideal.span {r} : Ideal R) ≠ 0 := by
    simpa [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot] using hr
  rw [← FractionalIdeal.coeIdeal_span_singleton (S := R⁰) (P := K) r,
    FractionalIdeal.count_coe K v hspan, v.intValuation_if_neg hr, WithZero.log_exp]
  ring

private lemma fractionalIdeal_spanSingleton_ne_zero_of_ne_zero (r : R) (hr : r ≠ 0) :
    FractionalIdeal.spanSingleton R⁰ (algebraMap R K r) ≠ 0 := by
  rw [FractionalIdeal.spanSingleton_ne_zero_iff]
  intro h
  exact hr ((IsLocalization.injective K (le_refl R⁰)) (by simpa using h))

private lemma fractionalIdeal_count_spanSingleton_inv_eq_log_intValuation
    (v : HeightOneSpectrum R) (r : R) (hr : r ≠ 0) :
    FractionalIdeal.count K v (FractionalIdeal.spanSingleton R⁰ (algebraMap R K r))⁻¹ =
      WithZero.log (v.intValuation r) := by
  rw [FractionalIdeal.count_inv,
    fractionalIdeal_count_spanSingleton_eq_neg_log_intValuation (K := K) v r hr]
  ring

private lemma fractionalIdeal_count_spanSingleton_inv_mul_spanSingleton_eq_neg_log_div
    (v : HeightOneSpectrum R) (n d : R) (hn : n ≠ 0) (hd : d ≠ 0) :
    FractionalIdeal.count K v
        (FractionalIdeal.spanSingleton R⁰ ((algebraMap R K d)⁻¹) *
          FractionalIdeal.spanSingleton R⁰ (algebraMap R K n)) =
      -WithZero.log (v.intValuation n / v.intValuation d) := by
  have hnI := fractionalIdeal_spanSingleton_ne_zero_of_ne_zero (K := K) n hn
  have hdI := fractionalIdeal_spanSingleton_ne_zero_of_ne_zero (K := K) d hd
  rw [← FractionalIdeal.spanSingleton_inv K (algebraMap R K d)]
  rw [FractionalIdeal.count_mul K v (inv_ne_zero hdI) hnI,
    fractionalIdeal_count_spanSingleton_inv_eq_log_intValuation (K := K) v d hd,
    fractionalIdeal_count_spanSingleton_eq_neg_log_intValuation (K := K) v n hn]
  rw [WithZero.log_div (v.intValuation_ne_zero n hn) (v.intValuation_ne_zero d hd)]
  ring

/-- Mathlib's exponent of a principal fractional ideal is the sign-flipped logarithm of the
corresponding height-one valuation. Stated at the multiplicative-units level `u : Kˣ`, matching
Mathlib's `toPrincipalIdeal R K : Kˣ →* _`; the order-system/`Additive` form is recovered by
`adicOrd_eq_fractionalIdeal_count`. -/
lemma fractionalIdeal_count_toPrincipalIdeal_eq_neg_log_valuation (v : HeightOneSpectrum R)
    (u : Kˣ) :
    FractionalIdeal.count K v
      (toPrincipalIdeal R K u : FractionalIdeal R⁰ K) =
        -WithZero.log (v.valuation K (u : K)) := by
  set k : K := (u : K) with hk
  obtain ⟨n, d, hnd⟩ := IsLocalization.exists_mk'_eq R⁰ k
  have hn : n ≠ 0 := by
    intro hn
    have hk0 : k ≠ 0 := Units.ne_zero _
    apply hk0
    rw [← hnd, hn, IsFractionRing.mk'_eq_div, map_zero, zero_div]
  have hd : (d : R) ≠ 0 := nonZeroDivisors.ne_zero d.2
  have hrepr :
      (toPrincipalIdeal R K u : FractionalIdeal R⁰ K) =
        FractionalIdeal.spanSingleton R⁰ ((algebraMap R K) (d : R))⁻¹ *
          ↑(Ideal.span {n} : Ideal R) := by
    exact toPrincipalIdeal_eq_spanSingleton_inv_mul_span_mk'_num (R := R) (K := K) u n d
      (by rw [hnd, hk])
  have hval :
      v.valuation K k = v.intValuation n / v.intValuation (d : R) := by
    rw [← hnd]
    exact valuation_mk'_eq_intValuation_div (R := R) (K := K) v n d
  rw [hval, hrepr, FractionalIdeal.coeIdeal_span_singleton]
  exact fractionalIdeal_count_spanSingleton_inv_mul_spanSingleton_eq_neg_log_div (R := R)
    (K := K) v n d hn hd

/-- The `v`-adic order of a rational function agrees with Mathlib's exponent of the
corresponding principal fractional ideal. -/
lemma adicOrd_eq_fractionalIdeal_count (v : HeightOneSpectrum R) (u : Additive Kˣ) :
    adicOrd R K v u =
      FractionalIdeal.count K v
        (toPrincipalIdeal R K (Additive.toMul u) : FractionalIdeal R⁰ K) := by
  rw [adicOrd_apply, fractionalIdeal_count_toPrincipalIdeal_eq_neg_log_valuation]

variable (R K)

/-- The order system of a Dedekind domain `R` with fraction field `K`: its points are the
height-one primes `v` of `R`, the group is the multiplicative group `Kˣ` of nonzero rational
functions, and the order at `v` is the `v`-adic order of vanishing. The finiteness condition is
exactly the statement that a nonzero rational function has zeros and poles at only finitely many
primes. -/
@[expose] noncomputable def OrderSystem.ofDedekindDomain :
    OrderSystem (HeightOneSpectrum R) (Additive Kˣ) where
  ord v := adicOrd R K v
  finite_support u := by
    refine Set.Finite.subset
      ((HeightOneSpectrum.Support.finite (R := R) (K := K)
          ((Additive.toMul u : Kˣ) : K)).union
        (HeightOneSpectrum.Support.finite (R := R) (K := K)
          (((Additive.toMul u : Kˣ) : K)⁻¹))) ?_
    intro v hv
    exact adicOrd_ne_zero_mem_support_union (R := R) (K := K) v u hv

/-- The order map of the Dedekind-domain order system at a height-one prime `v` is the `v`-adic
order of vanishing `adicOrd R K v`. -/
@[simp]
lemma OrderSystem.ofDedekindDomain_ord (v : HeightOneSpectrum R) :
    (OrderSystem.ofDedekindDomain R K).ord v = adicOrd R K v :=
  rfl

/-- The coefficient of the principal divisor of `f : Kˣ` at a height-one prime `v` is the
`v`-adic order of vanishing `-log v(f)`. -/
lemma coeff_principalDivisor_eq_neg_log_valuation (u : Additive Kˣ) (v : HeightOneSpectrum R) :
    coeff ((OrderSystem.ofDedekindDomain R K).principalDivisor u) v =
      -WithZero.log (v.valuation K ((Additive.toMul u : Kˣ) : K)) := by
  rw [OrderSystem.coeff_principalDivisor, OrderSystem.ofDedekindDomain_ord, adicOrd_apply]

/-- The coefficient of a Dedekind-domain principal divisor agrees with Mathlib's exponent of the
corresponding principal fractional ideal. -/
lemma coeff_principalDivisor_eq_fractionalIdeal_count (u : Additive Kˣ)
    (v : HeightOneSpectrum R) :
    coeff ((OrderSystem.ofDedekindDomain R K).principalDivisor u) v =
      FractionalIdeal.count K v
        (toPrincipalIdeal R K (Additive.toMul u) : FractionalIdeal R⁰ K) := by
  rw [OrderSystem.coeff_principalDivisor, OrderSystem.ofDedekindDomain_ord,
    adicOrd_eq_fractionalIdeal_count]

/-- A height-one prime lies in the support of a principal divisor exactly when the corresponding
valuation is not one. -/
lemma mem_support_principalDivisor_iff_valuation_ne_one (u : Additive Kˣ)
    (v : HeightOneSpectrum R) :
    v ∈ ((OrderSystem.ofDedekindDomain R K).principalDivisor u).support ↔
      v.valuation K ((Additive.toMul u : Kˣ) : K) ≠ 1 := by
  have hu : v.valuation K ((Additive.toMul u : Kˣ) : K) ≠ 0 :=
    (v.valuation K).ne_zero_iff.mpr (Units.ne_zero _)
  rw [WeilDivisor.mem_support_iff]
  rw [coeff_principalDivisor_eq_neg_log_valuation, neg_ne_zero]
  exact not_congr (log_eq_zero_iff_eq_one hu)

variable {R K}

/-- A coefficient of a principal divisor is positive exactly when the corresponding valuation is
strictly less than one. -/
lemma coeff_principalDivisor_pos_iff_valuation_lt_one (u : Additive Kˣ)
    (v : HeightOneSpectrum R) :
    0 < coeff ((OrderSystem.ofDedekindDomain R K).principalDivisor u) v ↔
      v.valuation K ((Additive.toMul u : Kˣ) : K) < 1 := by
  have hu : v.valuation K ((Additive.toMul u : Kˣ) : K) ≠ 0 :=
    (v.valuation K).ne_zero_iff.mpr (Units.ne_zero _)
  rw [coeff_principalDivisor_eq_neg_log_valuation, neg_pos, ← WithZero.log_one (M := ℤ),
    WithZero.log_lt_log hu one_ne_zero]

/-- The principal divisor of a nonzero *integral* element is effective: an element of `R` has
no poles, only zeros. The element is presented as any unit `u : Kˣ` whose value is
`algebraMap R K r`. This is the divisor-of-functions sanity check that rules out a vacuous
order system. -/
lemma isEffective_principalDivisor_of_integral {r : R} {u : Kˣ}
    (hu : (u : K) = algebraMap R K r) :
    IsEffective ((OrderSystem.ofDedekindDomain R K).principalDivisor (Additive.ofMul u)) := by
  rw [isEffective_iff]
  intro v
  rw [OrderSystem.coeff_principalDivisor, OrderSystem.ofDedekindDomain_ord, adicOrd_nonneg_iff]
  simp only [toMul_ofMul, hu]
  exact v.valuation_le_one r

/-- The divisor of a nonzero integral element `r : R`, presented as a unit `u : Kˣ` with value
`algebraMap R K r`, has a strictly positive coefficient (a genuine zero) at `v` exactly when `r`
lies in the prime `v`. -/
lemma coeff_principalDivisor_pos_iff_mem {r : R} {u : Kˣ} (hu : (u : K) = algebraMap R K r)
    (v : HeightOneSpectrum R) :
    0 < coeff ((OrderSystem.ofDedekindDomain R K).principalDivisor (Additive.ofMul u)) v ↔
      r ∈ v.asIdeal := by
  rw [coeff_principalDivisor_pos_iff_valuation_lt_one]
  simp only [toMul_ofMul, hu]
  exact v.valuation_lt_one_iff_mem r

/-- The support of the divisor of a nonzero integral element `r : R`, presented as a unit
`u : Kˣ` with value `algebraMap R K r`, is the set of height-one primes containing `r`. -/
lemma mem_support_principalDivisor_of_integral_iff_mem_asIdeal {r : R} {u : Kˣ}
    (hu : (u : K) = algebraMap R K r) (v : HeightOneSpectrum R) :
    v ∈ ((OrderSystem.ofDedekindDomain R K).principalDivisor (Additive.ofMul u)).support ↔
      r ∈ v.asIdeal := by
  rw [WeilDivisor.mem_support_iff]
  constructor
  · intro hv
    rw [← coeff_principalDivisor_pos_iff_mem hu v]
    exact lt_of_le_of_ne
      ((isEffective_iff _).mp (isEffective_principalDivisor_of_integral hu) v) (Ne.symm hv)
  · intro hv
    exact ne_of_gt ((coeff_principalDivisor_pos_iff_mem hu v).mpr hv)

end WeilDivisor

end AlgebraicGeometry

end TauCeti
