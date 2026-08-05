/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.WeilDivisor.Dedekind.Basic

/-!
# The Weil divisor of an invertible fractional ideal

For a Dedekind domain `R` with fraction field `K`,
`TauCeti.AlgebraicGeometry.WeilDivisor.Dedekind.Basic` turns the height-one spectrum of `R` into the
points of an affine curve and packages the order of vanishing of a rational function as the order
system `OrderSystem.ofDedekindDomain R K`. This basic module adds the *Cartier* side of that
picture: invertible fractional ideals of `R` are the Cartier divisors of the affine curve, and this
file identifies them with Weil divisors.

Concretely, a nonzero fractional ideal `I` has a well-defined `v`-adic multiplicity
`FractionalIdeal.count K v I` at each height-one prime `v`, zero for all but finitely many `v`, so
the assignment `v ↦ count K v I` is a Weil divisor. Because `count` is additive on products, this
gives a homomorphism

`fractionalIdealDivisor : Additive (FractionalIdeal R⁰ K)ˣ →+ WeilDivisor (HeightOneSpectrum R)`

from the group of invertible fractional ideals (every nonzero fractional ideal of a Dedekind domain
is invertible, `FractionalIdeal R⁰ K` being a semifield) to the free Weil-divisor group. This
homomorphism is an **isomorphism**: a fractional ideal is recovered from its multiplicities by the
factorization `I = ∏_v v^(count K v I)` (injectivity), and every finite integer combination of
primes is the divisor of the corresponding product of prime ideals (surjectivity). This is the
scheme-free, affine-chart form of the roadmap's **`Weil ≃ Cartier` dictionary**.

We also connect it to the order system already built: the divisor of the principal fractional ideal
`(x)` is exactly the principal divisor of the rational function `x`, so the isomorphism carries the
principal fractional ideals to the principal divisors. This is the compatibility on principal
elements needed before passing to quotient-level statements, which are not proved in this file.
The divisor of a prime `v` is the point divisor `[v]`, the sanity check that rules out a
vacuous map.

This advances `TauCetiRoadmap/JacobianChallenge/README.md`, Layer A, "Divisors on a curve",
specifically the "(smooth curve) `Weil ≃ Cartier`" dictionary realized here for the affine
Dedekind model. It reuses
Mathlib's `FractionalIdeal.count` factorization API (`count_mul`, `count_finsuppProd`,
`finprod_heightOneSpectrum_factorization'`, `count_maximal_coprime`) and Tau Ceti's `WeilDivisor`
and `OrderSystem.ofDedekindDomain` API; no external mathematics is vendored.
-/

public section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped nonZeroDivisors

namespace TauCeti

namespace AlgebraicGeometry

namespace WeilDivisor

variable (R : Type*) [CommRing R] [IsDedekindDomain R]
variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

/-- The **Weil divisor of an invertible fractional ideal**: the formal sum `Σ_v count K v I · [v]`
of the `v`-adic multiplicities of `I` over the height-one primes `v` of `R`, as a homomorphism from
the group of invertible fractional ideals to the free Weil-divisor group. The multiplicity is zero
for all but finitely many `v` (`FractionalIdeal.finite_factors`), and the multiplicativity of
`FractionalIdeal.count` makes this additive. -/
noncomputable def fractionalIdealDivisor :
    Additive (FractionalIdeal R⁰ K)ˣ →+ WeilDivisor (HeightOneSpectrum R) where
  toFun I := Finsupp.ofSupportFinite
    (fun v => FractionalIdeal.count K v (Units.val (Additive.toMul I)))
    (by
      simpa only [Function.support] using Filter.eventually_cofinite.mp
        (FractionalIdeal.finite_factors (Units.val (Additive.toMul I))))
  map_zero' := by
    apply Finsupp.ext
    intro v
    rw [Finsupp.ofSupportFinite_coe]
    simp only [toMul_zero, Units.val_one, Finsupp.coe_zero, Pi.zero_apply]
    exact FractionalIdeal.count_one K v
  map_add' I J := by
    apply Finsupp.ext
    intro v
    rw [Finsupp.add_apply, Finsupp.ofSupportFinite_coe, Finsupp.ofSupportFinite_coe,
      Finsupp.ofSupportFinite_coe]
    simp only [toMul_add, Units.val_mul]
    exact FractionalIdeal.count_mul K v (Units.ne_zero _) (Units.ne_zero _)

/-- The coefficient of `fractionalIdealDivisor R K I` at a height-one prime `v` is the
`v`-adic multiplicity `FractionalIdeal.count K v I` of the invertible fractional ideal `I`. -/
@[simp]
lemma coeff_fractionalIdealDivisor (I : Additive (FractionalIdeal R⁰ K)ˣ)
    (v : HeightOneSpectrum R) :
    coeff (fractionalIdealDivisor R K I) v =
      FractionalIdeal.count K v (Units.val (Additive.toMul I)) := by
  simp only [fractionalIdealDivisor, AddMonoidHom.coe_mk, ZeroHom.coe_mk, coeff,
    Finsupp.ofSupportFinite_coe]

/-- The divisor map is injective: an invertible fractional ideal is recovered from its
multiplicities through the factorization `I = ∏_v v^(count K v I)`. -/
lemma fractionalIdealDivisor_injective :
    Function.Injective (fractionalIdealDivisor R K) := by
  intro I J h
  have hcount : ∀ v, FractionalIdeal.count K v (Units.val (Additive.toMul I)) =
      FractionalIdeal.count K v (Units.val (Additive.toMul J)) := by
    intro v
    have hv := congrArg (fun D => coeff D v) h
    simpa only [coeff_fractionalIdealDivisor] using hv
  have key : Units.val (Additive.toMul I) = Units.val (Additive.toMul J) := by
    rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' K
          (Units.ne_zero (Additive.toMul I)),
        ← FractionalIdeal.finprod_heightOneSpectrum_factorization' K
          (Units.ne_zero (Additive.toMul J))]
    exact finprod_congr fun v => by rw [hcount v]
  exact Additive.toMul.injective (Units.ext key)

/-- The product `∏_v v^(D v)` of prime fractional ideals `v.asIdeal` raised to the multiplicities
`D v` of a Weil divisor `D` is nonzero, hence an invertible fractional ideal. This is the value of
the inverse of `fractionalIdealDivisor`. -/
lemma prod_asIdeal_zpow_ne_zero (D : WeilDivisor (HeightOneSpectrum R)) :
    (D.prod fun v e => (v.asIdeal : FractionalIdeal R⁰ K) ^ e) ≠ 0 := by
  rw [Finsupp.prod]
  exact Finset.prod_ne_zero_iff.mpr fun v _ =>
    zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot)

/-- The divisor map is surjective: a Weil divisor `D` is the divisor of the invertible fractional
ideal `∏_v v^(D v)`. -/
lemma fractionalIdealDivisor_surjective :
    Function.Surjective (fractionalIdealDivisor R K) := by
  intro D
  refine ⟨Additive.ofMul (Units.mk0 (D.prod fun v e => (v.asIdeal : FractionalIdeal R⁰ K) ^ e)
    (prod_asIdeal_zpow_ne_zero R K D)), ?_⟩
  ext v
  rw [coeff_fractionalIdealDivisor]
  simp only [toMul_ofMul, Units.val_mk0]
  rw [FractionalIdeal.count_finsuppProd]
  rfl

/-- **The Weil ≃ Cartier dictionary for the affine Dedekind chart.** The group of invertible
fractional ideals of a Dedekind domain `R` is isomorphic to the free Weil-divisor group on the
height-one primes of `R`, by taking `v`-adic multiplicities. The inverse sends a divisor `D` to the
fractional ideal `∏_v v^(D v)`. -/
noncomputable def fractionalIdealDivisorAddEquiv :
    Additive (FractionalIdeal R⁰ K)ˣ ≃+ WeilDivisor (HeightOneSpectrum R) :=
  AddEquiv.ofBijective (fractionalIdealDivisor R K)
    ⟨fractionalIdealDivisor_injective R K, fractionalIdealDivisor_surjective R K⟩

/-- On forward application the packaged equivalence `fractionalIdealDivisorAddEquiv` agrees with the
underlying homomorphism `fractionalIdealDivisor`. -/
@[simp]
lemma fractionalIdealDivisorAddEquiv_apply (I : Additive (FractionalIdeal R⁰ K)ˣ) :
    fractionalIdealDivisorAddEquiv R K I = fractionalIdealDivisor R K I := by
  -- `AddEquiv.ofBijective` stores the given homomorphism as its underlying map.  After the bump
  -- `rw [fractionalIdealDivisorAddEquiv, AddEquiv.ofBijective_apply]` no longer matches the
  -- coercion appearing here, so take the definitional step.
  rfl

/-- The inverse of `fractionalIdealDivisorAddEquiv` sends a Weil divisor `D` to the invertible
fractional ideal `∏_v v^(D v)`: the product of the prime ideals `v.asIdeal` raised to the
multiplicities `D v`. This gives the canonical formula for the inverse, which
`AddEquiv.ofBijective` otherwise leaves as an unspecified choice inverse. -/
@[simp]
lemma fractionalIdealDivisorAddEquiv_symm_apply (D : WeilDivisor (HeightOneSpectrum R)) :
    (fractionalIdealDivisorAddEquiv R K).symm D =
      Additive.ofMul (Units.mk0 (D.prod fun v e => (v.asIdeal : FractionalIdeal R⁰ K) ^ e)
        (prod_asIdeal_zpow_ne_zero R K D)) := by
  rw [AddEquiv.symm_apply_eq, fractionalIdealDivisorAddEquiv_apply]
  ext v
  rw [coeff_fractionalIdealDivisor]
  simp only [toMul_ofMul, Units.val_mk0]
  rw [FractionalIdeal.count_finsuppProd]
  rfl

variable {R K}

/-- The divisor of the principal fractional ideal `(x)` of a nonzero rational function `x` is the
principal divisor of `x`: the isomorphism carries principal fractional ideals to principal divisors.
This is the compatibility on principal elements needed to later identify the ideal class group with
the divisor class group `Cl(X)`; that quotient-level isomorphism is not proved here. -/
@[simp]
lemma fractionalIdealDivisor_toPrincipalIdeal (x : Kˣ) :
    fractionalIdealDivisor R K (Additive.ofMul (toPrincipalIdeal R K x)) =
      (OrderSystem.ofDedekindDomain R K).principalDivisor (Additive.ofMul x) := by
  ext v
  rw [coeff_fractionalIdealDivisor, coeff_principalDivisor_eq_fractionalIdeal_count]
  simp only [toMul_ofMul]

/-- Applying the isomorphism `fractionalIdealDivisorAddEquiv` to the principal fractional ideal
`(x)` of a nonzero rational function `x` yields the principal divisor of `x`, restating
`fractionalIdealDivisor_toPrincipalIdeal` for the packaged equivalence. -/
lemma fractionalIdealDivisorAddEquiv_toPrincipalIdeal (x : Kˣ) :
    fractionalIdealDivisorAddEquiv R K (Additive.ofMul (toPrincipalIdeal R K x)) =
      (OrderSystem.ofDedekindDomain R K).principalDivisor (Additive.ofMul x) :=
  fractionalIdealDivisor_toPrincipalIdeal x

/-- The divisor of a prime `v`, regarded as an invertible fractional ideal, is the point divisor
`[v]`. This is the non-vacuity check identifying the divisor map on generators. -/
@[simp]
lemma fractionalIdealDivisor_asIdeal (v : HeightOneSpectrum R) :
    fractionalIdealDivisor R K
        (Additive.ofMul (Units.mk0 (v.asIdeal : FractionalIdeal R⁰ K)
          (FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot))) = ofPoint v := by
  ext w
  rw [coeff_fractionalIdealDivisor]
  simp only [toMul_ofMul, Units.val_mk0]
  by_cases h : v = w
  · subst h
    rw [FractionalIdeal.count_self, coeff_ofPoint_self]
  · rw [FractionalIdeal.count_maximal_coprime K w h, coeff_ofPoint_of_ne (Ne.symm h)]

end WeilDivisor

end AlgebraicGeometry

end TauCeti
