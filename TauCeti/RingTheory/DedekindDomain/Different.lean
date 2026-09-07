/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DedekindDomain.Different
public import TauCeti.RingTheory.Trace.QuotientPow

/-!
# Dedekind's different theorem in the tame case

Let `B` be a Dedekind domain, module-finite over a Dedekind domain `A` with `Frac B / Frac A`
separable, let `p` be a maximal ideal of `A` and `P` a maximal ideal of `B` over it with
ramification index `e = e(P ∣ p)`.  Mathlib's `pow_sub_one_dvd_differentIdeal` gives the universal
half of Dedekind's different theorem, `P ^ (e - 1) ∣ 𝔡(B/A)`.  This file supplies the matching
non-divisibility that pins the exact value in the tame case: when the residue extension
`(B ⧸ P) / (A ⧸ p)` is separable and the residue characteristic does not divide `e`, the divisor
`P ^ e` does *not* divide the different, so the different exponent at `P` is exactly `e - 1`.

The criterion used is Mathlib's `not_dvd_differentIdeal_of_intTrace_not_mem`: to see that an ideal
`I` with `I * Q = p · B` does not divide `𝔡(B/A)` it is enough to produce `x ∈ Q` whose integral
trace is a unit mod `p`.  Taking `I = P ^ e` and `Q` the prime-to-`P` part of `p · B`, the Chinese
remainder theorem turns that into the requirement that the trace form of the `A ⧸ p`-algebra
`B ⧸ P ^ e` be nonzero, and `Algebra.trace_quotient_pow_mk` evaluates it: the trace of a residue is
`e` times its trace in `B ⧸ P`.  Separability of the residue extension makes the latter trace
nonzero somewhere, and tameness keeps the factor `e` from killing it.  Both hypotheses are needed:
in the wild case `e` is zero in `A ⧸ p` and the trace of `B ⧸ P ^ e` vanishes identically, and
without residue separability the different is divisible by `P` even when `e = 1`
(`dvd_differentIdeal_of_not_isSeparable`).

## Main results

* `TauCeti.not_pow_dvd_differentIdeal_of_isCoprime_of_isSeparable`: the criterion in the form that
  names a complement `Q` of `P ^ e` in `p · B`.
* `TauCeti.not_pow_ramificationIdx_dvd_differentIdeal`: **Dedekind's different theorem, tame
  half** — for a tame `P` with separable residue extension, `P ^ e(P ∣ p) ∤ 𝔡(B/A)`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Theorem 3.5.1(b).
-/

public section

open Module

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

namespace TauCeti

variable (A : Type*) {B : Type*} [CommRing A] [CommRing B] [Algebra A B]
variable [IsDedekindDomain A] [IsDedekindDomain B] [Module.IsTorsionFree A B] [Module.Finite A B]

attribute [local instance] Ideal.Quotient.field

/-- **A tame prime power does not divide the different ideal.** If `p · B = P ^ e * Q` with
`P ^ e` and `Q` coprime, the residue extension at `P` is separable, and `e` is invertible in the
residue field `A ⧸ p`, then `P ^ e` does not divide `differentIdeal A B`.

Together with Mathlib's `pow_sub_one_dvd_differentIdeal` this pins the different exponent at `P`
to `e - 1`.  Tameness enters only through `he`, and it is essential: in the wild case the trace
form of `B ⧸ P ^ e` over `A ⧸ p` is identically zero. -/
theorem not_pow_dvd_differentIdeal_of_isCoprime_of_isSeparable
    [Algebra.IsSeparable (FractionRing A) (FractionRing B)]
    {p : Ideal A} [p.IsMaximal] (P Q : Ideal B) [P.IsMaximal] [P.LiesOver p] {e : ℕ}
    [Algebra.IsSeparable (A ⧸ p) (B ⧸ P)]
    (hPQ : IsCoprime (P ^ e) Q) (hmul : P ^ e * Q = Ideal.map (algebraMap A B) p)
    (he : (e : A ⧸ p) ≠ 0) :
    ¬ P ^ e ∣ differentIdeal A B := by
  have hene : e ≠ 0 := by rintro rfl; simp at he
  rcases eq_or_ne P ⊥ with rfl | hPbot
  · intro hdvd
    rw [← Ideal.zero_eq_bot, zero_pow hene] at hdvd
    exact differentIdeal_ne_bot ((zero_dvd_iff.mp hdvd).trans Ideal.zero_eq_bot)
  have hQle : p ≤ Ideal.comap (algebraMap A B) Q := by
    rw [← Ideal.map_le_iff_le_comap, ← hmul]; exact Ideal.mul_le_right
  have hPle : p ≤ Ideal.comap (algebraMap A B) (P ^ e) := by
    rw [← Ideal.map_le_iff_le_comap, ← hmul]; exact Ideal.mul_le_left
  let instQ : Algebra (A ⧸ p) (B ⧸ Q) := Ideal.Quotient.algebraQuotientOfLEComap hQle
  have : IsScalarTower A (A ⧸ p) (B ⧸ Q) := .of_algebraMap_eq' rfl
  let instPe : Algebra (A ⧸ p) (B ⧸ P ^ e) := Ideal.Quotient.algebraQuotientOfLEComap hPle
  have : IsScalarTower A (A ⧸ p) (B ⧸ P ^ e) := .of_algebraMap_eq' rfl
  have hfQ : Module.Finite (A ⧸ p) (B ⧸ Q) := .of_restrictScalars_finite A _ _
  have hfP : Module.Finite (A ⧸ p) (B ⧸ P ^ e) := .of_restrictScalars_finite A _ _
  have hfP1 : Module.Finite (A ⧸ p) (B ⧸ P) := .of_restrictScalars_finite A _ _
  -- a residue with nonzero trace; its lift to `B ⧸ P ^ e` has trace `e` times as large
  obtain ⟨w, hw⟩ : ∃ w, Algebra.trace (A ⧸ p) (B ⧸ P) w ≠ 0 := by
    simpa [LinearMap.ext_iff] using Algebra.trace_ne_zero (A ⧸ p) (B ⧸ P)
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective w
  have hx : Algebra.trace (A ⧸ p) (B ⧸ P ^ e) (Ideal.Quotient.mk _ z) ≠ 0 := by
    rw [Algebra.trace_quotient_pow_mk hPbot e z, nsmul_eq_mul]
    exact mul_ne_zero he hw
  -- the Chinese remainder decomposition of `B ⧸ pB`
  let ee : (B ⧸ Ideal.map (algebraMap A B) p) ≃ₐ[A ⧸ p] ((B ⧸ P ^ e) × B ⧸ Q) :=
    { __ := (Ideal.quotEquivOfEq hmul.symm).trans
        (Ideal.quotientMulEquivQuotientProd (P ^ e) Q hPQ)
      commutes' := Quotient.ind fun _ ↦ rfl }
  have ee_snd_mk (b : B) :
      (ee (Ideal.Quotient.mk (Ideal.map (algebraMap A B) p) b)).2 =
        Ideal.Quotient.mk Q b := by
    simp [ee]
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (ee.symm (Ideal.Quotient.mk _ z, 0))
  refine not_dvd_differentIdeal_of_intTrace_not_mem A (P ^ e) Q hmul y ?_ ?_
  · rw [← Ideal.Quotient.eq_zero_iff_mem, ← ee_snd_mk]
    simpa using congrArg (fun x ↦ (ee x).2) hy
  · rw [← Ideal.Quotient.eq_zero_iff_mem, ← Algebra.trace_quotient_eq_of_isDedekindDomain,
      hy, Algebra.trace_eq_of_algEquiv, Algebra.trace_prod_apply]
    simpa using hx

/-- **Dedekind's different theorem, the tame half** (Stichtenoth, Theorem 3.5.1(b)): at a prime
`P` whose residue extension is separable and whose ramification index is invertible in the residue
field of `p`, the different ideal is divisible by `P ^ (e - 1)` — Mathlib's
`pow_sub_one_dvd_differentIdeal` — but not by `P ^ e`.

The complement `Q` of `P ^ e` in `p · B` is produced by `Ideal.eq_prime_pow_mul_coprime`, whose
exponent is the ramification index by
`Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count`. -/
theorem not_pow_ramificationIdx_dvd_differentIdeal
    [Algebra.IsSeparable (FractionRing A) (FractionRing B)]
    {p : Ideal A} [p.IsMaximal] (hp : p ≠ ⊥) (P : Ideal B) [P.IsMaximal] [P.LiesOver p]
    [Algebra.IsSeparable (A ⧸ p) (B ⧸ P)]
    (he : ((P.ramificationIdx A : ℕ) : A ⧸ p) ≠ 0) :
    ¬ P ^ P.ramificationIdx A ∣ differentIdeal A B := by
  have hp' : Ideal.map (algebraMap A B) p ≠ ⊥ :=
    (Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective A B)).not.mpr hp
  obtain ⟨Q, h₁, h₂⟩ := Ideal.eq_prime_pow_mul_coprime hp' P
  rw [← Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count p P hp'] at h₂
  exact not_pow_dvd_differentIdeal_of_isCoprime_of_isSeparable A P Q
    (Ideal.isCoprime_iff_sup_eq.mpr h₁).pow_left h₂.symm he

end TauCeti
