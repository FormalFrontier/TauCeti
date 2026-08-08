/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.DedekindDomain.Different
public import Mathlib.NumberTheory.NumberField.Basic

/-!
# Unramified primes in a relative quadratic extension

For an extension of number fields `L / K` given by a generator `θ : 𝓞 L` with
`minpoly (𝓞 K) θ = X² - a` and `L = K(θ)`, a prime of `𝓞 K` coprime to `2 * a` is unramified in
`𝓞 L`. This is the relative analogue of the absolute odd-prime half of
`TauCeti.Multiquadratic.isUnramifiedIn_iff_not_dvd_fundamentalDiscriminant`.

The proof is the relative different at work: `θ` generates `L` over `K`, so the value of the
derivative of its minimal polynomial at `θ`, namely `2θ`, lies in the relative different
`𝔇(𝓞 L / 𝓞 K)` (`aeval_derivative_mem_differentIdeal`). A prime not containing `2θ` therefore does
not divide the different, so it is unramified (`not_dvd_differentIdeal_iff`); and a prime of `𝓞 K`
coprime to `2 * a` has no prime of `𝓞 L` above it containing `2θ`, since `(2θ)² = 4a`.

## Main results

* `TauCeti.NumberField.two_mul_gen_mem_differentIdeal`: `2θ ∈ 𝔇(𝓞 L / 𝓞 K)`.
* `TauCeti.NumberField.isUnramifiedIn_of_isCoprime`: a prime of `𝓞 K` coprime to `2 * a` is
  unramified in `𝓞 L`.
-/

public section

open Polynomial
open scoped NumberField

namespace TauCeti.NumberField

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
  {θ : 𝓞 L} {a : 𝓞 K}

omit [NumberField K] [NumberField L] in
/-- The derivative of `X² - a` evaluated at `θ` is `2θ`. -/
private theorem aeval_derivative_minpoly (hmin : minpoly (𝓞 K) θ = X ^ 2 - C a) :
    aeval θ (derivative (minpoly (𝓞 K) θ)) = 2 * θ := by
  rw [hmin, derivative_sub, derivative_X_pow, derivative_C, sub_zero, map_mul, aeval_C,
    map_pow, aeval_X, Nat.cast_ofNat, map_ofNat]
  norm_num

omit [NumberField K] [NumberField L] in
/-- The generator squares to its radicand: `θ² = a` in `𝓞 L`. -/
private theorem gen_sq (hmin : minpoly (𝓞 K) θ = X ^ 2 - C a) :
    θ ^ 2 = algebraMap (𝓞 K) (𝓞 L) a := by
  have h := minpoly.aeval (𝓞 K) θ
  rw [hmin] at h
  simp only [map_sub, map_pow, aeval_X, aeval_C] at h
  linear_combination h

/-- **`2θ` lies in the relative different.** For a relative quadratic generator `θ` of `L / K` with
`minpoly (𝓞 K) θ = X² - a`, the element `2θ` lies in `𝔇(𝓞 L / 𝓞 K)` — the value at `θ` of the
derivative of its minimal polynomial. -/
theorem two_mul_gen_mem_differentIdeal (hmin : minpoly (𝓞 K) θ = X ^ 2 - C a)
    (hgen : Algebra.adjoin K {(algebraMap (𝓞 L) L θ)} = ⊤) :
    2 * θ ∈ differentIdeal (𝓞 K) (𝓞 L) := by
  have := aeval_derivative_mem_differentIdeal (𝓞 K) K L θ hgen
  rwa [aeval_derivative_minpoly hmin] at this

/-- A prime `𝔓` of `𝓞 L` not containing `2θ` is unramified over `𝓞 K`: it cannot divide the
different, which contains `2θ`. -/
theorem isUnramifiedAt_of_two_mul_gen_not_mem (hmin : minpoly (𝓞 K) θ = X ^ 2 - C a)
    (hgen : Algebra.adjoin K {(algebraMap (𝓞 L) L θ)} = ⊤)
    {𝔓 : Ideal (𝓞 L)} [𝔓.IsPrime] (h : 2 * θ ∉ 𝔓) :
    Algebra.IsUnramifiedAt (𝓞 K) 𝔓 := by
  rw [← not_dvd_differentIdeal_iff]
  intro hdvd
  exact h (Ideal.dvd_iff_le.mp hdvd (two_mul_gen_mem_differentIdeal hmin hgen))

omit [NumberField K] [NumberField L] in
/-- If a prime `𝔓` of `𝓞 L` lying over `𝔭` contains `2θ`, then `2a ∈ 𝔭` (as `(2θ)² = 4a`). -/
private theorem two_mul_mem_of_two_mul_gen_mem (hmin : minpoly (𝓞 K) θ = X ^ 2 - C a)
    {𝔭 : Ideal (𝓞 K)} [𝔭.IsPrime] {𝔓 : Ideal (𝓞 L)} [𝔓.IsPrime] [𝔓.LiesOver 𝔭]
    (h : 2 * θ ∈ 𝔓) : 2 * a ∈ 𝔭 := by
  have hsq : (2 * θ) ^ 2 = algebraMap (𝓞 K) (𝓞 L) (4 * a) := by
    rw [mul_pow, gen_sq hmin, map_mul, map_ofNat]; ring
  have h4L : algebraMap (𝓞 K) (𝓞 L) (4 * a) ∈ 𝔓 := by
    rw [← hsq, pow_two]; exact Ideal.mul_mem_left 𝔓 _ h
  have h4 : 4 * a ∈ 𝔭 := by
    have hmem : (4 * a) ∈ 𝔓.under (𝓞 K) := h4L
    rwa [← Ideal.LiesOver.over (p := 𝔭) (P := 𝔓)] at hmem
  have h4' : (2 : 𝓞 K) * (2 * a) ∈ 𝔭 := by
    have he : (2 : 𝓞 K) * (2 * a) = 4 * a := by ring
    rw [he]; exact h4
  rcases (‹𝔭.IsPrime›).mem_or_mem h4' with h2 | h2a
  · exact 𝔭.mul_mem_right a h2
  · exact h2a

/-- **A prime coprime to `2a` is unramified in a relative quadratic extension.** For a generator `θ`
of `L / K` with `minpoly (𝓞 K) θ = X² - a`, any maximal ideal `𝔭` of `𝓞 K` coprime to `2 * a` is
unramified in `𝓞 L`. This is the relative analogue of the odd-prime half of
`TauCeti.Multiquadratic.isUnramifiedIn_iff_not_dvd_fundamentalDiscriminant`. -/
theorem isUnramifiedIn_of_isCoprime (hmin : minpoly (𝓞 K) θ = X ^ 2 - C a)
    (hgen : Algebra.adjoin K {(algebraMap (𝓞 L) L θ)} = ⊤)
    {𝔭 : Ideal (𝓞 K)} [𝔭.IsMaximal] (hcop : IsCoprime 𝔭 (Ideal.span {2 * a})) :
    Algebra.IsUnramifiedIn (𝓞 L) 𝔭 := by
  have h𝔭bot : 𝔭 ≠ ⊥ :=
    Ring.ne_bot_of_isMaximal_of_not_isField ‹_› (NumberField.RingOfIntegers.not_isField K)
  rw [Algebra.isUnramifiedIn_iff_forall_of_isDedekindDomain' h𝔭bot]
  intro 𝔓 h𝔓max h𝔓lo
  have : 𝔓.IsPrime := h𝔓max.isPrime
  have : 𝔓.LiesOver 𝔭 := h𝔓lo
  refine isUnramifiedAt_of_two_mul_gen_not_mem hmin hgen (fun hmem => ?_)
  have h2a : 2 * a ∈ 𝔭 := two_mul_mem_of_two_mul_gen_mem hmin hmem
  have hle : Ideal.span {2 * a} ≤ 𝔭 := Ideal.span_le.mpr (Set.singleton_subset_iff.mpr h2a)
  have htop : 𝔭 = ⊤ := by
    have hsup := Ideal.isCoprime_iff_sup_eq.mp hcop
    rwa [sup_eq_left.mpr hle] at hsup
  exact (‹𝔭.IsMaximal›).ne_top htop

end TauCeti.NumberField
