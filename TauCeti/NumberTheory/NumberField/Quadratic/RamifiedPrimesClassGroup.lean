/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Quadratic.TotalRamification
public import Mathlib.RingTheory.ClassGroup.Basic

/-!
# The class of a ramified prime is 2-torsion

For a degree-two number field `K`, the unique prime `𝔭` of `𝓞 K` above a ramified rational prime `p`
satisfies `𝔭² = p 𝓞 K`, the extension of the principal ideal `(p)`, so its class `[𝔭]` in
`Cl(𝓞 K)` squares to `1`: it is an explicit element of the 2-torsion `Cl(𝓞 K)[2]`, the object
measured by `card_elementaryTwoQuotient_eq_card_twoTorsion`.

Any ring automorphism of `𝓞 K` fixes `𝔭` (`map_eq_self_of_mem_ramifiedPrimes`); applied to quadratic
conjugation this says `𝔭` is an *ambiguous* ideal, so the ramified primes furnish *individual*
explicit ambiguous 2-torsion classes. Determining all of `Cl(𝓞 K)[2]` (the ambiguous-class-number /
2-rank theorem of genus theory, which for real fields carries a unit-index correction relating these
strongly ambiguous classes to the ambiguous ones) is left to later work.

See D. A. Cox, *Primes of the Form x² + ny²*, and F. Lemmermeyer, *Reciprocity Laws*, for the
classical genus theory this result underlies.

## Main results

* `NumberField.exists_primeIdealFamily`: a finite set of rational primes admits a family of prime
  ideals above it, packaged for `ClassGroup.mk0`.
* `NumberField.classGroupMk0_sq_eq_one_of_mem_ramifiedPrimes`: the class of a ramified prime
  is 2-torsion.
-/

public section

open NumberField Ideal Module
open scoped NumberField nonZeroDivisors

namespace NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- An ideal lying over a rational prime is a non-zero-divisor in the ideal monoid, so it can be
passed to `ClassGroup.mk0`. -/
theorem ideal_mem_nonZeroDivisors_of_isPrime_liesOver {p : ℕ} (hp : p.Prime)
    (𝔭 : Ideal (𝓞 K)) [𝔭.LiesOver (span {(p : ℤ)})] :
    𝔭 ∈ nonZeroDivisors (Ideal (𝓞 K)) := by
  refine mem_nonZeroDivisors_of_ne_zero ?_
  rw [Ideal.zero_eq_bot]
  exact Ideal.ne_bot_of_liesOver_of_ne_bot (p := span {(p : ℤ)})
    (by rw [ne_eq, Ideal.span_singleton_eq_bot, Int.natCast_eq_zero]
        exact hp.pos.ne') 𝔭

/-- A finite set of rational primes admits a family of prime ideals above it, packaged as
non-zero-divisors so their classes can be taken with `ClassGroup.mk0`. Away from the specified
finite set the family is filled with the unit ideal. -/
theorem exists_primeIdealFamily (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    ∃ Q : (ℕ → (Ideal (𝓞 K))⁰),
      (∀ p ∈ s, (Q p : Ideal (𝓞 K)).IsPrime) ∧
        ∀ p ∈ s, (Q p : Ideal (𝓞 K)).LiesOver (span {(p : ℤ)}) := by
  classical
  have hex : ∀ p, p ∈ s → ∃ Q : (Ideal (𝓞 K))⁰,
      (Q : Ideal (𝓞 K)).IsPrime ∧ (Q : Ideal (𝓞 K)).LiesOver (span {(p : ℤ)}) := by
    intro p hp
    let _ : Fact p.Prime := ⟨hs p hp⟩
    obtain ⟨𝔭, hprime, hover⟩ :=
      (inferInstance : Nonempty ((span {(p : ℤ)} : Ideal ℤ).primesOver (𝓞 K)))
    let _ := hprime
    let _ := hover
    exact ⟨⟨𝔭, ideal_mem_nonZeroDivisors_of_isPrime_liesOver (hs p hp) 𝔭⟩,
      hprime, hover⟩
  choose Q hprime hover using hex
  let Q' : ℕ → (Ideal (𝓞 K))⁰ := fun p ↦ if hp : p ∈ s then Q p hp else 1
  refine ⟨Q', ?_, ?_⟩
  · intro p hp
    simpa [Q', hp] using hprime p hp
  · intro p hp
    simpa [Q', hp] using hover p hp

/-- **The class of a ramified prime is 2-torsion.** In a degree-two number field, the prime `𝔭`
above a ramified rational prime `p` satisfies `𝔭² = p 𝓞 K`, the extension of the principal ideal
`(p)`, so its class in `Cl(𝓞 K)` squares to `1`: `[𝔭]` is an explicit element of the 2-torsion
`Cl(𝓞 K)[2]`. -/
theorem classGroupMk0_sq_eq_one_of_mem_ramifiedPrimes (hK : finrank ℚ K = 2)
    {p : ℕ} (hmem : p ∈ ramifiedPrimes K) (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime]
    [𝔭.LiesOver (span {(p : ℤ)})] :
    ClassGroup.mk0 ⟨𝔭,
      ideal_mem_nonZeroDivisors_of_isPrime_liesOver (prime_of_mem_ramifiedPrimes hmem) 𝔭⟩ ^ 2 =
      1 := by
  have hnzd := ideal_mem_nonZeroDivisors_of_isPrime_liesOver
    (prime_of_mem_ramifiedPrimes hmem) 𝔭
  -- `[𝔭]² = [𝔭²] = [p 𝓞 K] = 1`, as `𝔭² = p 𝓞 K` is the extension of the principal ideal `(p)`.
  rw [← map_pow, SubmonoidClass.mk_pow 𝔭 hnzd 2, ClassGroup.mk0_eq_one_iff,
    ← map_span_eq_sq_of_mem_ramifiedPrimes hK hmem 𝔭, Ideal.map_span, Set.image_singleton]
  exact ⟨_, rfl⟩

end NumberField
