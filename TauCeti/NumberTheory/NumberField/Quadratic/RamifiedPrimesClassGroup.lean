/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.NumberTheory.NumberField.Quadratic.TotalRamification
public import Mathlib.RingTheory.ClassGroup.Basic
public import Mathlib.Algebra.Algebra.Equiv

/-!
# Ramified primes: fixed by automorphisms, and 2-torsion in the class group

For a degree-two number field `K`, this file records two facts about the unique prime `𝔭` of `𝓞 K`
above a ramified rational prime `p`:

* any ring automorphism of `𝓞 K` **fixes** `𝔭` (`map_eq_self_of_mem_ramifiedPrimes`), since it
  permutes the primes over `(p)` and there is only one;
* the class `[𝔭]` in `Cl(𝓞 K)` is **2-torsion** (`classGroupMk0_sq_eq_one_of_mem_ramifiedPrimes`),
  because `𝔭² = p 𝓞 K` is principal.

Applied to quadratic conjugation `σ` the first says `𝔭` is an *ambiguous* ideal; together with the
fixed-class characterization `mulEquiv_ringOfIntegersQuadraticConj_apply_eq_self_iff`, the ramified
primes furnish *individual* explicit ambiguous 2-torsion classes. Determining all of `Cl(𝓞 K)[2]`
(the ambiguous-class-number / 2-rank theorem of genus theory, which for real fields carries a
unit-index correction relating these strongly ambiguous classes to the ambiguous ones) is left to
later work.

See D. A. Cox, *Primes of the Form x² + ny²*, and F. Lemmermeyer, *Reciprocity Laws*, for the
classical genus theory these results underlie.

## Main results

* `TauCeti.NumberField.map_eq_self_of_mem_ramifiedPrimes`: any ring automorphism of `𝓞 K` fixes the
  prime above a ramified `p`, in a degree-two field.
* `TauCeti.NumberField.classGroupMk0_sq_eq_one_of_mem_ramifiedPrimes`: the class of a ramified prime
  is 2-torsion.
-/

public section

open NumberField Ideal Module
open scoped NumberField

namespace TauCeti.NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- **A ring automorphism fixes a ramified prime.** In a degree-two number field, any ring
automorphism `σ` of `𝓞 K` fixes the unique prime `𝔭` above a ramified rational prime `p`: `σ 𝔭` is
again a prime of `𝓞 K` lying over `p` (its `ℤ`-algebra form `toIntAlgEquiv` has the same underlying
map, `RingEquiv.coe_toIntAlgEquiv`), and a ramified prime has only one prime above it. -/
theorem map_eq_self_of_mem_ramifiedPrimes (hK : finrank ℚ K = 2) (σ : 𝓞 K ≃+* 𝓞 K)
    {p : ℕ} (hmem : p ∈ ramifiedPrimes K) (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime]
    [𝔭.LiesOver (span {(p : ℤ)})] :
    Ideal.map σ 𝔭 = 𝔭 := by
  have hlo : (Ideal.map σ 𝔭).LiesOver (span {(p : ℤ)}) :=
    Ideal.LiesOver.of_eq_map_equiv (span {(p : ℤ)}) σ.toIntAlgEquiv rfl
  have hmemset : Ideal.map σ 𝔭 ∈ (span {(p : ℤ)} : Ideal ℤ).primesOver (𝓞 K) :=
    ⟨inferInstance, hlo⟩
  rwa [primesOver_eq_singleton_of_mem_ramifiedPrimes hK hmem 𝔭, Set.mem_singleton_iff] at hmemset

/-- **The class of a ramified prime is 2-torsion.** In a degree-two number field, the prime `𝔭`
above a ramified rational prime `p` satisfies `𝔭² = p 𝓞 K`, the extension of the principal ideal
`(p)`, so its class in `Cl(𝓞 K)` squares to `1`: `[𝔭]` is an explicit element of the 2-torsion
`Cl(𝓞 K)[2]`. -/
theorem classGroupMk0_sq_eq_one_of_mem_ramifiedPrimes (hK : finrank ℚ K = 2)
    {p : ℕ} (hmem : p ∈ ramifiedPrimes K) (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime]
    [𝔭.LiesOver (span {(p : ℤ)})] :
    ClassGroup.mk0 ⟨𝔭, by
      refine mem_nonZeroDivisors_of_ne_zero ?_
      rw [Ideal.zero_eq_bot]
      exact Ideal.ne_bot_of_liesOver_of_ne_bot (p := span {(p : ℤ)})
        (by rw [ne_eq, Ideal.span_singleton_eq_bot, Int.natCast_eq_zero]
            exact (prime_of_mem_ramifiedPrimes hmem).pos.ne') 𝔭⟩ ^ 2 = 1 := by
  have hnzd : 𝔭 ∈ nonZeroDivisors (Ideal (𝓞 K)) := by
    refine mem_nonZeroDivisors_of_ne_zero ?_
    rw [Ideal.zero_eq_bot]
    exact Ideal.ne_bot_of_liesOver_of_ne_bot (p := span {(p : ℤ)})
      (by rw [ne_eq, Ideal.span_singleton_eq_bot, Int.natCast_eq_zero]
          exact (prime_of_mem_ramifiedPrimes hmem).pos.ne') 𝔭
  have hsq : (⟨𝔭, hnzd⟩ : nonZeroDivisors (Ideal (𝓞 K))) ^ 2 = ⟨𝔭 ^ 2, pow_mem hnzd 2⟩ :=
    Subtype.ext (by rw [SubmonoidClass.coe_pow])
  -- `[𝔭]² = [𝔭²] = [p 𝓞 K] = 1`, as `𝔭² = p 𝓞 K` is the extension of the principal ideal `(p)`.
  rw [← map_pow, hsq, ClassGroup.mk0_eq_one_iff,
    ← map_span_eq_sq_of_mem_ramifiedPrimes hK hmem 𝔭, Ideal.map_span, Set.image_singleton]
  exact ⟨_, rfl⟩

end TauCeti.NumberField
