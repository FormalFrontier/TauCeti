/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.PrimeIdeal
public import TauCeti.NumberTheory.NumberField.NarrowClassGroup.Basic
public import TauCeti.NumberTheory.NumberField.Quadratic.TotalRamification
import Mathlib.NumberTheory.NumberField.ClassNumber

/-!
# The class of a ramified prime is 2-torsion

For a degree-two number field `K`, the unique prime `𝔭` of `𝓞 K` above a ramified rational prime `p`
satisfies `𝔭² = p 𝓞 K`, the extension of the principal ideal `(p)`, so its class `[𝔭]` in
`Cl(𝓞 K)` squares to `1`: it is an explicit element of the 2-torsion `Cl(𝓞 K)[2]`, the object
measured by `card_elementaryTwoQuotient_eq_card_twoTorsion`. The generator `p` of that principal
ideal is a *positive* rational integer, hence totally positive, so the same computation bounds the
order of `[𝔭]⁺` in the narrow class group `Cl⁺(K)`.

Any ring automorphism of `𝓞 K` fixes `𝔭` (`map_eq_self_of_mem_ramifiedPrimes`); applied to quadratic
conjugation this says `𝔭` is an *ambiguous* ideal, so the ramified primes furnish *individual*
explicit ambiguous 2-torsion classes. Determining all of `Cl(𝓞 K)[2]` (the ambiguous-class-number /
2-rank theorem of genus theory, which for real fields carries a unit-index correction relating these
strongly ambiguous classes to the ambiguous ones) is left to later work.

A ramified prime also *exhausts* the class group when the Minkowski bound is small enough: if that
bound is below `3` and `2` is ramified, then every ideal class is trivial or the class of the prime
above `2`, so `Cl(𝓞 K)` has at most two elements.

See D. A. Cox, *Primes of the Form x² + ny²*, and F. Lemmermeyer, *Reciprocity Laws*, for the
classical genus theory this result underlies.

## Main results

* `NumberField.classGroupMk0_sq_eq_one_of_mem_ramifiedPrimes`: the class of a ramified prime
  is 2-torsion.
* `NumberField.NarrowClassGroup.mk0_sq_eq_one_of_mem_ramifiedPrimes`: so is its narrow class.
* `TauCeti.NumberField.class_eq_one_or_eq_classGroupMk0_primeAboveTwo_of_minkowskiBound_lt_three`:
  with Minkowski bound below `3` and `2` ramified, every ideal class is trivial or the class of a
  prime above `2`.
-/

public section

open NumberField Ideal Module
open scoped NumberField nonZeroDivisors

namespace NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- **The class of a ramified prime is 2-torsion.** In a degree-two number field, the prime `𝔭`
above a ramified rational prime `p` satisfies `𝔭² = p 𝓞 K`, the extension of the principal ideal
`(p)`, so its class in `Cl(𝓞 K)` squares to `1`: `[𝔭]` is an explicit element of the 2-torsion
`Cl(𝓞 K)[2]`. -/
theorem classGroupMk0_sq_eq_one_of_mem_ramifiedPrimes (hK : finrank ℚ K = 2)
    {p : ℕ} (hmem : p ∈ ramifiedPrimes K) (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime]
    [𝔭.LiesOver (span {(p : ℤ)})] :
    ClassGroup.mk0 ⟨𝔭,
      mem_nonZeroDivisors_of_prime_of_liesOver (prime_of_mem_ramifiedPrimes hmem) 𝔭⟩ ^ 2 =
      1 := by
  have hnzd := mem_nonZeroDivisors_of_prime_of_liesOver
    (prime_of_mem_ramifiedPrimes hmem) 𝔭
  -- `[𝔭]² = [𝔭²] = [p 𝓞 K] = 1`, as `𝔭² = p 𝓞 K` is the extension of the principal ideal `(p)`.
  rw [← map_pow, SubmonoidClass.mk_pow 𝔭 hnzd 2, ClassGroup.mk0_eq_one_iff,
    ← map_span_eq_sq_of_mem_ramifiedPrimes hK hmem 𝔭, Ideal.map_span, Set.image_singleton]
  exact ⟨_, rfl⟩

/-- **The narrow class of a ramified prime is 2-torsion.** In a degree-two number field, the prime
`𝔭` above a ramified rational prime `p` satisfies `𝔭² = p 𝓞 K`, and the rational integer `p` is
positive, hence totally positive; so the narrow class of `𝔭` squares to `1` in `Cl⁺(K)`. -/
theorem NarrowClassGroup.mk0_sq_eq_one_of_mem_ramifiedPrimes (hK : finrank ℚ K = 2)
    {p : ℕ} (hmem : p ∈ ramifiedPrimes K) (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime]
    [𝔭.LiesOver (span {(p : ℤ)})] :
    NarrowClassGroup.mk0 ⟨𝔭,
      mem_nonZeroDivisors_of_prime_of_liesOver (prime_of_mem_ramifiedPrimes hmem) 𝔭⟩ ^ 2 =
      1 := by
  have hprime := prime_of_mem_ramifiedPrimes hmem
  have hnzd := mem_nonZeroDivisors_of_prime_of_liesOver hprime 𝔭
  have hp0 : (algebraMap ℤ (𝓞 K) (p : ℤ)) ≠ 0 := by
    simpa using fun h ↦ hprime.ne_zero (by exact_mod_cast h)
  -- `𝔭² = p 𝓞 K = (p)`, the principal ideal on the positive rational integer `p`. This is the
  -- underlying ideal of the nonzero-ideal wrapper `⟨𝔭 ^ 2, _⟩` that `mk0` is applied to; no
  -- rewrite can reach it inside that wrapper, since the membership proof depends on `𝔭 ^ 2`.
  have hspan : 𝔭 ^ 2 = span {algebraMap ℤ (𝓞 K) (p : ℤ)} := by
    rw [← map_span_eq_sq_of_mem_ramifiedPrimes hK hmem 𝔭, Ideal.map_span, Set.image_singleton]
  rw [← map_pow, SubmonoidClass.mk_pow 𝔭 hnzd 2]
  refine NarrowClassGroup.mk0_eq_one_of_isTotallyPositive hp0 ?_ hspan
  simpa using isTotallyPositive_intCast (K := K) (n := (p : ℤ)) (by exact_mod_cast hprime.pos)

end NumberField

namespace TauCeti.NumberField

open NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- With Minkowski bound below `3` and `2` ramified in a quadratic field, every ideal class is
trivial or the class of a prime `P` above `2`. -/
theorem class_eq_one_or_eq_classGroupMk0_primeAboveTwo_of_minkowskiBound_lt_three
    (hfin : finrank ℚ K = 2) (hram : 2 ∈ ramifiedPrimes K)
    (hM : (4 / Real.pi) ^ InfinitePlace.nrComplexPlaces K *
        ((finrank ℚ K).factorial / (finrank ℚ K) ^ (finrank ℚ K) *
          Real.sqrt |(NumberField.discr K : ℝ)|) < 3)
    (P : Ideal (𝓞 K)) [P.IsPrime] [P.LiesOver (span {(2 : ℤ)})]
    (C : ClassGroup (𝓞 K)) :
    C = 1 ∨ C = ClassGroup.mk0 ⟨P, mem_nonZeroDivisors_of_prime_of_liesOver Nat.prime_two P⟩ := by
  classical
  -- Minkowski gives a representative of norm at most `2`; norm `1` is principal and norm `2`
  -- must be the ramified prime.
  obtain ⟨I, hIC, hIle⟩ := NumberField.exists_ideal_in_class_of_norm_le C
  have hIlt : (I.1.absNorm : ℝ) < 3 := hIle.trans_lt hM
  have hIleTwo : I.1.absNorm ≤ 2 := by
    exact_mod_cast (Nat.lt_succ_iff.mp (by exact_mod_cast hIlt))
  have hIpos : 0 < I.1.absNorm := absNorm_pos_of_nonZeroDivisors I
  rcases (by omega : I.1.absNorm = 1 ∨ I.1.absNorm = 2) with hnorm | hnorm
  · left
    rw [← hIC]
    exact (ClassGroup.mk0_eq_one_iff I.2).mpr <| by
      rw [Ideal.absNorm_eq_one_iff.mp hnorm]
      exact top_isPrincipal
  · right
    rw [← hIC]
    have hIP : I.1 = P :=
      eq_of_absNorm_eq_of_mem_ramifiedPrimes hfin hram P I.1 hnorm
    apply congrArg ClassGroup.mk0
    exact Subtype.ext hIP

end TauCeti.NumberField
