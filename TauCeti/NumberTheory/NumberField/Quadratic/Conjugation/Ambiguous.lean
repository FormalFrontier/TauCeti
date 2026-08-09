/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.NumberTheory.NumberField.Quadratic.Conjugation.ClassGroup
public import TauCeti.NumberTheory.NumberField.Quadratic.TotalRamification

/-!
# Ramified primes are ambiguous 2-torsion classes

For a quadratic field `K` (modelled by an integral generator `θ : 𝓞 K` with `minpoly ℤ θ = X² - d`
and `ℚ⟮θ⟯ = K`), write `σ = ringOfIntegersQuadraticConj` for quadratic conjugation. This file
records the arithmetic of `σ` at a ramified rational prime `p`:

* quadratic conjugation **fixes** the unique prime `𝔭` of `𝓞 K` above `p`, so `𝔭` is an
  *ambiguous* ideal (`σ 𝔭 = 𝔭`);
* being fixed by `σ` is **equivalent** to being 2-torsion, since `σ` acts on `Cl(𝓞 K)` by
  inversion (`mulEquiv_ringOfIntegersQuadraticConj_apply_eq_inv`);
* hence the class `[𝔭]` in `Cl(𝓞 K)` is **2-torsion**.

Together these exhibit the ramified primes as explicit ambiguous 2-torsion classes — the members of
`Cl(𝓞 K)[2]` (the object measured by `card_elementaryTwoQuotient_eq_card_twoTorsion`) that the
ambiguous-class-number / 2-rank theorem of genus theory counts. This is the lower-bound building
block of that theorem; the matching upper bound (that these generate all of `Cl(𝓞 K)[2]`, with a
single relation) is left to later work.

## Main results

* `TauCeti.NumberField.map_ringOfIntegersQuadraticConj_eq_self_of_mem_ramifiedPrimes`: `σ 𝔭 = 𝔭`
  for the prime `𝔭` above a ramified `p`.
* `TauCeti.NumberField.mulEquiv_ringOfIntegersQuadraticConj_apply_eq_self_iff`: a class is fixed by
  `σ` iff it is 2-torsion.
* `TauCeti.NumberField.classGroupMk0_sq_eq_one_of_mem_ramifiedPrimes`: the class of a ramified prime
  is 2-torsion.
-/

public section

open NumberField Polynomial Ideal Module
open scoped NumberField

namespace TauCeti.NumberField

variable {K : Type*} [Field K] [NumberField K] {θ : 𝓞 K} {d : ℤ}

/-- **Quadratic conjugation fixes a ramified prime.** For the unique prime `𝔭` of `𝓞 K` above a
ramified rational prime `p`, quadratic conjugation `σ` satisfies `σ 𝔭 = 𝔭`: the pushforward
`𝔭.map σ` is again a prime of `𝓞 K` lying over `p`, and a ramified prime of a quadratic field has
only one prime above it. In other words, `𝔭` is an *ambiguous* ideal. -/
theorem map_ringOfIntegersQuadraticConj_eq_self_of_mem_ramifiedPrimes
    (hmin : minpoly ℤ θ = X ^ 2 - C d) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    {p : ℕ} (hmem : p ∈ ramifiedPrimes K) (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime]
    [𝔭.LiesOver (span {(p : ℤ)})] :
    Ideal.map (ringOfIntegersQuadraticConj hmin hgen) 𝔭 = 𝔭 := by
  have hK : finrank ℚ K = 2 := finrank_rat_eq_two hmin hgen
  -- Push forward along `σ`'s canonical `ℤ`-algebra form `toIntAlgEquiv` (same underlying map, by
  -- `RingEquiv.coe_toIntAlgEquiv`): it is again a prime of `𝓞 K` over `(p)`, hence equals `𝔭`.
  have hmemset : Ideal.map (ringOfIntegersQuadraticConj hmin hgen).toIntAlgEquiv 𝔭 ∈
      (span {(p : ℤ)} : Ideal ℤ).primesOver (𝓞 K) := ⟨inferInstance, inferInstance⟩
  rw [primesOver_eq_singleton_of_mem_ramifiedPrimes hK hmem 𝔭, Set.mem_singleton_iff] at hmemset
  exact hmemset

/-- **A class is fixed by quadratic conjugation iff it is 2-torsion.** Because quadratic conjugation
acts on `Cl(𝓞 K)` by inversion, the classes it fixes are exactly those equal to their own inverse,
i.e. the 2-torsion. These are the *ambiguous* classes of genus theory. -/
theorem mulEquiv_ringOfIntegersQuadraticConj_apply_eq_self_iff
    (hmin : minpoly ℤ θ = X ^ 2 - C d) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    (C : ClassGroup (𝓞 K)) :
    ClassGroup.mulEquiv (ringOfIntegersQuadraticConj hmin hgen) C = C ↔ C ^ 2 = 1 := by
  rw [mulEquiv_ringOfIntegersQuadraticConj_apply_eq_inv hmin hgen, inv_eq_iff_mul_eq_one, ← pow_two]

/-- The prime above a ramified rational prime is a nonzero divisor of the ideal monoid: it lies over
the nonzero ideal `(p)`, so it is itself nonzero. -/
theorem mem_nonZeroDivisors_of_mem_ramifiedPrimes {p : ℕ} (hmem : p ∈ ramifiedPrimes K)
    (𝔭 : Ideal (𝓞 K)) [𝔭.LiesOver (span {(p : ℤ)})] : 𝔭 ∈ nonZeroDivisors (Ideal (𝓞 K)) := by
  apply mem_nonZeroDivisors_of_ne_zero
  rw [Ideal.zero_eq_bot]
  refine Ideal.ne_bot_of_liesOver_of_ne_bot (?_ : (span {(p : ℤ)} : Ideal ℤ) ≠ ⊥) 𝔭
  rw [ne_eq, Ideal.span_singleton_eq_bot]
  exact_mod_cast (prime_of_mem_ramifiedPrimes hmem).pos.ne'

/-- **The class of a ramified prime is 2-torsion.** The prime `𝔭` above a ramified rational prime
`p` is fixed by quadratic conjugation (it is ambiguous), and `σ` acts on `Cl(𝓞 K)` by inversion, so
the class `[𝔭]` equals its own inverse: `[𝔭]² = 1`. Concretely, `[𝔭]` is an explicit element of the
2-torsion `Cl(𝓞 K)[2]`. -/
theorem classGroupMk0_sq_eq_one_of_mem_ramifiedPrimes
    (hmin : minpoly ℤ θ = X ^ 2 - C d) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    {p : ℕ} (hmem : p ∈ ramifiedPrimes K) (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime]
    [𝔭.LiesOver (span {(p : ℤ)})] :
    ClassGroup.mk0 ⟨𝔭, mem_nonZeroDivisors_of_mem_ramifiedPrimes hmem 𝔭⟩ ^ 2 = 1 := by
  -- The class is 2-torsion because it is fixed by `σ` (ambiguity) and `σ` acts by inversion.
  rw [← mulEquiv_ringOfIntegersQuadraticConj_apply_eq_self_iff hmin hgen, ClassGroup.mulEquiv_mk0]
  exact congrArg (ClassGroup.mk0 ·)
    (Subtype.ext (map_ringOfIntegersQuadraticConj_eq_self_of_mem_ramifiedPrimes hmin hgen hmem 𝔭))

end TauCeti.NumberField
