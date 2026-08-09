/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.NumberTheory.NumberField.Quadratic.Conjugation.ClassGroup
public import TauCeti.NumberTheory.NumberField.Quadratic.TotalRamification

/-!
# Quadratic conjugation fixes ramified primes; ambiguous classes are 2-torsion

For a quadratic field `K`, write `σ = ringOfIntegersQuadraticConj` for quadratic conjugation
(defined from an integral generator `θ : 𝓞 K` with `minpoly ℤ θ = X² - d` and `ℚ⟮θ⟯ = K`). This
file records two facts about `σ` at a ramified rational prime `p`:

* quadratic conjugation **fixes** the unique prime `𝔭` of `𝓞 K` above `p` (`σ 𝔭 = 𝔭`), so `𝔭` is
  an *ambiguous* ideal;
* being fixed by `σ` is **equivalent** to being 2-torsion, since `σ` acts on `Cl(𝓞 K)` by inversion
  (`mulEquiv_ringOfIntegersQuadraticConj_apply_eq_inv`); these are the *ambiguous* classes.

Since `𝔭 · σ𝔭 = 𝔭²` is principal (`𝔭² = p 𝓞 K`), the class of a ramified prime is then a 2-torsion
member of `Cl(𝓞 K)[2]` — the object measured by `card_elementaryTwoQuotient_eq_card_twoTorsion`.
Together these are the lower-bound building block of the ambiguous-class-number / 2-rank theorem of
genus theory; the matching upper bound (that such classes exhaust `Cl(𝓞 K)[2]`, with a single
relation) is left to later work.

See D. A. Cox, *Primes of the Form x² + ny²*, and F. Lemmermeyer, *Reciprocity Laws*, for the
classical genus theory these results underlie.

## Main results

* `TauCeti.NumberField.map_ringOfIntegersQuadraticConj_eq_self_of_mem_ramifiedPrimes`: `σ 𝔭 = 𝔭`
  for the prime `𝔭` above a ramified `p`.
* `TauCeti.NumberField.mulEquiv_ringOfIntegersQuadraticConj_apply_eq_self_iff`: a class is fixed by
  `σ` iff it is 2-torsion.
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
  -- `𝔭.map σ` lies over `(p)`: `σ`'s `ℤ`-algebra form `toIntAlgEquiv` has the same underlying map
  -- (`RingEquiv.coe_toIntAlgEquiv`) and carries `𝔭` to a prime over `(p)`.
  have hlo : (Ideal.map (ringOfIntegersQuadraticConj hmin hgen) 𝔭).LiesOver (span {(p : ℤ)}) :=
    Ideal.LiesOver.of_eq_map_equiv (span {(p : ℤ)})
      (ringOfIntegersQuadraticConj hmin hgen).toIntAlgEquiv rfl
  have hmemset : Ideal.map (ringOfIntegersQuadraticConj hmin hgen) 𝔭 ∈
      (span {(p : ℤ)} : Ideal ℤ).primesOver (𝓞 K) := ⟨inferInstance, hlo⟩
  rwa [primesOver_eq_singleton_of_mem_ramifiedPrimes hK hmem 𝔭, Set.mem_singleton_iff] at hmemset

/-- **A class is fixed by quadratic conjugation iff it is 2-torsion.** Because quadratic conjugation
acts on `Cl(𝓞 K)` by inversion, the classes it fixes are exactly those equal to their own inverse,
i.e. the 2-torsion. These are the *ambiguous* classes of genus theory. -/
theorem mulEquiv_ringOfIntegersQuadraticConj_apply_eq_self_iff
    (hmin : minpoly ℤ θ = X ^ 2 - C d) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    (C : ClassGroup (𝓞 K)) :
    ClassGroup.mulEquiv (ringOfIntegersQuadraticConj hmin hgen) C = C ↔ C ^ 2 = 1 := by
  rw [mulEquiv_ringOfIntegersQuadraticConj_apply_eq_inv hmin hgen, inv_eq_iff_mul_eq_one, ← pow_two]

end TauCeti.NumberField
