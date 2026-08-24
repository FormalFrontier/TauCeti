/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Multiquadratic.Quadratic.RamifiedPrime.Product
public import TauCeti.NumberTheory.NumberField.Quadratic.Conjugation.Ambiguous.Narrow
import TauCeti.Algebra.Group.Subgroup.TwoTorsionClosure
import TauCeti.NumberTheory.NumberField.Quadratic.Conjugation.Ambiguous.Structure
import TauCeti.NumberTheory.NumberField.Quadratic.Conjugation.Hilbert90
import TauCeti.NumberTheory.NumberField.Quadratic.Conjugation.Norm
import TauCeti.NumberTheory.NumberField.Quadratic.Conjugation.Units

/-!
# The narrow relation between the ramified primes of a quadratic field

Let `K = ℚ(√d)` be a quadratic number field, presented by `θ : 𝓞 K` with
`minpoly ℤ θ = X ^ 2 - d` and `Algebra.adjoin ℚ {θ} = ⊤`, with `d` squarefree and `1 < |d|`, and
let `𝔭_p` be the prime of `𝓞 K` above a ramified rational prime `p`. The narrow classes `[𝔭_p]⁺`
are involutions in the narrow class group `Cl⁺(K)`, so a priori they span at most `2 ^ t` classes
with `t` the number of ramified primes. This file produces one **relation** between them, cutting
the bound to `2 ^ (t - 1)`:

`∃ S ≠ ∅, ∏_{p ∈ S} [𝔭_p]⁺ = 1`.

In the *ordinary* class group the relation is the single explicit identity `∏_{p ∣ d} [𝔭_p] = 1`,
coming from `(θ) = ∏_{p ∣ d} 𝔭_p` (`TauCeti.Multiquadratic.prod_classGroupMk0_eq_one`). Narrowly
that identity survives only when `(θ)` has a *totally positive* generator, and for a real quadratic
field it often does not: for `K = ℚ(√3)` the narrow class of `𝔭_3 = (√3)` is nontrivial, and the
relation is instead `[𝔭_2]⁺[𝔭_3]⁺ = 1`; for `K = ℚ(√7)` it is `[𝔭_2]⁺ = 1`, since `3 + √7` is
totally positive of norm `2`. There is no uniform choice of `S`, and the proof splits accordingly.

* If some unit `u` makes `θu` totally positive up to sign, `S` is the set of prime factors of `d`.
  This covers every imaginary quadratic field, where total positivity is vacuous, and every real
  quadratic field admitting a unit of norm `-1`.
* Otherwise every unit has norm `1`, so every unit is `±` a totally positive one; since a field with
  a real place has unit rank `1`, where the squares have index `2 ^ (rank + 1) = 4`
  (`NumberField.units_sq_index_eq`), some totally positive unit `ε` is not a square. Hilbert 90
  turns `ε` into `z ≠ 0` with `σz = εz`; the ideal `(z)` is then ambiguous, so it is a positive
  rational integer times a product of distinct ramified primes, and dividing out that rational
  factor leaves `∏_{p ∈ S} 𝔭_p = (γ)` with `γ/σγ = ε⁻¹` totally positive. Were `S` empty, `γ` would
  be a unit `v` with `σv = εv`, forcing `ε = (v⁻¹)²`, a square.

Both branches are archimedean where the ordinary theory is not: what replaces the ordinary
argument's use of total complexity is total positivity, exactly as in the narrow Hilbert-90 descent
of `TauCeti.NumberTheory.NumberField.Quadratic.Conjugation.Ambiguous.Narrow`.

The classical source is F. Lemmermeyer, *Reciprocity Laws: From Euler to Eisenstein*, §2.2, and
D. A. Cox, *Primes of the Form x² + ny²*, §6.A, where this is the "first inequality"
`#Cl⁺/(Cl⁺)² ≤ 2 ^ (t - 1)` of the ambiguous class number formula.

## Main results

In the namespace `TauCeti.Multiquadratic`:

* `exists_nonempty_prod_narrowMk0_eq_one_of_unit`: the Hilbert-90 construction of a relation
  from such a unit.
* `exists_nonempty_prod_narrowMk0_eq_one`: the relation, for a quadratic field of either signature.
* `natCard_closure_image_narrowMk0_le`: hence the narrow classes of the ramified primes generate a
  subgroup of order at most `2 ^ (t - 1)`.
-/

public section

open Polynomial NumberField
open scoped NumberField nonZeroDivisors

namespace TauCeti.Multiquadratic

variable {K : Type*} [Field K] [NumberField K] {θ : 𝓞 K} {d : ℤ}

/-! ### The relation -/

variable {Q : ℕ → (Ideal (𝓞 K))⁰}

/-- **A totally positive unit that is not a conjugation ratio produces a relation.** Let `ε` be a
totally positive unit of norm one such that `σv = εv` for no unit `v`. Hilbert 90 produces `z ≠ 0`
with `σz = εz`, so the ideal `(z)` is ambiguous; the structure theorem writes it as a positive
rational integer times a product `∏_{p ∈ S} 𝔭_p` of distinct ramified primes, and stripping the
rational factor leaves `∏_{p ∈ S} 𝔭_p = (γ)` with `γ/σγ = ε⁻¹` totally positive. Hence `γ` or `-γ`
is totally positive and the product has trivial *narrow* class. The set `S` is nonempty: were it
empty, `γ` would be a unit `v` with `σv = εv`. -/
theorem exists_nonempty_prod_narrowMk0_eq_one_of_unit
    (hmin : minpoly ℤ θ = X ^ 2 - C d) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    (hprime : ∀ p ∈ ramifiedPrimes K, (Q p : Ideal (𝓞 K)).IsPrime)
    (hover : ∀ p ∈ ramifiedPrimes K,
      (Q p : Ideal (𝓞 K)).LiesOver (Ideal.span {(p : ℤ)}))
    {ε : (𝓞 K)ˣ} (hpos : IsTotallyPositive ((ε : 𝓞 K) : K))
    (hne : ∀ v : (𝓞 K)ˣ,
      ringOfIntegersQuadraticConj hmin hgen (v : 𝓞 K) ≠ (ε : 𝓞 K) * (v : 𝓞 K)) :
    ∃ S : Finset ℕ, S.Nonempty ∧ ↑S ⊆ ramifiedPrimes K ∧
      ∏ p ∈ S, NarrowClassGroup.mk0 (Q p) = 1 := by
  classical
  set σ := ringOfIntegersQuadraticConj hmin hgen
  have hnorm : (ε : 𝓞 K) * σ (ε : 𝓞 K) = 1 := by
    rcases mul_ringOfIntegersQuadraticConj_unit_eq_one_or_neg_one hmin hgen ε with h | h
    · exact h
    · have hεK : (((ε : 𝓞 K) : K)) ≠ 0 :=
        RingOfIntegers.coe_ne_zero_iff.mpr ε.ne_zero
      have hnorm_pos := norm_pos_of_isTotallyPositive hεK hpos
      have hnorm_neg : Algebra.norm ℚ (((ε : 𝓞 K) : K)) = -1 := by
        apply (algebraMap ℚ K).injective
        rw [algebraMap_norm_eq_mul_ringOfIntegersQuadraticConj hmin hgen, h]
        simp
      rw [hnorm_neg] at hnorm_pos
      norm_num at hnorm_pos
  obtain ⟨z, hz0, hz⟩ :=
    exists_ne_zero_mul_eq_mul_ringOfIntegersQuadraticConj hmin hgen (x := (ε : 𝓞 K)) (y := 1)
      ε.ne_zero (by simpa using hnorm)
  rw [one_mul] at hz
  have hσz : σ z = (ε : 𝓞 K) * z := hz.symm
  have hspanz : Ideal.span ({z} : Set (𝓞 K)) ≠ 0 := by
    rw [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact hz0
  -- `(z)` is an ambiguous ideal, since `σz` and `z` differ by a unit.
  have hamb : Ideal.map σ (Ideal.span {z}) = Ideal.span {z} := by
    rw [Ideal.map_span, Set.image_singleton, hσz]
    refine Ideal.span_singleton_eq_span_singleton.mpr ⟨ε⁻¹, ?_⟩
    rw [mul_comm ((ε : 𝓞 K)) z, mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      mul_one]
  obtain ⟨m, hm0, S, hS, hzeq⟩ :=
    exists_eq_span_singleton_mul_prod_of_map_eq_self hmin hgen hprime hover hspanz hamb
  have hm0' : ((m : ℕ) : 𝓞 K) ≠ 0 := Nat.cast_ne_zero.mpr hm0.ne'
  have hspanm : Ideal.span ({(m : 𝓞 K)} : Set (𝓞 K)) ≠ 0 := by
    rw [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact hm0'
  -- Strip the rational factor: `z = γ m` and `∏_{p ∈ S} 𝔭_p = (γ)`.
  obtain ⟨γ, hγ⟩ : ∃ γ : 𝓞 K, γ * (m : 𝓞 K) = z := by
    have hzmem : z ∈ Ideal.span ({(m : 𝓞 K)} : Set (𝓞 K)) * ∏ p ∈ S, (Q p : Ideal (𝓞 K)) := by
      rw [← hzeq]
      exact Ideal.mem_span_singleton_self z
    exact Ideal.mem_span_singleton'.mp (Ideal.mul_le_left hzmem)
  have hγ0 : γ ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hγ
    exact hz0 hγ.symm
  have hprodeq : (∏ p ∈ S, (Q p : Ideal (𝓞 K))) = Ideal.span {γ} := by
    refine mul_left_cancel₀ hspanm ?_
    rw [← hzeq, Ideal.span_singleton_mul_span_singleton, ← hγ, mul_comm]
  have hσγ : σ γ = (ε : 𝓞 K) * γ := by
    have h := congrArg σ hγ
    rw [map_mul, map_natCast, hσz, ← hγ] at h
    refine mul_right_cancel₀ hm0' ?_
    rw [mul_assoc]
    exact h
  -- `γ / σγ = ε⁻¹` is totally positive, so `γ` or `-γ` is.
  have hσγK : quadraticConj hmin hgen (γ : K) = ((ε : 𝓞 K) : K) * (γ : K) := by
    rw [← coe_ringOfIntegersQuadraticConj hmin hgen γ, hσγ]
    push_cast
    ring
  have hγK : (γ : K) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr hγ0
  have hεK : ((ε : 𝓞 K) : K) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr ε.ne_zero
  have hposratio : IsTotallyPositive ((γ : K) / quadraticConj hmin hgen (γ : K)) := by
    rw [hσγK, div_mul_eq_div_div_swap, div_self hγK]
    simpa using hpos.inv
  have hcoe : ((∏ p ∈ S, Q p : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) = Ideal.span {γ} := by
    rw [Submonoid.coe_finsetProd]
    exact hprodeq
  have hone : ∏ p ∈ S, NarrowClassGroup.mk0 (Q p) = 1 := by
    rw [← map_prod]
    rcases isTotallyPositive_or_isTotallyPositive_neg_of_isTotallyPositive_div_quadraticConj
      hmin hgen hposratio with h | h
    · exact NarrowClassGroup.mk0_eq_one_of_isTotallyPositive hγ0 h hcoe
    · refine NarrowClassGroup.mk0_eq_one_of_isTotallyPositive (a := -γ) (neg_ne_zero.mpr hγ0)
        (by push_cast; exact h) ?_
      rw [Ideal.span_singleton_neg]
      exact hcoe
  refine ⟨S, ?_, hS, hone⟩
  rcases S.eq_empty_or_nonempty with rfl | hSne
  · rw [Finset.prod_empty, Ideal.one_eq_top, eq_comm, Ideal.span_singleton_eq_top] at hprodeq
    obtain ⟨v, rfl⟩ := hprodeq
    exact absurd hσγ (hne v)
  · exact hSne

/-- **An explicit relation of narrow genus theory.** For `K = ℚ(√d)` with `d` squarefree and
`1 < |d|`, some *nonempty* set `S` of ramified primes has `∏_{p ∈ S} [𝔭_p]⁺ = 1` in `Cl⁺(K)`.

Which set works depends on `K`. If some unit `u` makes `θu` totally positive up to sign — in
particular whenever `K` is imaginary, where the condition is vacuous, and whenever some unit has
norm `-1` — then `S` is the set of prime factors of `d`, because `(θ) = ∏_{p ∣ d} 𝔭_p`. Otherwise
`K` is real with every unit of norm one, and
`exists_nonempty_prod_narrowMk0_eq_one_of_unit` builds `S` by Hilbert 90 from a totally
positive unit that is not a square (`exists_isTotallyPositive_notMem_square`).

Unlike the ordinary relation `prod_classGroupMk0_eq_one`, which is the single identity
`∏_{p ∣ d} [𝔭_p] = 1`, no *uniform* choice of `S` is available: for `K = ℚ(√3)` the relation is
`[𝔭_2]⁺[𝔭_3]⁺ = 1` with `[𝔭_3]⁺ ≠ 1`, whereas for `K = ℚ(√7)` it is `[𝔭_2]⁺ = 1`. The hypothesis
`1 < |d|` excludes `d = -1`, where the radicand has no prime factor and the first branch would
produce the empty set. -/
theorem exists_nonempty_prod_narrowMk0_eq_one (hmin : minpoly ℤ θ = X ^ 2 - C d)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) (hsf : Squarefree d) (hd : 1 < d.natAbs)
    (hprime : ∀ p ∈ ramifiedPrimes K, (Q p : Ideal (𝓞 K)).IsPrime)
    (hover : ∀ p ∈ ramifiedPrimes K,
      (Q p : Ideal (𝓞 K)).LiesOver (Ideal.span {(p : ℤ)})) :
    ∃ S : Finset ℕ, S.Nonempty ∧ ↑S ⊆ ramifiedPrimes K ∧
      ∏ p ∈ S, NarrowClassGroup.mk0 (Q p) = 1 := by
  classical
  have hθK : ((θ : 𝓞 K) : K) ≠ 0 := coe_gen_ne_zero hmin
  have hθ0 : (θ : 𝓞 K) ≠ 0 := fun h0 => hθK (by rw [h0]; simp)
  by_cases hA : ∃ u : (𝓞 K)ˣ, IsTotallyPositive ((θ * (u : 𝓞 K) : 𝓞 K) : K) ∨
      IsTotallyPositive (-((θ * (u : 𝓞 K) : 𝓞 K) : K))
  · -- The product over the prime factors of `d` is `(θ)`, which is narrowly principal.
    obtain ⟨u, hu⟩ := hA
    have hsub : ↑d.natAbs.primeFactors ⊆ ramifiedPrimes K := fun p hp =>
      mem_ramifiedPrimes_of_mem_primeFactors hmin hgen hsf hp
    have hspan : ((∏ p ∈ d.natAbs.primeFactors, Q p : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) =
        Ideal.span {θ * (u : 𝓞 K)} := by
      rw [Submonoid.coe_finsetProd, ← span_singleton_eq_prod_primeFactors hmin hgen hsf _
        (fun p hp => hprime p (hsub hp)) fun p hp => hover p (hsub hp)]
      exact Ideal.span_singleton_eq_span_singleton.mpr ⟨u, rfl⟩
    have hθu0 : θ * (u : 𝓞 K) ≠ 0 := mul_ne_zero hθ0 u.ne_zero
    refine ⟨d.natAbs.primeFactors, Nat.nonempty_primeFactors.mpr hd, hsub, ?_⟩
    rw [← map_prod]
    rcases hu with h | h
    · exact NarrowClassGroup.mk0_eq_one_of_isTotallyPositive hθu0 h hspan
    · refine NarrowClassGroup.mk0_eq_one_of_isTotallyPositive (a := -(θ * (u : 𝓞 K)))
        (neg_ne_zero.mpr hθu0) (by push_cast; exact h) ?_
      rw [Ideal.span_singleton_neg]
      exact hspan
  · -- No such unit: `K` is real and every unit has norm one.
    have hcomplex : ¬ IsTotallyComplex K := by
      intro hTC
      exact hA ⟨1, Or.inl (isTotallyPositive_iff.mpr fun w hw =>
        absurd hw (InfinitePlace.not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex w)))⟩
    have hnormone : ∀ u : (𝓞 K)ˣ,
        (u : 𝓞 K) * ringOfIntegersQuadraticConj hmin hgen (u : 𝓞 K) = 1 := by
      intro u
      rcases mul_ringOfIntegersQuadraticConj_unit_eq_one_or_neg_one hmin hgen u with h | h
      · exact h
      · refine absurd ⟨u, ?_⟩ hA
        -- With `u σu = -1`, the ratio `θu / σ(θu)` is the square `u²`.
        have huK : ((u : 𝓞 K) : K) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr u.ne_zero
        have hu' : ((u : 𝓞 K) : K) * quadraticConj hmin hgen ((u : 𝓞 K) : K) = -1 := by
          simpa [coe_ringOfIntegersQuadraticConj] using congrArg (fun x : 𝓞 K => (x : K)) h
        have hcjK : quadraticConj hmin hgen ((θ * (u : 𝓞 K) : 𝓞 K) : K) =
            -(θ : K) * quadraticConj hmin hgen ((u : 𝓞 K) : K) := by
          push_cast
          rw [map_mul, quadraticConj_gen hmin hgen]
        have hcjne : quadraticConj hmin hgen ((u : 𝓞 K) : K) ≠ 0 := fun h0 => by
          rw [h0, mul_zero] at hu'
          exact zero_ne_one (neg_eq_zero.mp hu'.symm).symm
        have hdiv : ((θ * (u : 𝓞 K) : 𝓞 K) : K) /
            quadraticConj hmin hgen ((θ * (u : 𝓞 K) : 𝓞 K) : K) = ((u : 𝓞 K) : K) ^ 2 := by
          rw [hcjK, div_eq_iff (by simp [hθK, hcjne])]
          push_cast
          linear_combination ((θ : K) * ((u : 𝓞 K) : K)) * hu'
        exact isTotallyPositive_or_isTotallyPositive_neg_of_isTotallyPositive_div_quadraticConj
          hmin hgen (by rw [hdiv]; exact isTotallyPositive_sq huK)
    obtain ⟨ε, hεpos, hεsq⟩ := exists_isTotallyPositive_notMem_square hmin hgen hcomplex hnormone
    refine exists_nonempty_prod_narrowMk0_eq_one_of_unit hmin hgen hprime hover hεpos fun v hv =>
      hεsq ?_
    have hvv := hnormone v
    rw [hv] at hvv
    have hunit : ε * (v * v) = 1 := by
      refine Units.ext ?_
      simp only [Units.val_mul, Units.val_one]
      linear_combination hvv
    exact ⟨v⁻¹, by rw [← mul_inv]; exact eq_inv_of_mul_eq_one_left hunit⟩

/-- **The narrow classes of the ramified primes generate a subgroup of order at most
`2 ^ (t - 1)`.** Let `s` be the finite set of ramified primes of `K = ℚ(√d)`, with `Q p` the prime
of `𝓞 K` above `p`. Then the subgroup of `Cl⁺(K)` generated by their narrow classes has at most
`2 ^ (t - 1)` elements, where `t = #s`.

The classes are involutions (`NarrowClassGroup.mk0_sq_eq_one_of_mem_ramifiedPrimes`), so the
subgroup they generate is the set of sub-products; the relation
`exists_nonempty_prod_narrowMk0_eq_one` removes one generator. -/
theorem natCard_closure_image_narrowMk0_le (hmin : minpoly ℤ θ = X ^ 2 - C d)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) (hsf : Squarefree d) (hd : 1 < d.natAbs)
    {s : Finset ℕ} (hs : (↑s : Set ℕ) = ramifiedPrimes K)
    (hprime : ∀ p ∈ ramifiedPrimes K, (Q p : Ideal (𝓞 K)).IsPrime)
    (hover : ∀ p ∈ ramifiedPrimes K,
      (Q p : Ideal (𝓞 K)).LiesOver (Ideal.span {(p : ℤ)})) :
    Nat.card (Subgroup.closure ((fun p ↦ NarrowClassGroup.mk0 (Q p)) '' (↑s : Set ℕ))) ≤
      2 ^ (s.card - 1) := by
  classical
  obtain ⟨S, hSne, hSsub, hSrel⟩ :=
    exists_nonempty_prod_narrowMk0_eq_one hmin hgen hsf hd hprime hover
  refine natCard_closure_image_le_two_pow_card_sub_one s _ (fun p hp => ?_) (fun p hp => ?_)
    hSne hSrel
  · have hpram : p ∈ ramifiedPrimes K := by
      rw [← hs]
      exact Finset.mem_coe.mpr hp
    let _ := hprime p hpram
    let _ := hover p hpram
    exact NarrowClassGroup.mk0_sq_eq_one_of_mem_ramifiedPrimes
      (NumberField.finrank_rat_eq_two hmin hgen) hpram (Q p : Ideal (𝓞 K))
  · have hps : p ∈ (↑s : Set ℕ) := by
      rw [hs]
      exact hSsub (Finset.mem_coe.mpr hp)
    exact Finset.mem_coe.mp hps

end TauCeti.Multiquadratic
