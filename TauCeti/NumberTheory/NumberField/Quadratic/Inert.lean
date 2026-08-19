/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.RamifiedPrimes
public import Mathlib.NumberTheory.RamificationInertia.Galois

/-!
# A conjugation-stable prime over an unramified rational prime is inert

Let `K` be a number field of degree `2` over `ℚ`. Such a field is Galois by Mathlib's
`Algebra.IsQuadraticExtension.isGalois` instance, and its Galois group has order `2`.
Consequently the two elements of that group act on the primes of `𝓞 K` above a rational prime `p`
transitively, and a prime `𝔭` above `p` fixed by the nontrivial automorphism is the *only* prime
above `p`.

Adding that `p` is unramified turns that into

`p 𝓞 K = 𝔭`,

so `p` is inert and `𝔭` is principal. Together with the ramified case
(`TauCeti.NumberTheory.NumberField.Quadratic.TotalRamification`, where `p 𝓞 K = 𝔭 ^ 2`) this
disposes of every prime that quadratic conjugation fixes: it is either principal, or one of the
finitely many primes above a ramified rational prime. That dichotomy is what makes the classes of
the ramified primes generate the ambiguous ideal classes of `K` in
`TauCeti.NumberTheory.NumberField.Quadratic.Conjugation.Ambiguous.Ideal`, the descent step of the
ambiguous class number formula of genus theory.

The automorphism is supplied as a `ℚ`-algebra automorphism `f` of `K` together with a ring
automorphism `σ` of `𝓞 K` restricting it; that is the shape in which
`NumberField.ringOfIntegersQuadraticConj` and `NumberField.coe_ringOfIntegersQuadraticConj` present
quadratic conjugation.

See D. A. Cox, *Primes of the Form x² + ny²*, and F. Lemmermeyer, *Reciprocity Laws*, Chapter 6, for
the classical genus theory in which this dichotomy is used.

## Main results

* `NumberField.primesOver_eq_singleton_of_map_eq_self`: a prime fixed by the nontrivial
  automorphism is the unique prime above the rational prime it lies over.
* `NumberField.map_span_eq_of_notMem_ramifiedPrimes`: if that rational prime is moreover
  unramified, then `p 𝓞 K = 𝔭`.
* `NumberField.isPrincipal_of_notMem_ramifiedPrimes`: hence `𝔭` is principal.
-/

public section

open Ideal Module
open scoped NumberField Pointwise

namespace NumberField

variable {K : Type*} [Field K] [NumberField K] {p : ℕ}

/-- The pointwise action of a `ℚ`-algebra automorphism of `K` on the ideals of `𝓞 K` is the
pushforward along any ring automorphism of `𝓞 K` restricting it. -/
private theorem smul_ideal_eq_map {f : K ≃ₐ[ℚ] K} {σ : 𝓞 K ≃+* 𝓞 K}
    (hσ : ∀ x : 𝓞 K, (σ x : K) = f x) (I : Ideal (𝓞 K)) :
    f • I = Ideal.map σ I := by
  have hhom : MulSemiringAction.toRingHom (K ≃ₐ[ℚ] K) (𝓞 K) f = (σ : 𝓞 K →+* 𝓞 K) := by
    refine RingHom.ext fun x ↦ RingOfIntegers.coe_injective ?_
    rw [RingHom.coe_coe]
    exact (hσ x).symm
  rw [Ideal.pointwise_smul_def, hhom, Ideal.map_coe]

/-- An ideal of `𝓞 K` fixed by the nontrivial automorphism of a quadratic number field is fixed by
every automorphism: the stabilizer is a nontrivial subgroup of a group of prime order. -/
private theorem smul_eq_self_of_map_eq_self (hK : finrank ℚ K = 2) {f : K ≃ₐ[ℚ] K} (hf : f ≠ 1)
    {σ : 𝓞 K ≃+* 𝓞 K} (hσ : ∀ x : 𝓞 K, (σ x : K) = f x) {I : Ideal (𝓞 K)}
    (hfix : Ideal.map σ I = I) (τ : K ≃ₐ[ℚ] K) : τ • I = I := by
  let _ : Algebra.IsQuadraticExtension ℚ K := ⟨hK⟩
  have hcard : Nat.card (K ≃ₐ[ℚ] K) = 2 := by
    rw [IsGalois.card_aut_eq_finrank, hK]
  have hsq : f ^ 2 = 1 := by rw [← hcard]; exact pow_card_eq_one'
  have hle : Subgroup.zpowers f ≤ MulAction.stabilizer (K ≃ₐ[ℚ] K) I := by
    rw [Subgroup.zpowers_le]
    exact (smul_ideal_eq_map hσ I).trans hfix
  have htop : Subgroup.zpowers f = ⊤ :=
    Subgroup.eq_top_of_card_eq _ (by rw [Nat.card_zpowers, orderOf_eq_prime hsq hf, hcard])
  exact hle (htop ▸ Subgroup.mem_top τ)

/-- **A conjugation-stable prime is the unique prime above its rational prime.** In a quadratic
number field the Galois group has order two, so it acts transitively on the primes above a rational
prime `p` through the single nontrivial automorphism `f`. A prime `𝔭` above `p` that `f` fixes is
therefore the whole of that orbit. -/
theorem primesOver_eq_singleton_of_map_eq_self (hK : finrank ℚ K = 2) (hp : p.Prime)
    {f : K ≃ₐ[ℚ] K} (hf : f ≠ 1) {σ : 𝓞 K ≃+* 𝓞 K} (hσ : ∀ x : 𝓞 K, (σ x : K) = f x)
    (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] [𝔭.LiesOver (span {(p : ℤ)})] (hfix : Ideal.map σ 𝔭 = 𝔭) :
    (span {(p : ℤ)} : Ideal ℤ).primesOver (𝓞 K) = {𝔭} := by
  let _ : Algebra.IsQuadraticExtension ℚ K := ⟨hK⟩
  have := Fact.mk hp
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨‹_›, ‹_›⟩, ?_⟩
  rintro 𝔮 ⟨h1, h2⟩
  obtain ⟨τ, hτ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup (span {(p : ℤ)}) 𝔭 𝔮 (K ≃ₐ[ℚ] K)
  rw [← hτ, smul_eq_self_of_map_eq_self hK hf hσ hfix]

/-- **A conjugation-stable prime over an unramified rational prime is inert.** If `p` does not
ramify in the quadratic number field `K` and the prime `𝔭` above it is fixed by the nontrivial
automorphism, then `p 𝓞 K = 𝔭`: the ideal generated by `p` is already prime. -/
theorem map_span_eq_of_notMem_ramifiedPrimes (hK : finrank ℚ K = 2) (hp : p.Prime)
    (hmem : p ∉ ramifiedPrimes K) {f : K ≃ₐ[ℚ] K} (hf : f ≠ 1) {σ : 𝓞 K ≃+* 𝓞 K}
    (hσ : ∀ x : 𝓞 K, (σ x : K) = f x) (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime]
    [𝔭.LiesOver (span {(p : ℤ)})] (hfix : Ideal.map σ 𝔭 = 𝔭) :
    (span {(p : ℤ)} : Ideal ℤ).map (algebraMap ℤ (𝓞 K)) = 𝔭 := by
  have := Fact.mk hp
  have hunr : Algebra.IsUnramifiedIn (𝓞 K) (span {(p : ℤ)}) := by
    by_contra h
    exact hmem (mem_ramifiedPrimes_iff.mpr ⟨hp, h⟩)
  have he : 𝔭.ramificationIdx ℤ = 1 :=
    Algebra.IsUnramifiedIn.ramificationIdx_eq_one (R := ℤ) hunr ‹_›
  rw [Ideal.map_algebraMap_eq_finsetProd_pow (by simp [hp.ne_zero]),
    Set.toFinset_congr (primesOver_eq_singleton_of_map_eq_self hK hp hf hσ 𝔭 hfix)]
  simp [he]

/-- **A conjugation-stable prime over an unramified rational prime is principal.** It is generated
by that rational prime, by `map_span_eq_of_notMem_ramifiedPrimes`. -/
theorem isPrincipal_of_notMem_ramifiedPrimes (hK : finrank ℚ K = 2) (hp : p.Prime)
    (hmem : p ∉ ramifiedPrimes K) {f : K ≃ₐ[ℚ] K} (hf : f ≠ 1) {σ : 𝓞 K ≃+* 𝓞 K}
    (hσ : ∀ x : 𝓞 K, (σ x : K) = f x) (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime]
    [𝔭.LiesOver (span {(p : ℤ)})] (hfix : Ideal.map σ 𝔭 = 𝔭) :
    Submodule.IsPrincipal 𝔭 :=
  ⟨algebraMap ℤ (𝓞 K) (p : ℤ), by
    rw [← map_span_eq_of_notMem_ramifiedPrimes hK hp hmem hf hσ 𝔭 hfix, Ideal.map_span,
      Set.image_singleton, submodule_span_eq]⟩

end NumberField
