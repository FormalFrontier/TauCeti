/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.BigOperators.Associated
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Tactic

/-!
# Conjugate-transversal ideal families in a Dedekind domain

Let `σ` be a ring automorphism of a Dedekind domain `R` and `S` a finite set of nonzero prime
ideals, packaged as `IsDedekindDomain.HeightOneSpectrum R`, on which `σ` acts as a
fixed-point-free involution. Pairing each prime with its conjugate `σ p ≠ p`, the product of
one prime from each pair gives many ideals `A`, each satisfying
`A * σ A = ∏ p ∈ S, p.asIdeal`.

This is the combinatorial core behind counting the ideals `𝔄` with `𝔄 · σ 𝔄` a fixed product of
split primes — the engine of the prime-splitting layer of the multiquadratic roadmap.

## Main results

* `TauCeti.DedekindDomain.exists_transversal_family`: the family of
  `≥ 2 ^ (S.card / 2)` ideals.

## Provenance

Migrated from
[kim-em/erdos-unit-distance](https://github.com/kim-em/erdos-unit-distance), the formalization
of L. Alpöge's disproof of the uniform-constant Erdős unit-distance conjecture, where it counted
the conjugate-product ideals over primes `p ≡ 1 (mod 4)` in a concrete CM field.
-/

public section

attribute [local instance] Classical.propDecidable

namespace TauCeti.DedekindDomain

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

include R

/-- A nonzero prime ideal of a Dedekind domain does not divide a finite product of nonzero
prime ideals unless it equals one of the factors. -/
private theorem isPrime_not_dvd_prod (p : IsDedekindDomain.HeightOneSpectrum R)
    {T : Finset (IsDedekindDomain.HeightOneSpectrum R)} (hpT : p ∉ T) :
    ¬ p.asIdeal ∣ ∏ q ∈ T, q.asIdeal := by
  have := p.isPrime
  have hpprime : Prime p.asIdeal := p.prime
  rw [Prime.dvd_finsetProd_iff hpprime]
  rintro ⟨q, hqT, hpq⟩
  have heq : q.asIdeal = p.asIdeal := q.isMaximal.eq_of_le p.isMaximal.ne_top (Ideal.le_of_dvd hpq)
  exact hpT (IsDedekindDomain.HeightOneSpectrum.ext heq ▸ hqT)

omit R [CommRing R] [IsDedekindDomain R] in
/-- Under an involutive `f` with `q = f p`, the image `f x` of an element outside the pair
`{p, q}` again lies outside `{p, q}`. -/
private theorem notMem_pair_of_apply_involutive {α : Type*} [DecidableEq α] {f : α → α}
    {p q x : α} (hqdef : q = f p) (hinvolx : f (f x) = x) (hinvolp : f (f p) = p)
    (hxnotpair : x ∉ ({p, q} : Finset α)) : f x ∉ ({p, q} : Finset α) := by
  rw [Finset.mem_insert, Finset.mem_singleton]
  rintro (h | h)
  · -- `f x = p` forces `x = f p = q`, but `x ∉ {p, q}`.
    refine hxnotpair ?_
    rw [Finset.mem_insert, Finset.mem_singleton]
    exact Or.inr <| calc
      x = f (f x) := hinvolx.symm
      _ = f p := by rw [h]
      _ = q := hqdef.symm
  · -- `f x = q = f p` forces `x = p`, but `x ∉ {p, q}`.
    refine hxnotpair ?_
    rw [Finset.mem_insert, Finset.mem_singleton]
    exact Or.inl <| calc
      x = f (f x) := hinvolx.symm
      _ = f q := by rw [h]
      _ = f (f p) := by rw [hqdef]
      _ = p := hinvolp

omit [IsDedekindDomain R] in
/-- Transporting a height-one prime along a ring equivalence `σ` maps its ideal to the image
ideal: `(equivOfRingEquiv σ p).asIdeal = Ideal.map σ p.asIdeal`. -/
private lemma asIdeal_equivOfRingEquiv (σ : R ≃+* R) (p : IsDedekindDomain.HeightOneSpectrum R) :
    (IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv σ p).asIdeal =
      Ideal.map σ p.asIdeal := by
  ext x
  -- `equivOfRingEquiv` transports a prime by comapping along `σ.symm`, so membership in its
  -- ideal is by definition membership of `σ.symm x`; there is no lemma stating this.
  change σ.symm x ∈ p.asIdeal ↔ x ∈ Ideal.map σ p.asIdeal
  exact Ideal.symm_apply_mem_of_equiv_iff

/-- For a distinct prime `q ≠ p` and a family `G'` no member of which is divisible by `p.asIdeal`,
multiplying `G'` by `p.asIdeal` and by `q.asIdeal` gives disjoint images. -/
private theorem disjoint_image_mul_asIdeal {p q : IsDedekindDomain.HeightOneSpectrum R}
    {G' : Finset (Ideal R)} (hpq : q ≠ p) (hpFree : ∀ A ∈ G', ¬ p.asIdeal ∣ A) :
    Disjoint (G'.image (· * p.asIdeal)) (G'.image (· * q.asIdeal)) := by
  rw [Finset.disjoint_left]
  rintro A hAp hAq
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hAp
  obtain ⟨b, hb, hab⟩ := Finset.mem_image.mp hAq
  -- `a * p = b * q` forces `p ∣ b`, but no member of `G'` is divisible by `p`.
  have hpdvd : p.asIdeal ∣ b := by
    have hpdvd' : p.asIdeal ∣ b * q.asIdeal := hab.symm ▸ dvd_mul_left p.asIdeal a
    rcases ((Ideal.prime_iff_isPrime p.ne_bot).mpr p.isPrime).dvd_or_dvd hpdvd' with h | h
    · exact h
    · exact absurd (q.isMaximal.eq_of_le p.isMaximal.ne_top (Ideal.le_of_dvd h))
        (fun hpqIdeal => hpq (IsDedekindDomain.HeightOneSpectrum.ext hpqIdeal))
  exact hpFree b hb hpdvd

omit R [CommRing R] [IsDedekindDomain R] in
/-- If `n ≤ m + 2` then `2 ^ (n / 2) ≤ 2 * 2 ^ (m / 2)`. -/
private lemma two_pow_div_two_le_two_mul_two_pow_div_two_of_le_add_two {m n : ℕ} (hmn : n ≤ m + 2) :
    2 ^ (n / 2) ≤ 2 * 2 ^ (m / 2) := by
  rw [← pow_succ']
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

omit R [CommRing R] [IsDedekindDomain R] in
/-- Every ideal in the union `G'.image (· * P) ∪ G'.image (· * Q)` has conjugate product `prodS`,
given the conjugate-pair relations `Q = Ideal.map σ P` and `Ideal.map σ Q = P`, the factorisation
`prodS = prodS' * P * Q` of the product through the pair, and the product property
`a * Ideal.map σ a = prodS'` of every `a ∈ G'`. This is a pure identity about ideals under a ring
homomorphism `σ`, valid over any commutative semiring (no Dedekind structure needed). -/
private theorem mul_map_eq_prod_of_mem_image_union {R : Type*} [CommSemiring R] {σ : R →+* R}
    {prodS prodS' P Q : Ideal R} {G' : Finset (Ideal R)}
    (hqIdeal : Q = Ideal.map σ P) (hmapq : Ideal.map σ Q = P) (hprodS : prodS = prodS' * P * Q)
    (hprod' : ∀ a ∈ G', a * Ideal.map σ a = prodS') {A : Ideal R}
    (hA : A ∈ G'.image (· * P) ∪ G'.image (· * Q)) :
    A * Ideal.map σ A = prodS := by
  rw [Finset.mem_union] at hA
  rcases hA with hA | hA
  · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hA
    rw [Ideal.map_mul, ← hqIdeal, hprodS, ← hprod' a ha]; ring
  · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hA
    rw [Ideal.map_mul, hmapq, hprodS, ← hprod' a ha]; ring

/-- **Two shifted copies double the family.** Multiplying a family of ideals by each of two
height-one primes gives images of the same size, and if those images are disjoint the union has
twice the cardinality. That is exactly enough to carry a bound `2 ^ (m / 2)` up to `2 ^ (n / 2)`
whenever `n ≤ m + 2` — the two primes removed from the index set at each induction step. No
relationship between the primes is assumed beyond disjointness of the images; the caller
supplies a conjugate pair, but the estimate does not need that. -/
private lemma two_pow_le_card_union_image_mul {G' : Finset (Ideal R)}
    {p q : IsDedekindDomain.HeightOneSpectrum R}
    (hdisj : Disjoint (G'.image (· * p.asIdeal)) (G'.image (· * q.asIdeal)))
    {n m : ℕ} (hcard' : 2 ^ (m / 2) ≤ G'.card) (hnm : n ≤ m + 2) :
    2 ^ (n / 2) ≤ ((G'.image (· * p.asIdeal)) ∪ (G'.image (· * q.asIdeal))).card := by
  rw [Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injective _ (fun _ _ h => mul_right_cancel₀ p.ne_bot h),
    Finset.card_image_of_injective _ (fun _ _ h => mul_right_cancel₀ q.ne_bot h)]
  calc 2 ^ (n / 2) ≤ 2 * 2 ^ (m / 2) :=
        two_pow_div_two_le_two_mul_two_pow_div_two_of_le_add_two hnm
    _ ≤ G'.card + G'.card := by omega

omit [IsDedekindDomain R] in
/-- **The complement of a conjugate pair is still invariant.** Removing `p` and its image `q`
from `S` leaves a set the involution still maps to itself: an element outside the pair cannot be
sent into it, since applying the involution twice returns it. -/
private lemma mem_sdiff_pair_of_invariant {σ : R ≃+* R}
    {S : Finset (IsDedekindDomain.HeightOneSpectrum R)} {p q : IsDedekindDomain.HeightOneSpectrum R}
    (hqdef : q = IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv σ p)
    (hinv : ∀ x ∈ S, IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv σ x ∈ S)
    (hinvol : ∀ x ∈ S, IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv σ
      (IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv σ x) = x) (hpS : p ∈ S) :
    ∀ x ∈ S \ {p, q}, IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv σ x ∈ S \ {p, q} := by
  intro x hx
  have hxS := (Finset.mem_sdiff.mp hx).1
  refine Finset.mem_sdiff.mpr ⟨hinv x hxS, ?_⟩
  exact notMem_pair_of_apply_involutive
    (f := IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv σ) hqdef (hinvol x hxS)
    (hinvol p hpS) (Finset.mem_sdiff.mp hx).2

/-- The inductive step. Given a conjugate pair `p`, `σ p` inside `S` and a transversal family for
`S` with that pair removed, multiplying the family through by `p` and by `σ p` separately doubles
it and gives a transversal family for `S`. -/
private theorem exists_transversal_family_of_sdiff_pair (σ : R ≃+* R)
    {S : Finset (IsDedekindDomain.HeightOneSpectrum R)}
    {p : IsDedekindDomain.HeightOneSpectrum R} (hpS : p ∈ S)
    (hqS : IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv σ p ∈ S)
    (hpq : IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv σ p ≠ p)
    (hinvol : IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv σ
      (IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv σ p) = p) {G' : Finset (Ideal R)}
    (hcard' : 2 ^ ((S \ {p, IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv σ p}).card / 2)
      ≤ G'.card)
    (hprod' : ∀ A ∈ G', A * Ideal.map σ A =
      ∏ x ∈ S \ {p, IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv σ p}, x.asIdeal) :
    ∃ G : Finset (Ideal R), 2 ^ (S.card / 2) ≤ G.card ∧
      ∀ A ∈ G, A * Ideal.map σ A = ∏ x ∈ S, x.asIdeal := by
  set q := IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv σ p with hqdef
  have hpair : ({p, q} : Finset (IsDedekindDomain.HeightOneSpectrum R)) ⊆ S :=
    Finset.insert_subset_iff.mpr ⟨hpS, Finset.singleton_subset_iff.mpr hqS⟩
  have hqIdeal : q.asIdeal = Ideal.map σ p.asIdeal := by
    rw [hqdef]; exact asIdeal_equivOfRingEquiv σ p
  -- The product over `S` factors through the conjugate pair we removed.
  have hprodS : ∏ x ∈ S, x.asIdeal
      = (∏ x ∈ S \ {p, q}, x.asIdeal) * p.asIdeal * q.asIdeal := by
    rw [← Finset.prod_sdiff hpair, Finset.prod_pair hpq.symm, mul_assoc]
  have hcardS : (S \ {p, q}).card = S.card - 2 := by
    have h := Finset.card_sdiff_add_card_eq_card hpair
    rw [Finset.card_pair hpq.symm] at h
    omega
  have hpS' : p ∉ S \ {p, q} := fun h => (Finset.mem_sdiff.mp h).2 (Finset.mem_insert_self _ _)
  refine ⟨(G'.image (· * p.asIdeal)) ∪ (G'.image (· * q.asIdeal)), ?_, ?_⟩
  · -- The two images are disjoint, so the union doubles the family.
    have hdisj : Disjoint (G'.image (· * p.asIdeal)) (G'.image (· * q.asIdeal)) :=
      disjoint_image_mul_asIdeal hpq (fun A hA hpA =>
        isPrime_not_dvd_prod p hpS' (hprod' A hA ▸ dvd_mul_of_dvd_left hpA (Ideal.map σ A)))
    exact two_pow_le_card_union_image_mul hdisj hcard' (by omega)
  · have hmapq : Ideal.map σ q.asIdeal = p.asIdeal := by
      rw [← asIdeal_equivOfRingEquiv σ q]
      exact congr_arg IsDedekindDomain.HeightOneSpectrum.asIdeal hinvol
    exact fun A hA =>
      mul_map_eq_prod_of_mem_image_union (σ := (σ : R →+* R)) hqIdeal hmapq hprodS hprod' hA

/-- **Conjugate-transversal ideal family.** For a fixed-point-free involution `σ` of a finite set
`S` of height-one primes of a Dedekind domain, there are at least `2 ^ (S.card / 2)` ideals `A`
with `A * σ A = ∏ p ∈ S, p.asIdeal`. -/
theorem exists_transversal_family (σ : R ≃+* R) (S : Finset (IsDedekindDomain.HeightOneSpectrum R))
    (hinv : ∀ p ∈ S, IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv σ p ∈ S) (hinvol : ∀ p ∈ S,
      IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv σ
        (IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv σ p) = p)
    (hfree : ∀ p ∈ S, IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv σ p ≠ p) :
    ∃ G : Finset (Ideal R), 2 ^ (S.card / 2) ≤ G.card ∧
      ∀ A ∈ G, A * Ideal.map σ A = ∏ p ∈ S, p.asIdeal := by
  induction S using Finset.strongInduction with
  | _ S ih =>
  rcases S.eq_empty_or_nonempty with rfl | hS
  · refine ⟨{1}, by simp, fun A hA => ?_⟩
    rw [Finset.mem_singleton.mp hA, Finset.prod_empty, one_mul, Ideal.one_eq_top, Ideal.map_top]
  obtain ⟨p, hpS⟩ := hS
  set q := IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv σ p with hqdef
  have hqS : q ∈ S := hinv p hpS
  have hS'sub : S \ {p, q} ⊂ S :=
    Finset.sdiff_ssubset (Finset.insert_subset_iff.mpr ⟨hpS, Finset.singleton_subset_iff.mpr hqS⟩)
      ⟨p, Finset.mem_insert_self _ _⟩
  -- The subset `S \ {p, q}` still satisfies all the hypotheses.
  have hmem' : ∀ {x}, x ∈ S \ {p, q} → x ∈ S := fun hx => (Finset.mem_sdiff.mp hx).1
  obtain ⟨G', hcard', hprod'⟩ := ih _ hS'sub (mem_sdiff_pair_of_invariant hqdef hinv hinvol hpS)
    (fun x hx => hinvol x (hmem' hx)) (fun x hx => hfree x (hmem' hx))
  exact exists_transversal_family_of_sdiff_pair σ hpS hqS (hfree p hpS) (hinvol p hpS)
    hcard' hprod'

end TauCeti.DedekindDomain
