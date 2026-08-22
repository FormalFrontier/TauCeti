/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Multiquadratic.Prime.Discriminant.Compositum
public import TauCeti.NumberTheory.NumberField.RamifiedPrimes
import TauCeti.NumberTheory.NumberField.Quadratic.TotalRamification
import TauCeti.NumberTheory.RamificationInertia.Tower
import TauCeti.NumberTheory.Multiquadratic.Prime.Discriminant.Independence
import TauCeti.NumberTheory.Multiquadratic.RelativeDegree
import TauCeti.NumberTheory.NumberField.IntegralSqrt
import TauCeti.RingTheory.Ideal.LiesOver
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.Ideal.NatInt

/-!
# Ramification in a compositum of prime-discriminant quadratic fields

Let `D i` be prime discriminants and let `root i` be chosen square roots of their radicands inside
a number field. This file describes the ramification of the rational primes in their compositum
`M = ℚ(root i : i)`. The support result allows repeated factors and multiple even factors; the
ramification-index results additionally assume distinct factors with at most one even factor.

Two facts are proved. Together they are the ramified-prime half of the multiquadratic splitting
law, complementary to the quadratic-residue description in
`TauCeti/NumberTheory/Multiquadratic/Prime/Discriminant/Splitting.lean`, which is stated for the
primes dividing none of the `D i`.

* A rational prime ramifies in `M` if and only if it is the prime `primeDiscriminantPrime (D i)`
  belonging to one of the factors. One direction follows from the corresponding quadratic
  subfield. For the other, inertia outside this finite set fixes every generating square root and
  is therefore trivial.
* At such a prime the ramification index is exactly `2`, however large the compositum is: the
  inertia at a ramified prime of a prime-discriminant compositum is as small as it can be. The
  upper bound is a transverse cancellation — the compositum of all the *other* roots is
  unramified at `primeDiscriminantPrime (D i)` and has `M` as a quadratic extension — and the
  lower bound comes from the quadratic subfield `ℚ(root i)`, where the prime is totally ramified.

The payoff is a criterion for relative unramifiedness, which is the shape the genus-field
construction needs: if `F` is a subfield of `M` in which every `primeDiscriminantPrime (D i)`
already has ramification index `2`, then `M` is unramified over `F` at every finite place. The
genus field of `ℚ(√d)` is the case `F = ℚ(√d)`, whose ramified primes are precisely the primes of
the prime-discriminant factorization of its discriminant.

The prime-discriminant construction of the genus field is classical; see D. A. Cox, *Primes of the
Form x² + ny²*, §6.A, and F. Lemmermeyer, *Reciprocity Laws: from Euler to Eisenstein*, §2.2.

## Main results

* `TauCeti.Multiquadratic.mem_ramifiedPrimes_adjoin_range_primeDiscriminantRadicands_iff`: the
  ramified primes of the compositum are the primes belonging to the factors, and
  `TauCeti.Multiquadratic.mem_ramifiedPrimes_iff_exists_eq_primeDiscriminantPrime` is its form for
  a number field the roots generate.
* `TauCeti.Multiquadratic.isUnramifiedIn_of_forall_ne_primeDiscriminantPrime` and
  `TauCeti.Multiquadratic.isUnramifiedIn_adjoin_range_ne_primeDiscriminantPrime`: the two
  unramifiedness statements those give, for a prime outside the family and for the prime of an
  omitted factor in the compositum of the remaining ones.
* `TauCeti.Multiquadratic.ramificationIdx_eq_two_of_liesOver_primeDiscriminantPrime`: the
  ramification index at a ramified prime is `2`.
* `TauCeti.Multiquadratic.isUnramifiedIn_of_forall_ramificationIdx_eq_two`: the relative
  unramifiedness criterion at a prime of a subfield that already carries the ramification.
-/

public section

open Polynomial IntermediateField NumberField
open scoped NumberField

namespace TauCeti.Multiquadratic

universe u v

variable {ι : Type u} [Finite ι] {L : Type v} [Field L] [NumberField L]

section RamifiedPrimes

/-- If `d ≡ 1 (mod 4)` and `x² = d`, then `(1 + x) / 2` is an algebraic integer. -/
private theorem isIntegral_one_add_sqrt_div_two {x : L} {d : ℤ}
    (hx : x ^ 2 = algebraMap ℤ L d) (hd4 : d % 4 = 1) :
    IsIntegral ℤ ((1 + x) / 2) := by
  obtain ⟨e, he⟩ : ∃ e : ℤ, d = 4 * e + 1 := ⟨d / 4, by omega⟩
  have hde : algebraMap ℤ L d = 4 * algebraMap ℤ L e + 1 := by
    rw [he]
    simp only [map_add, map_mul, map_ofNat, map_one]
  refine ⟨X ^ 2 - X - C e, ?_, ?_⟩
  · monicity!
  · simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
    field_simp
    linear_combination hx + hde

/-- **A negated square root pins down the prime.** Let `P` be a prime of `𝓞 M` above the rational
prime `p`, and let `σ` be an automorphism of `M` that acts trivially modulo `P`. If `σ` negates a
square root `x` of the radicand of a prime discriminant `D`, then `p` is the prime belonging to
`D`. Contrapositively, inertia at any other prime fixes `x`.

Away from `2` the witness is `2x`, whose square `4d` lies in `P`; at `2` the odd prime
discriminant congruent to `1` modulo `4` makes `(1 + x) / 2` an algebraic integer, and the
corresponding witness squares to `d`. -/
private theorem eq_primeDiscriminantPrime_of_apply_eq_neg {M : Type v} [Field M] [NumberField M]
    {p : ℕ} (hp : p.Prime) (P : Ideal (𝓞 M)) [P.LiesOver (Ideal.span {(p : ℤ)})]
    {D : ℤ} (hD : IsPrimeDiscriminant D) {x : M}
    (hx : x ^ 2 = algebraMap ℤ M (primeDiscriminantRadicand D)) {σ : M ≃ₐ[ℚ] M}
    (hσ : ∀ z : 𝓞 M, σ • z - z ∈ P) (hneg : σ x = -x) :
    p = primeDiscriminantPrime D := by
  have : Fact p.Prime := ⟨hp⟩
  have hbridge (z : 𝓞 M) : algebraMap (𝓞 M) M (σ • z) = σ (algebraMap (𝓞 M) M z) := by
    have hcoe : algebraMap (𝓞 M) M (σ • z) = σ • algebraMap (𝓞 M) M z := by
      rw [← NumberField.RingOfIntegers.coe_eq_algebraMap,
        ← NumberField.RingOfIntegers.coe_eq_algebraMap]
      exact integralClosure.coe_smul σ z
    rw [hcoe, AlgEquiv.smul_def]
  by_cases hp2 : p = 2
  · subst p
    by_contra hne
    have hoddD : ¬ IsEvenPrimeDiscriminant D := fun heven =>
      hne (primeDiscriminantPrime_of_isEvenPrimeDiscriminant heven).symm
    have hd4 : primeDiscriminantRadicand D % 4 = 1 :=
      (isEvenPrimeDiscriminant_or_primeDiscriminantRadicand_mod_four_eq_one hD).resolve_left hoddD
    let W : 𝓞 M := ⟨(1 + x) / 2, isIntegral_one_add_sqrt_div_two hx hd4⟩
    have hW : σ • W - W ∈ P := hσ W
    -- `W` is given by its value, so its image in `M` is that value definitionally.
    have hWval : algebraMap (𝓞 M) M W = (1 + x) / 2 := rfl
    have hWcoe : algebraMap (𝓞 M) M (σ • W - W) = -x := by
      rw [map_sub, hbridge, hWval, map_div₀, map_add, map_one, hneg, map_ofNat]
      ring
    have hWsq : (σ • W - W) ^ 2 = algebraMap ℤ (𝓞 M) (primeDiscriminantRadicand D) := by
      apply FaithfulSMul.algebraMap_injective (𝓞 M) M
      rw [map_pow, hWcoe, neg_sq, ← IsScalarTower.algebraMap_apply ℤ (𝓞 M) M]
      exact hx
    have hdvd : (2 : ℤ) ∣ primeDiscriminantRadicand D :=
      (TauCeti.algebraMap_int_mem_iff_dvd_of_liesOver P _).mp
        (hWsq ▸ P.pow_mem_of_mem hW 2 (by norm_num))
    omega
  · let R : 𝓞 M := NumberField.integralSqrt hx
    have hR : σ • R = -R := by
      apply FaithfulSMul.algebraMap_injective (𝓞 M) M
      rw [hbridge, map_neg]
      simpa only [R, NumberField.algebraMap_integralSqrt] using hneg
    have htwoR : (2 : 𝓞 M) * R ∈ P := by
      have hsub := hσ R
      rw [hR] at hsub
      have heq : -((2 : 𝓞 M) * R) = -R - R := by ring
      have hmem : -((2 : 𝓞 M) * R) ∈ P := heq.symm ▸ hsub
      exact neg_mem_iff.mp hmem
    have hsq : ((2 : 𝓞 M) * R) ^ 2 = algebraMap ℤ (𝓞 M) (4 * primeDiscriminantRadicand D) := by
      rw [mul_pow, NumberField.integralSqrt_sq, map_mul]
      norm_num
    have hdvd : (p : ℤ) ∣ 4 * primeDiscriminantRadicand D :=
      (TauCeti.algebraMap_int_mem_iff_dvd_of_liesOver P _).mp
        (hsq ▸ P.pow_mem_of_mem htwoR 2 (by norm_num))
    have hpnot4 : ¬ (p : ℤ) ∣ 4 := by
      intro hp4
      have hp4nat : p ∣ 2 ^ 2 := by norm_num at hp4 ⊢; exact_mod_cast hp4
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
        (hp.dvd_of_dvd_pow hp4nat))
    have hpdr : (p : ℤ) ∣ primeDiscriminantRadicand D :=
      (Nat.prime_iff_prime_int.mp hp).dvd_mul.mp hdvd |>.resolve_left hpnot4
    have hpD : (p : ℤ) ∣ D :=
      (dvd_primeDiscriminant_iff_dvd_radicand (q := p) D hp2).mpr hpdr
    exact (natCast_dvd_primeDiscriminant_iff hD hp).mp hpD

/-- **The ramified primes of a prime-discriminant compositum.** Let `D : ι → ℤ` be any finite
family of prime discriminants and let `root i` square to the radicand of `D i`. A rational prime
ramifies in the compositum `ℚ(root i : i)` exactly when it is the prime
`primeDiscriminantPrime (D i)` belonging to one of the factors. Repeated factors and multiple even
prime discriminants are allowed: neither changes the support of ramification. -/
theorem mem_ramifiedPrimes_adjoin_range_primeDiscriminantRadicands_iff
    (D : ι → ℤ) (hD : ∀ i, IsPrimeDiscriminant (D i)) (root : ι → L)
    (hroot : ∀ i, root i ^ 2 = algebraMap ℚ L (((primeDiscriminantRadicand (D i) : ℤ) : ℚ)))
    {p : ℕ} (hp : p.Prime) :
    p ∈ ramifiedPrimes (adjoin ℚ (Set.range root)) ↔ ∃ i, p = primeDiscriminantPrime (D i) := by
  classical
  let M : IntermediateField ℚ L := adjoin ℚ (Set.range root)
  let rootM : ι → M := gen (K := ℚ) root
  have hrootM (i : ι) : rootM i ^ 2 =
      algebraMap ℚ M (((primeDiscriminantRadicand (D i) : ℤ) : ℚ)) := gen_sq hroot i
  have hrootM_int (i : ι) : rootM i ^ 2 =
      algebraMap ℤ M (primeDiscriminantRadicand (D i)) := by
    rw [hrootM, IsScalarTower.algebraMap_apply ℤ ℚ M]
    norm_num
  constructor
  · intro hram
    by_contra hnot
    simp only [not_exists] at hnot
    have htopM : adjoin ℚ (Set.range rootM) = ⊤ := adjoin_gen_eq_top
    have hG' := isGalois (K := ℚ) (L := M)
      (d := fun i => ((primeDiscriminantRadicand (D i) : ℤ) : ℚ))
      (root := rootM) hrootM
    have hG : IsGalois ℚ M := by
      rw [htopM] at hG'
      exact isGalois_iff_isGalois_top.mp hG'
    let _ : Fact p.Prime := ⟨hp⟩
    have : IsGalois ℚ M := hG
    have : Finite (M →ₐ[ℚ] M) := Fintype.finite (minpoly.AlgHom.fintype ℚ M M)
    have : Finite Gal(M/ℚ) := Finite.algEquiv
    have : IsGaloisGroup Gal(M/ℚ) ℤ (𝓞 M) :=
      IsGaloisGroup.of_isFractionRing Gal(M/ℚ) ℤ (𝓞 M) ℚ M
    have hunr : Algebra.IsUnramifiedIn (𝓞 M) (Ideal.span {(p : ℤ)}) := by
      rw [Algebra.isUnramifiedIn_iff_forall_ramificationIdx_eq_one]
      intro P hP hPover
      have : P.IsPrime := hP
      have : P.LiesOver (Ideal.span {(p : ℤ)}) := hPover
      have : (Ideal.span {(p : ℤ)} : Ideal ℤ).IsPrime :=
        (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr
          (Nat.prime_iff_prime_int.mp hp)
      have hinertia : P.inertia Gal(M/ℚ) = ⊥ := by
        rw [eq_bot_iff]
        intro σ hσ
        rw [Subgroup.mem_bot]
        apply AlgEquiv.ext
        intro x
        rw [AlgEquiv.one_apply]
        have hx : x ∈ adjoin ℚ (Set.range rootM) := by
          rw [htopM]
          exact IntermediateField.mem_top
        induction hx using IntermediateField.adjoin_induction with
        | mem x hx =>
            obtain ⟨i, rfl⟩ := hx
            have hsquare : σ (rootM i) ^ 2 = rootM i ^ 2 := by
              rw [← map_pow, hrootM, AlgEquiv.commutes, ← hrootM]
            rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsquare with hi | hi
            · exact hi
            · exact absurd (eq_primeDiscriminantPrime_of_apply_eq_neg hp P (hD i)
                (hrootM_int i) (fun z => hσ z) hi) (hnot i)
        | algebraMap q => exact AlgEquiv.commutes σ q
        | add a b _ _ ha hb => rw [map_add, ha, hb]
        | inv a _ ha => rw [map_inv₀, ha]
        | mul a b _ _ ha hb => rw [map_mul, ha, hb]
      have hcard := Ideal.card_inertia_eq_ramificationIdxIn (G := Gal(M/ℚ))
        (Ideal.span {(p : ℤ)}) P
      rw [hinertia] at hcard
      rw [← Ideal.ramificationIdxIn_eq_ramificationIdx (Ideal.span {(p : ℤ)}) P Gal(M/ℚ)]
      simpa using hcard.symm
    exact (NumberField.mem_ramifiedPrimes_iff.mp hram).2 hunr
  · rintro ⟨i, rfl⟩
    rw [NumberField.mem_ramifiedPrimes_iff_dvd_discr
      (prime_primeDiscriminantPrime (hD i))]
    let F : IntermediateField ℚ M := adjoin ℚ {rootM i}
    apply dvd_trans _ (NumberField.discr_dvd_discr F M)
    rw [discr_adjoin_singleton_eq_primeDiscriminant (hD i) (hrootM_int i)]
    exact primeDiscriminantPrime_dvd (hD i)

/-- **The ramified primes of a field generated by prime-discriminant roots.** The `⊤` form of
`mem_ramifiedPrimes_adjoin_range_primeDiscriminantRadicands_iff`, for a number field `L` that the
chosen roots generate. -/
theorem mem_ramifiedPrimes_iff_exists_eq_primeDiscriminantPrime
    (D : ι → ℤ) (hD : ∀ i, IsPrimeDiscriminant (D i)) (root : ι → L)
    (hroot : ∀ i, root i ^ 2 = algebraMap ℚ L (((primeDiscriminantRadicand (D i) : ℤ) : ℚ)))
    (htop : adjoin ℚ (Set.range root) = ⊤) {p : ℕ} (hp : p.Prime) :
    p ∈ ramifiedPrimes L ↔ ∃ i, p = primeDiscriminantPrime (D i) := by
  have f : (adjoin ℚ (Set.range root) : IntermediateField ℚ L) ≃ₐ[ℚ] L :=
    (IntermediateField.equivOfEq htop).trans IntermediateField.topEquiv
  have hdisc : NumberField.discr (adjoin ℚ (Set.range root)) = NumberField.discr L :=
    NumberField.discr_eq_discr_of_algEquiv _ f
  rw [← mem_ramifiedPrimes_adjoin_range_primeDiscriminantRadicands_iff D hD root hroot
    hp, NumberField.mem_ramifiedPrimes_iff_dvd_discr hp,
    NumberField.mem_ramifiedPrimes_iff_dvd_discr hp, hdisc]

end RamifiedPrimes

section Ramification

variable (D : ι → ℤ) (root : ι → L)

/-- **A prime outside the family is unramified.** If a rational prime is not the prime belonging to
any of the prime-discriminant factors, it is unramified in the field they generate. -/
theorem isUnramifiedIn_of_forall_ne_primeDiscriminantPrime
    (hD : ∀ i, IsPrimeDiscriminant (D i))
    (hroot : ∀ i, root i ^ 2 = algebraMap ℚ L (((primeDiscriminantRadicand (D i) : ℤ) : ℚ)))
    (htop : adjoin ℚ (Set.range root) = ⊤) {p : ℕ} (hp : p.Prime)
    (hne : ∀ i, p ≠ primeDiscriminantPrime (D i)) :
    Algebra.IsUnramifiedIn (𝓞 L) (Ideal.span {(p : ℤ)}) := by
  by_contra hcon
  obtain ⟨i, hi⟩ := (mem_ramifiedPrimes_iff_exists_eq_primeDiscriminantPrime D hD root
    hroot htop hp).mp (NumberField.mem_ramifiedPrimes_iff.mpr ⟨hp, hcon⟩)
  exact hne i hi

/-- **The transverse subcompositum is unramified at the omitted prime.** The prime belonging to the
factor `D i` is unramified in the compositum of the roots attached to all the *other* factors,
because that compositum's ramified primes belong to those other factors, and the prime of a factor
determines it. -/
theorem isUnramifiedIn_adjoin_range_ne_primeDiscriminantPrime
    (hD : ∀ i, IsPrimeDiscriminant (D i)) (hinj : Function.Injective D)
    (heven : ∀ i j, IsEvenPrimeDiscriminant (D i) → IsEvenPrimeDiscriminant (D j) → D i = D j)
    (hroot : ∀ i, root i ^ 2 = algebraMap ℚ L (((primeDiscriminantRadicand (D i) : ℤ) : ℚ)))
    (i : ι) :
    Algebra.IsUnramifiedIn (𝓞 (adjoin ℚ (Set.range fun j : {j // j ≠ i} => root j.val)))
      (Ideal.span {(primeDiscriminantPrime (D i) : ℤ)}) := by
  by_contra hcon
  have hp : (primeDiscriminantPrime (D i)).Prime := prime_primeDiscriminantPrime (hD i)
  obtain ⟨j, hj⟩ := (mem_ramifiedPrimes_adjoin_range_primeDiscriminantRadicands_iff
    (fun j : {j // j ≠ i} => D j.val) (fun j => hD j.val)
    (fun j : {j // j ≠ i} => root j.val) (fun j => hroot j.val) hp).mp
    (NumberField.mem_ramifiedPrimes_iff.mpr ⟨hp, hcon⟩)
  exact j.property (hinj (eq_of_primeDiscriminantPrime_eq (hD i) (hD j.val)
    (fun ha hb => heven _ _ ha hb) hj)).symm

/-- The compositum is quadratic over the transverse subcompositum omitting one factor. -/
private theorem finrank_over_adjoin_range_ne
    (hD : ∀ i, IsPrimeDiscriminant (D i)) (hinj : Function.Injective D)
    (heven : ∀ i j, IsEvenPrimeDiscriminant (D i) → IsEvenPrimeDiscriminant (D j) → D i = D j)
    (hroot : ∀ i, root i ^ 2 = algebraMap ℚ L (((primeDiscriminantRadicand (D i) : ℤ) : ℚ)))
    (htop : adjoin ℚ (Set.range root) = ⊤) (i : ι) :
    Module.finrank (adjoin ℚ (Set.range fun j : {j // j ≠ i} => root j.val)) L = 2 :=
  finrank_top_over_adjoin_range_ne hroot
    (not_isSquare_prod_primeDiscriminantRadicands_of_forall_isEvenPrimeDiscriminant_eq D hD hinj
      heven) htop i

omit [Finite ι] in
/-- The quadratic subfield attached to one factor is totally ramified at the prime of that
factor. -/
private theorem ramificationIdx_adjoin_singleton_eq_two
    (hD : ∀ i, IsPrimeDiscriminant (D i))
    (hroot : ∀ i, root i ^ 2 = algebraMap ℚ L (((primeDiscriminantRadicand (D i) : ℤ) : ℚ)))
    (i : ι) (𝔮 : Ideal (𝓞 (adjoin ℚ ({root i} : Set L)))) [𝔮.IsPrime]
    [𝔮.LiesOver (Ideal.span {(primeDiscriminantPrime (D i) : ℤ)})] :
    𝔮.ramificationIdx ℤ = 2 := by
  have hp : (primeDiscriminantPrime (D i)).Prime := prime_primeDiscriminantPrime (hD i)
  have hrange : Set.range (fun _ : Fin 1 => root i) = ({root i} : Set L) := Set.range_const
  have hindep := not_isSquare_prod_primeDiscriminantRadicands_of_forall_isEvenPrimeDiscriminant_eq
    (fun _ : Fin 1 => D i) (fun _ => hD i) (fun a b _ => Subsingleton.elim a b)
    (fun _ _ _ _ => rfl)
  have hfin : Module.finrank ℚ (adjoin ℚ ({root i} : Set L)) = 2 := by
    have h := finrank_adjoin_range (K := ℚ) (root := fun _ : Fin 1 => root i)
      (fun _ => hroot i) hindep
    rwa [hrange, Nat.card_eq_fintype_card, Fintype.card_fin, pow_one] at h
  have hmem : primeDiscriminantPrime (D i) ∈ ramifiedPrimes (adjoin ℚ ({root i} : Set L)) := by
    have h := (mem_ramifiedPrimes_adjoin_range_primeDiscriminantRadicands_iff
      (fun _ : Fin 1 => D i) (fun _ => hD i)
      (fun _ : Fin 1 => root i) (fun _ => hroot i) hp).mpr ⟨0, rfl⟩
    rwa [hrange] at h
  exact NumberField.ramificationIdx_eq_two_of_mem_ramifiedPrimes hfin hmem 𝔮

/-- **The ramification index at a ramified prime of a prime-discriminant compositum is `2`.**
However many factors the compositum has, a prime belonging to one of them has ramification index
exactly two: the inertia subgroup at a ramified prime is as small as it can be.

The upper bound is transverse cancellation. The compositum `U` of the other roots is unramified at
the prime (`isUnramifiedIn_adjoin_range_ne_primeDiscriminantPrime`), so the absolute ramification
index equals the relative one over `U`, which is at most `[L : U] = 2`. The lower bound is the
total ramification of the quadratic subfield `ℚ(root i)`. -/
theorem ramificationIdx_eq_two_of_liesOver_primeDiscriminantPrime
    (hD : ∀ i, IsPrimeDiscriminant (D i)) (hinj : Function.Injective D)
    (heven : ∀ i j, IsEvenPrimeDiscriminant (D i) → IsEvenPrimeDiscriminant (D j) → D i = D j)
    (hroot : ∀ i, root i ^ 2 = algebraMap ℚ L (((primeDiscriminantRadicand (D i) : ℤ) : ℚ)))
    (htop : adjoin ℚ (Set.range root) = ⊤) (i : ι) (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime]
    [𝔓.LiesOver (Ideal.span {(primeDiscriminantPrime (D i) : ℤ)})] :
    𝔓.ramificationIdx ℤ = 2 := by
  classical
  set U : IntermediateField ℚ L := adjoin ℚ (Set.range fun j : {j // j ≠ i} => root j.val) with hU
  -- The transverse compositum is unramified at the prime, so it contributes nothing upstairs.
  have hUunr : Algebra.IsUnramifiedIn (𝓞 U)
      (Ideal.span {(primeDiscriminantPrime (D i) : ℤ)}) :=
    isUnramifiedIn_adjoin_range_ne_primeDiscriminantPrime D root hD hinj heven hroot i
  have h𝔓 : 𝔓.LiesOver (Ideal.span {(primeDiscriminantPrime (D i) : ℤ)}) := inferInstance
  have hUlies : (𝔓.under (𝓞 U)).LiesOver
      (Ideal.span {(primeDiscriminantPrime (D i) : ℤ)}) :=
    ⟨by rw [Ideal.under_under]; exact h𝔓.over⟩
  have hUone : (𝔓.under (𝓞 U)).ramificationIdx ℤ = 1 := hUunr.ramificationIdx_eq_one hUlies
  have hle : 𝔓.ramificationIdx ℤ ≤ 2 := by
    calc 𝔓.ramificationIdx ℤ
        = (𝔓.under (𝓞 U)).ramificationIdx ℤ * 𝔓.ramificationIdx (𝓞 U) :=
          Ideal.ramificationIdx_tower (R := ℤ) (𝔓.under (𝓞 U)) 𝔓
      _ = 𝔓.ramificationIdx (𝓞 U) := by rw [hUone, one_mul]
      _ ≤ Module.finrank (𝓞 U) (𝓞 L) :=
          RamificationInertia.ramificationIdx_le_finrank (𝔓.under (𝓞 U)) 𝔓
      _ = 2 := by
          rw [← IsFractionRing.finrank_eq (𝓞 U) U (𝓞 L) L, hU]
          exact finrank_over_adjoin_range_ne D root hD hinj heven hroot htop i
  -- The quadratic subfield attached to the factor is already totally ramified there.
  set F : IntermediateField ℚ L := adjoin ℚ ({root i} : Set L) with hF
  have hFlies : (𝔓.under (𝓞 F)).LiesOver
      (Ideal.span {(primeDiscriminantPrime (D i) : ℤ)}) :=
    ⟨by rw [Ideal.under_under]; exact h𝔓.over⟩
  have hFtwo : (𝔓.under (𝓞 F)).ramificationIdx ℤ = 2 :=
    ramificationIdx_adjoin_singleton_eq_two D root hD hroot i (𝔓.under (𝓞 F))
  have htower : 𝔓.ramificationIdx ℤ =
      (𝔓.under (𝓞 F)).ramificationIdx ℤ * 𝔓.ramificationIdx (𝓞 F) :=
    Ideal.ramificationIdx_tower (R := ℤ) (𝔓.under (𝓞 F)) 𝔓
  rw [hFtwo] at htower
  have hpos : 0 < 𝔓.ramificationIdx (𝓞 F) := 𝔓.ramificationIdx_pos (𝓞 F)
  omega

/-- **Unramifiedness over a subfield carrying the ramification.** Let `F` be a subfield of the
prime-discriminant compositum `L` and let `𝔮` be a prime of `𝓞 F` whose ramification index over
`ℤ` is already `2` whenever it lies over one of the primes `primeDiscriminantPrime (D i)`. Then
`𝔮` is unramified in `𝓞 L`.

Indeed, a prime of `𝓞 L` above `𝔮` has absolute ramification index `2` as well, by
`ramificationIdx_eq_two_of_liesOver_primeDiscriminantPrime`, so nothing is left to ramify in the
tower; and if `𝔮` lies over none of those primes, the rational prime below it is already
unramified in `L`.

This is the finite-place half of the genus-field property. For the genus field of `ℚ(√d)` the
subfield `F` is the embedded copy of `ℚ(√d)`, whose ramified primes are exactly the primes of the
prime-discriminant factorization of its discriminant, each with ramification index `2`. -/
theorem isUnramifiedIn_of_forall_ramificationIdx_eq_two
    (hD : ∀ i, IsPrimeDiscriminant (D i)) (hinj : Function.Injective D)
    (heven : ∀ i j, IsEvenPrimeDiscriminant (D i) → IsEvenPrimeDiscriminant (D j) → D i = D j)
    (hroot : ∀ i, root i ^ 2 = algebraMap ℚ L (((primeDiscriminantRadicand (D i) : ℤ) : ℚ)))
    (htop : adjoin ℚ (Set.range root) = ⊤) (F : IntermediateField ℚ L) (𝔮 : Ideal (𝓞 F))
    [𝔮.IsPrime]
    (hF : ∀ i, 𝔮.LiesOver (Ideal.span {(primeDiscriminantPrime (D i) : ℤ)}) →
      𝔮.ramificationIdx ℤ = 2) :
    Algebra.IsUnramifiedIn (𝓞 L) 𝔮 := by
  classical
  have hunder : (Ideal.under ℤ 𝔮).IsPrime := inferInstance
  rcases Ideal.isPrime_int_iff.mp hunder with hbot | ⟨p, hp, hspan⟩
  · -- A prime contracting to `⊥` is `⊥`, where there is nothing to ramify.
    have h𝔮 : 𝔮 = ⊥ := by
      by_contra hne
      exact Ideal.IsIntegral.comap_ne_bot (R := ℤ) hne hbot
    subst h𝔮
    exact Algebra.isUnramifiedIn_bot
  · have hlies : 𝔮.LiesOver (Ideal.span {(p : ℤ)}) := ⟨hspan.symm⟩
    refine RamificationInertia.isUnramifiedIn_of_forall_ramificationIdx_le (R := ℤ) 𝔮 ?_
    intro r _ hr
    have : r.LiesOver 𝔮 := hr
    have hrp : r.LiesOver (Ideal.span {(p : ℤ)}) := Ideal.LiesOver.trans r 𝔮 _
    by_cases hex : ∃ i, p = primeDiscriminantPrime (D i)
    · -- Both levels have ramification index exactly `2`, so nothing is left to ramify.
      obtain ⟨i, rfl⟩ := hex
      exact le_of_eq ((ramificationIdx_eq_two_of_liesOver_primeDiscriminantPrime D root hD hinj
        heven hroot htop i r).trans (hF i hlies).symm)
    · -- The prime is unramified in `L` already over `ℚ`, so nothing ramifies above `𝔮`.
      simp only [not_exists] at hex
      rw [(isUnramifiedIn_of_forall_ne_primeDiscriminantPrime D root hD hroot htop hp
        hex).ramificationIdx_eq_one hrp]
      exact 𝔮.ramificationIdx_pos ℤ

end Ramification

end TauCeti.Multiquadratic
