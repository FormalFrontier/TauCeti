/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Multiquadratic.Prime.Discriminant.Compositum
public import TauCeti.NumberTheory.NumberField.Quadratic.TotalRamification
public import TauCeti.NumberTheory.RamificationInertia.Tower
import TauCeti.NumberTheory.Multiquadratic.Prime.Discriminant.Independence
import TauCeti.NumberTheory.Multiquadratic.RelativeDegree
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.RingTheory.Ideal.NatInt

/-!
# Ramification in a compositum of prime-discriminant quadratic fields

Let `D i` be distinct prime discriminants, at most one of which is even, and let `root i` be
chosen square roots of their radicands inside a number field. This file describes the ramification
of the rational primes in their compositum `M = ℚ(root i : i)`.

Two facts are proved. Together they are the ramified-prime half of the multiquadratic splitting
law, complementary to the quadratic-residue description in
`TauCeti/NumberTheory/Multiquadratic/Prime/Discriminant/Splitting.lean`, which is stated for the
primes dividing none of the `D i`.

* A rational prime ramifies in `M` if and only if it is the prime `primeDiscriminantPrime (D i)`
  belonging to one of the factors. This is read off the discriminant
  `|disc M| = ∏ i, |D i| ^ 2 ^ (n - 1)` computed in `Prime/Discriminant/Compositum.lean`, since a
  prime divides a prime discriminant exactly when it is the prime belonging to it.
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
* `TauCeti.Multiquadratic.ramificationIdx_eq_two_primeDiscriminantPrime`: the ramification index
  at a ramified prime is `2`.
* `TauCeti.Multiquadratic.isUnramifiedIn_of_forall_ramificationIdx_eq_two`: the relative
  unramifiedness criterion over a subfield that already carries all the ramification.
-/

public section

open IntermediateField NumberField
open scoped NumberField

namespace TauCeti.Multiquadratic

universe u v

variable {ι : Type u} [Finite ι] {L : Type v} [Field L] [NumberField L]

section RamifiedPrimes

/-- **The ramified primes of a prime-discriminant compositum.** Let `D : ι → ℤ` be an injective
family of prime discriminants with at most one even member and let `root i` square to the radicand
of `D i`. A rational prime ramifies in the compositum `ℚ(root i : i)` exactly when it is the prime
`primeDiscriminantPrime (D i)` belonging to one of the factors.

The discriminant of the compositum is `∏ i, |D i| ^ 2 ^ (n - 1)`, so the primes dividing it are
the primes dividing some `D i`, and a prime divides a prime discriminant only if it is *the* prime
belonging to it. -/
theorem mem_ramifiedPrimes_adjoin_range_primeDiscriminantRadicands_iff
    (D : ι → ℤ) (hD : ∀ i, IsPrimeDiscriminant (D i)) (hinj : Function.Injective D)
    (heven : ∀ i j, IsEvenPrimeDiscriminant (D i) → IsEvenPrimeDiscriminant (D j) → D i = D j)
    (root : ι → L)
    (hroot : ∀ i, root i ^ 2 = algebraMap ℚ L (((primeDiscriminantRadicand (D i) : ℤ) : ℚ)))
    {p : ℕ} (hp : p.Prime) :
    p ∈ ramifiedPrimes (adjoin ℚ (Set.range root)) ↔ ∃ i, p = primeDiscriminantPrime (D i) := by
  classical
  have := Fintype.ofFinite ι
  rw [NumberField.mem_ramifiedPrimes_iff_dvd_discr hp, Int.natCast_dvd,
    natAbs_discr_adjoin_range_primeDiscriminantRadicands D hD hinj heven root hroot,
    hp.prime.dvd_finsetProd_iff]
  constructor
  · rintro ⟨i, -, hdvd⟩
    exact ⟨i, (natCast_dvd_primeDiscriminant_iff (hD i) hp).mp
      (Int.natCast_dvd.mpr (hp.dvd_of_dvd_pow hdvd))⟩
  · rintro ⟨i, rfl⟩
    refine ⟨i, Finset.mem_univ i, dvd_pow ?_ (Nat.two_pow_pos _).ne'⟩
    exact Int.natCast_dvd.mp ((natCast_dvd_primeDiscriminant_iff (hD i) hp).mpr rfl)

/-- **The ramified primes of a field generated by prime-discriminant roots.** The `⊤` form of
`mem_ramifiedPrimes_adjoin_range_primeDiscriminantRadicands_iff`, for a number field `L` that the
chosen roots generate. -/
theorem mem_ramifiedPrimes_iff_exists_eq_primeDiscriminantPrime
    (D : ι → ℤ) (hD : ∀ i, IsPrimeDiscriminant (D i)) (hinj : Function.Injective D)
    (heven : ∀ i j, IsEvenPrimeDiscriminant (D i) → IsEvenPrimeDiscriminant (D j) → D i = D j)
    (root : ι → L)
    (hroot : ∀ i, root i ^ 2 = algebraMap ℚ L (((primeDiscriminantRadicand (D i) : ℤ) : ℚ)))
    (htop : adjoin ℚ (Set.range root) = ⊤) {p : ℕ} (hp : p.Prime) :
    p ∈ ramifiedPrimes L ↔ ∃ i, p = primeDiscriminantPrime (D i) := by
  have f : (adjoin ℚ (Set.range root) : IntermediateField ℚ L) ≃ₐ[ℚ] L :=
    (IntermediateField.equivOfEq htop).trans IntermediateField.topEquiv
  have hdisc : NumberField.discr (adjoin ℚ (Set.range root)) = NumberField.discr L :=
    NumberField.discr_eq_discr_of_algEquiv _ f
  rw [← mem_ramifiedPrimes_adjoin_range_primeDiscriminantRadicands_iff D hD hinj heven root hroot
    hp, NumberField.mem_ramifiedPrimes_iff_dvd_discr hp,
    NumberField.mem_ramifiedPrimes_iff_dvd_discr hp, hdisc]

end RamifiedPrimes

section Ramification

variable (D : ι → ℤ) (root : ι → L)

/-- **A prime outside the family is unramified.** If a rational prime is not the prime belonging to
any of the prime-discriminant factors, it is unramified in the field they generate. -/
theorem isUnramifiedIn_of_forall_ne_primeDiscriminantPrime
    (hD : ∀ i, IsPrimeDiscriminant (D i)) (hinj : Function.Injective D)
    (heven : ∀ i j, IsEvenPrimeDiscriminant (D i) → IsEvenPrimeDiscriminant (D j) → D i = D j)
    (hroot : ∀ i, root i ^ 2 = algebraMap ℚ L (((primeDiscriminantRadicand (D i) : ℤ) : ℚ)))
    (htop : adjoin ℚ (Set.range root) = ⊤) {p : ℕ} (hp : p.Prime)
    (hne : ∀ i, p ≠ primeDiscriminantPrime (D i)) :
    Algebra.IsUnramifiedIn (𝓞 L) (Ideal.span {(p : ℤ)}) := by
  by_contra hcon
  obtain ⟨i, hi⟩ := (mem_ramifiedPrimes_iff_exists_eq_primeDiscriminantPrime D hD hinj heven root
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
    (fun a b hab => Subtype.ext (hinj hab)) (fun a b ha hb => heven _ _ ha hb)
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
      (fun _ : Fin 1 => D i) (fun _ => hD i) (fun a b _ => Subsingleton.elim a b)
      (fun _ _ _ _ => rfl) (fun _ : Fin 1 => root i) (fun _ => hroot i) hp).mpr ⟨0, rfl⟩
    rwa [hrange] at h
  exact NumberField.ramificationIdx_eq_two_of_mem_ramifiedPrimes hfin hmem 𝔮

/-- **The ramification index at a ramified prime of a prime-discriminant compositum is `2`.**
However many factors the compositum has, a prime belonging to one of them has ramification index
exactly two: the inertia subgroup at a ramified prime is as small as it can be.

The upper bound is transverse cancellation. The compositum `U` of the other roots is unramified at
the prime (`isUnramifiedIn_adjoin_range_ne_primeDiscriminantPrime`), so the absolute ramification
index equals the relative one over `U`, which is at most `[L : U] = 2`. The lower bound is the
total ramification of the quadratic subfield `ℚ(root i)`. -/
theorem ramificationIdx_eq_two_primeDiscriminantPrime
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

/-- **Unramifiedness over a subfield carrying all the ramification.** Let `F` be a subfield of the
prime-discriminant compositum `L` in which every prime `primeDiscriminantPrime (D i)` already has
ramification index `2`. Then every prime of `𝓞 F` is unramified in `𝓞 L`: the extension `L / F` is
unramified at every finite place.

This is the finite-place half of the genus-field property. For the genus field of `ℚ(√d)` the
subfield `F` is the embedded copy of `ℚ(√d)`, whose ramified primes are exactly the primes of the
prime-discriminant factorization of its discriminant, each with ramification index `2`. -/
theorem isUnramifiedIn_of_forall_ramificationIdx_eq_two
    (hD : ∀ i, IsPrimeDiscriminant (D i)) (hinj : Function.Injective D)
    (heven : ∀ i j, IsEvenPrimeDiscriminant (D i) → IsEvenPrimeDiscriminant (D j) → D i = D j)
    (hroot : ∀ i, root i ^ 2 = algebraMap ℚ L (((primeDiscriminantRadicand (D i) : ℤ) : ℚ)))
    (htop : adjoin ℚ (Set.range root) = ⊤) (F : IntermediateField ℚ L)
    (hF : ∀ (i : ι) (𝔮 : Ideal (𝓞 F)) [𝔮.IsPrime],
      𝔮.LiesOver (Ideal.span {(primeDiscriminantPrime (D i) : ℤ)}) → 𝔮.ramificationIdx ℤ = 2)
    (𝔮 : Ideal (𝓞 F)) [𝔮.IsPrime] :
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
    by_cases hex : ∃ i, p = primeDiscriminantPrime (D i)
    · obtain ⟨i, rfl⟩ := hex
      -- Cancel the ramification of `F` against the transverse compositum of the other roots.
      refine RamificationInertia.isUnramifiedIn_of_finrank_le_of_under_ramificationIdx_eq_one
        (R := ℤ) (U := 𝓞 (adjoin ℚ (Set.range fun j : {j // j ≠ i} => root j.val))) 𝔮 ?_ ?_
      · rw [hF i 𝔮 hlies, ← IsFractionRing.finrank_eq
          (𝓞 (adjoin ℚ (Set.range fun j : {j // j ≠ i} => root j.val)))
          (adjoin ℚ (Set.range fun j : {j // j ≠ i} => root j.val)) (𝓞 L) L]
        exact (finrank_over_adjoin_range_ne D root hD hinj heven hroot htop i).le
      · intro r _ hr
        have : r.LiesOver 𝔮 := hr
        have hrp : r.LiesOver (Ideal.span {(primeDiscriminantPrime (D i) : ℤ)}) :=
          Ideal.LiesOver.trans r 𝔮 _
        have hur : (r.under (𝓞 (adjoin ℚ (Set.range fun j : {j // j ≠ i} => root j.val)))).LiesOver
            (Ideal.span {(primeDiscriminantPrime (D i) : ℤ)}) :=
          ⟨by rw [Ideal.under_under]; exact hrp.over⟩
        exact (isUnramifiedIn_adjoin_range_ne_primeDiscriminantPrime D root hD hinj heven hroot
          i).ramificationIdx_eq_one hur
    · -- The prime is unramified in `L` already over `ℚ`, so nothing ramifies above `𝔮`.
      simp only [not_exists] at hex
      have hunr := isUnramifiedIn_of_forall_ne_primeDiscriminantPrime D root hD hinj heven hroot
        htop hp hex
      refine RamificationInertia.isUnramifiedIn_of_forall_ramificationIdx_le (R := ℤ) 𝔮 ?_
      intro r _ hr
      have : r.LiesOver 𝔮 := hr
      have hrp : r.LiesOver (Ideal.span {(p : ℤ)}) := Ideal.LiesOver.trans r 𝔮 _
      rw [hunr.ramificationIdx_eq_one hrp]
      exact 𝔮.ramificationIdx_pos ℤ

end Ramification

end TauCeti.Multiquadratic
