/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.NumberTheory.Multiquadratic.Degree
public import TauCeti.NumberTheory.Multiquadratic.Prime.Discriminants
public import Mathlib.Data.Int.NatAbs
public import Mathlib.RingTheory.Int.Basic

/-!
# Square-class independence of prime discriminants

The genus-field layer of the multiquadratic roadmap builds the genus field of `ℚ(√d)` as the
compositum of the quadratic fields `ℚ(√D*)` over the **prime discriminants** `D*` dividing the
discriminant of `ℚ(√d)`. To know this compositum is multiquadratic of full degree `2ᵗ` (and so
to apply the degree theorem `TauCeti.Multiquadratic.finrank_adjoin_range`), one needs the prime
discriminants to be **square-class independent**: no nonempty subset product of their radicands
is a rational square.

This file supplies that independence. The natural prime-discriminant criterion is that the family
is injective and does not contain all three even prime discriminants `-4`, `8`, and `-8`: those
three radicands multiply to the square `4`, while every proper subfamily of the even radicands is
independent. The fundamental-discriminant specialization has at most one even factor, hence
satisfies this criterion automatically.

## Main results

* `TauCeti.Multiquadratic.isCoprime_primeDiscriminantRadicand`: the radicands of two distinct
  prime discriminants are coprime except for the pair `8`, `-8`.
* `TauCeti.Multiquadratic.not_isSquare_prod_primeDiscriminantRadicands`: for an injective family
  of prime discriminants not containing all of `-4`, `8`, and `-8`, no nonempty subset product of
  their radicands is a rational square — square-class independence in the form the degree theorem
  consumes.
* `TauCeti.Multiquadratic.finrank_adjoin_roots_primeDiscriminantRadicands`: the multiquadratic
  compositum of the roots of `radicand D i` over such a family has degree `2^|ι|`.
* The `_of_forall_isEvenPrimeDiscriminant_eq` variants: the same independence and degree
  theorems under an `at most one even prime discriminant` hypothesis.
-/

public section

open scoped Function

namespace TauCeti.Multiquadratic

/-- Products over odd prime-discriminant radicands, with no `-4` radicand, are not `-1`. -/
private theorem prod_primeDiscriminantRadicands_ne_neg_one {ι : Type*} {D : ι → ℤ}
    (hD : ∀ i, IsPrimeDiscriminant (D i)) {S : Finset ι}
    (hno_neg_four : ∀ i ∈ S, D i ≠ -4) :
    (∏ i ∈ S, primeDiscriminantRadicand (D i)) ≠ -1 := by
  classical
  intro hprod
  by_cases hS : S.Nonempty
  · have hnp := map_prod Int.natAbsHom (fun i => primeDiscriminantRadicand (D i)) S
    simp only [Int.natAbsHom_apply] at hnp
    have habs : ∏ i ∈ S, (primeDiscriminantRadicand (D i)).natAbs = 1 := by
      rw [← hnp, hprod]
      norm_num
    have hall : ∀ i ∈ S, (primeDiscriminantRadicand (D i)).natAbs = 1 :=
      (Finset.prod_eq_one_iff).mp habs
    obtain ⟨i, hi⟩ := hS
    exact hno_neg_four i hi ((primeDiscriminantRadicand_natAbs_eq_one_iff (hD i)).mp
      (hall i hi))
  · rw [Finset.not_nonempty_iff_eq_empty.mp hS] at hprod
    norm_num at hprod

/-- Products over prime-discriminant radicands are squarefree when the selected radicands are
pairwise coprime. -/
private theorem squarefree_prod_primeDiscriminantRadicands_of_pairwise_isCoprime {ι : Type*}
    {D : ι → ℤ} (hD : ∀ i, IsPrimeDiscriminant (D i)) {S : Finset ι}
    (hcop : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      IsCoprime (primeDiscriminantRadicand (D i)) (primeDiscriminantRadicand (D j))) :
    Squarefree (∏ i ∈ S, primeDiscriminantRadicand (D i)) :=
  Finset.squarefree_prod_of_pairwise_isCoprime
    (fun i hi j hj hij => (hcop i hi j hj hij).isRelPrime)
    (fun i _ => squarefree_primeDiscriminantRadicand (hD i))

/-- Products over pairwise coprime prime-discriminant radicands are not rational squares, provided
the selected product is not the empty product in disguise. -/
private theorem not_isSquare_prod_primeDiscriminantRadicands_of_pairwise_isCoprime {ι : Type*}
    {D : ι → ℤ} (hD : ∀ i, IsPrimeDiscriminant (D i)) {S : Finset ι}
    (hcop : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      IsCoprime (primeDiscriminantRadicand (D i)) (primeDiscriminantRadicand (D j)))
    (hne_one : (∏ i ∈ S, primeDiscriminantRadicand (D i)) ≠ 1) :
    ¬ IsSquare (∏ i ∈ S, ((primeDiscriminantRadicand (D i) : ℤ) : ℚ)) := by
  rw [← Int.cast_prod]
  exact not_isSquare_intCast_of_squarefree_of_ne_one
    (squarefree_prod_primeDiscriminantRadicands_of_pairwise_isCoprime hD hcop) hne_one

/-- A product of prime-discriminant radicands is not `1` as soon as the discriminant family is
injective and the selected set is nonempty. -/
private theorem prod_primeDiscriminantRadicands_ne_one_of_nonempty {ι : Type*} {D : ι → ℤ}
    (hD : ∀ i, IsPrimeDiscriminant (D i)) (hinj : Function.Injective D) {S : Finset ι}
    (hS : S.Nonempty) :
    (∏ i ∈ S, primeDiscriminantRadicand (D i)) ≠ 1 := by
  intro hP
  have hnp := map_prod Int.natAbsHom (fun i => primeDiscriminantRadicand (D i)) S
  simp only [Int.natAbsHom_apply] at hnp
  have habs : ∏ i ∈ S, (primeDiscriminantRadicand (D i)).natAbs = 1 := by
    rw [← hnp, hP, Int.natAbs_one]
  have hall : ∀ i ∈ S, (primeDiscriminantRadicand (D i)).natAbs = 1 :=
    (Finset.prod_eq_one_iff).mp habs
  have hallD : ∀ i ∈ S, D i = -4 := fun i hi =>
    (primeDiscriminantRadicand_natAbs_eq_one_iff (hD i)).mp (hall i hi)
  obtain ⟨i₀, hi₀⟩ := hS
  have hsingle : S = {i₀} :=
    Finset.eq_singleton_iff_unique_mem.mpr
      ⟨hi₀, fun x hx => hinj (by rw [hallD x hx, hallD i₀ hi₀])⟩
  rw [hsingle, Finset.prod_singleton, hallD i₀ hi₀, primeDiscriminantRadicand_neg_four] at hP
  exact absurd hP (by decide)

/-!
The first block of private helpers above is intentionally local to this file; the public API starts
with the coprimality theorem below.
-/

/-- **Coprimality of distinct prime-discriminant radicands.** The radicands of two distinct prime
discriminants are coprime except for the ordered exceptional pairs `8`, `-8` and `-8`, `8`.
Their absolute values are `1`, `2` (the even radicands), or distinct odd primes (the odd ones);
the only non-coprime distinct even radicands are `2` and `-2`. -/
theorem isCoprime_primeDiscriminantRadicand {D E : ℤ}
    (hD : IsPrimeDiscriminant D) (hE : IsPrimeDiscriminant E) (hDE : D ≠ E)
    (hnot : ¬ ((D = 8 ∧ E = -8) ∨ (D = -8 ∧ E = 8))) :
    IsCoprime (primeDiscriminantRadicand D) (primeDiscriminantRadicand E) := by
  rw [Int.isCoprime_iff_nat_coprime]
  rcases isPrimeDiscriminant_iff.mp hD with hevD | ⟨p, hp, hpodd, rfl⟩
  · rcases isPrimeDiscriminant_iff.mp hE with hevE | ⟨q, hq, hqodd, rfl⟩
    · rcases hevD with rfl | rfl | rfl <;> rcases hevE with rfl | rfl | rfl <;>
        simp_all
    · rw [primeDiscriminantRadicand_of_isEvenPrimeDiscriminant hevD,
        primeDiscriminantRadicand_oddPrimeDiscriminant hqodd, oddPrimeDiscriminant_natAbs]
      rcases evenPrimeDiscriminantRadicand_natAbs_eq_one_or_two hevD with h1 | h2
      · rw [h1]; exact Nat.coprime_one_left q
      · rw [h2]; exact Nat.coprime_two_left.mpr hqodd
  · rcases isPrimeDiscriminant_iff.mp hE with hevE | ⟨q, hq, hqodd, rfl⟩
    · rw [primeDiscriminantRadicand_oddPrimeDiscriminant hpodd, oddPrimeDiscriminant_natAbs,
        primeDiscriminantRadicand_of_isEvenPrimeDiscriminant hevE]
      rcases evenPrimeDiscriminantRadicand_natAbs_eq_one_or_two hevE with h1 | h2
      · rw [h1]; exact Nat.coprime_one_right p
      · rw [h2]; exact Nat.coprime_two_right.mpr hpodd
    · rw [primeDiscriminantRadicand_oddPrimeDiscriminant hpodd,
        primeDiscriminantRadicand_oddPrimeDiscriminant hqodd, oddPrimeDiscriminant_natAbs,
        oddPrimeDiscriminant_natAbs]
      exact (Nat.coprime_primes hp hq).mpr fun h => hDE (by rw [h])

/-- Square-class independence in the exceptional even case where `S` carries indices for both `8`
and `-8` but none for `-4`: the product of the radicands `primeDiscriminantRadicand (D i)` over `S`
is not a rational square. -/
private theorem not_isSquare_prod_primeDiscriminantRadicands_of_mem_eight_neg_eight {ι : Type*}
    {D : ι → ℤ} (hD : ∀ i, IsPrimeDiscriminant (D i)) (hinj : Function.Injective D)
    {S : Finset ι} (hno4S : ∀ i ∈ S, D i ≠ -4)
    (hboth : (∃ i ∈ S, D i = 8) ∧ (∃ i ∈ S, D i = -8)) :
    ¬ IsSquare (∏ i ∈ S, ((primeDiscriminantRadicand (D i) : ℤ) : ℚ)) := by
  classical
  obtain ⟨⟨i8, hi8S, hi8D⟩, im8, him8S, him8D⟩ := hboth
  have hne : i8 ≠ im8 := by rintro rfl; omega
  let T := (S.erase i8).erase im8
  let P : ℤ := ∏ i ∈ T, primeDiscriminantRadicand (D i)
  have him8_erase : im8 ∈ S.erase i8 := Finset.mem_erase.mpr ⟨hne.symm, him8S⟩
  have hprod_int : (∏ i ∈ S, primeDiscriminantRadicand (D i)) = -4 * P := by
    rw [← Finset.mul_prod_erase S (fun i => primeDiscriminantRadicand (D i)) hi8S,
      ← Finset.mul_prod_erase (S.erase i8) (fun i => primeDiscriminantRadicand (D i))
        him8_erase]
    simp [P, T, hi8D, him8D]
    ring
  have hcopT : ∀ i ∈ T, ∀ j ∈ T, i ≠ j →
      IsCoprime (primeDiscriminantRadicand (D i)) (primeDiscriminantRadicand (D j)) := by
    intro i hiT j hjT hij
    exact isCoprime_primeDiscriminantRadicand (hD i) (hD j) (fun h => hij (hinj h))
      (by
        intro hbad
        rcases hbad with ⟨hi, hj⟩ | ⟨hi, hj⟩
        · exact Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hiT)
            (hinj (by rw [hi, hi8D]))
        · exact Finset.ne_of_mem_erase hiT (hinj (by rw [hi, him8D])))
  have hne_negP : -P ≠ 1 := by
    intro hneg
    have hP : P = -1 := by omega
    exact prod_primeDiscriminantRadicands_ne_neg_one hD
      (fun i hi => hno4S i (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hi))) hP
  have hnot_negP : ¬ IsSquare (((-P : ℤ) : ℚ)) :=
    not_isSquare_intCast_of_squarefree_of_ne_one
      (squarefree_prod_primeDiscriminantRadicands_of_pairwise_isCoprime hD hcopT).neg hne_negP
  intro hsquare
  have hfour : IsSquare (4 * ((-P : ℤ) : ℚ)) := by
    convert hsquare using 1
    rw [← Int.cast_prod, hprod_int]
    norm_num
  have hdiv := hfour.div (⟨2, by norm_num⟩ : IsSquare (4 : ℚ))
  rw [mul_div_cancel_left₀ _ (by norm_num : (4 : ℚ) ≠ 0)] at hdiv
  exact hnot_negP hdiv

/-- **Square-class independence of prime discriminants.** Let `D : ι → ℤ` be an injective family
of prime discriminants which does not contain all three even prime discriminants `-4`, `8`, and
`-8`. Then no nonempty subset product of the radicands `primeDiscriminantRadicand (D i)` is a
rational square. This is the `hindep` hypothesis the multiquadratic degree theorem
`finrank_adjoin_range` consumes, applied to the genus-field generators. -/
theorem not_isSquare_prod_primeDiscriminantRadicands {ι : Type*} (D : ι → ℤ)
    (hD : ∀ i, IsPrimeDiscriminant (D i)) (hinj : Function.Injective D)
    (heven : ¬ ((∃ i, D i = -4) ∧ (∃ i, D i = 8) ∧ (∃ i, D i = -8))) :
    ∀ S : Finset ι, S.Nonempty →
      ¬ IsSquare (∏ i ∈ S, ((primeDiscriminantRadicand (D i) : ℤ) : ℚ)) := by
  intro S hS
  by_cases hboth : (∃ i ∈ S, D i = 8) ∧ (∃ i ∈ S, D i = -8)
  · refine not_isSquare_prod_primeDiscriminantRadicands_of_mem_eight_neg_eight hD hinj ?_ hboth
    exact fun i _ hiD => heven ⟨⟨i, hiD⟩, hboth.1.imp fun _ h => h.2, hboth.2.imp fun _ h => h.2⟩
  · refine not_isSquare_prod_primeDiscriminantRadicands_of_pairwise_isCoprime hD ?_
      (prod_primeDiscriminantRadicands_ne_one_of_nonempty hD hinj hS)
    intro i hi j hj hij
    exact isCoprime_primeDiscriminantRadicand (hD i) (hD j) (fun h => hij (hinj h))
      (by
        intro hbad
        rcases hbad with ⟨hi8, hjm8⟩ | ⟨him8, hj8⟩
        · exact hboth ⟨⟨i, hi, hi8⟩, ⟨j, hj, hjm8⟩⟩
        · exact hboth ⟨⟨j, hj, hj8⟩, ⟨i, hi, him8⟩⟩)

/-- A prime-discriminant family with at most one even prime discriminant cannot contain the three
even prime discriminants `-4`, `8`, and `-8` simultaneously.

The hypothesis is stated extensionally: any two indices whose discriminants are even prime
discriminants must carry the same discriminant value. This is the form supplied by the
prime-discriminant factorization of a quadratic discriminant, where there is only one 2-adic
factor. -/
theorem not_all_three_evenPrimeDiscriminants_of_forall_isEvenPrimeDiscriminant_eq {ι : Type*}
    {D : ι → ℤ}
    (heven_unique : ∀ i j,
      IsEvenPrimeDiscriminant (D i) → IsEvenPrimeDiscriminant (D j) → D i = D j) :
    ¬ ((∃ i, D i = -4) ∧ (∃ i, D i = 8) ∧ (∃ i, D i = -8)) := by
  rintro ⟨⟨i4, hi4⟩, ⟨i8, hi8⟩, _⟩
  have hD : D i4 = D i8 :=
    heven_unique i4 i8 (hi4.symm ▸ isEvenPrimeDiscriminant_neg_four)
      (hi8.symm ▸ isEvenPrimeDiscriminant_eight)
  omega

/-- **Square-class independence for prime-discriminant families with at most one even factor.**
Let `D : ι → ℤ` be an injective family of prime discriminants, and assume any two even prime
discriminants in the family are equal as integers. Then no nonempty subset product of the
associated radicands `primeDiscriminantRadicand (D i)` is a rational square.

This is the genus-field specialization of
`not_isSquare_prod_primeDiscriminantRadicands`: the prime discriminants dividing a quadratic
discriminant have at most one even member, so the exceptional product
`(-1) * 2 * (-2) = 4` cannot occur. -/
theorem not_isSquare_prod_primeDiscriminantRadicands_of_forall_isEvenPrimeDiscriminant_eq
    {ι : Type*} (D : ι → ℤ) (hD : ∀ i, IsPrimeDiscriminant (D i))
    (hinj : Function.Injective D)
    (heven_unique : ∀ i j,
      IsEvenPrimeDiscriminant (D i) → IsEvenPrimeDiscriminant (D j) → D i = D j) :
    ∀ S : Finset ι, S.Nonempty →
      ¬ IsSquare (∏ i ∈ S, ((primeDiscriminantRadicand (D i) : ℤ) : ℚ)) := by
  exact not_isSquare_prod_primeDiscriminantRadicands D hD hinj
    (not_all_three_evenPrimeDiscriminants_of_forall_isEvenPrimeDiscriminant_eq heven_unique)

/-- **Full degree for adjoining roots of prime-discriminant radicands.** Over any field `L ⊇ ℚ`
carrying square roots `root i` of the radicands of an injective family of prime discriminants not
containing all three even prime discriminants, the compositum `ℚ(root i : i)` has degree `2^|ι|`.
In a later genus-field specialization, the chosen roots will be identified with the genus-field
generators. This is the prime-discriminant instance of `finrank_adjoin_range`, fed the
square-class independence `not_isSquare_prod_primeDiscriminantRadicands`. -/
theorem finrank_adjoin_roots_primeDiscriminantRadicands {ι : Type*} [Finite ι]
    {L : Type*} [Field L] [Algebra ℚ L] (D : ι → ℤ)
    (hD : ∀ i, IsPrimeDiscriminant (D i)) (hinj : Function.Injective D)
    (heven : ¬ ((∃ i, D i = -4) ∧ (∃ i, D i = 8) ∧ (∃ i, D i = -8)))
    (root : ι → L)
    (hroot : ∀ i, root i ^ 2 = algebraMap ℚ L ((primeDiscriminantRadicand (D i) : ℤ) : ℚ)) :
    Module.finrank ℚ (IntermediateField.adjoin ℚ (Set.range root)) = 2 ^ Nat.card ι :=
  finrank_adjoin_range hroot
    (not_isSquare_prod_primeDiscriminantRadicands D hD hinj heven)

/-- **Full degree for adjoining roots of prime-discriminant radicands with at most one even
factor.** If `D : ι → ℤ` is an injective finite family of prime discriminants with at most one
even member, then adjoining square roots of the associated radicands gives a multiquadratic field
of degree `2 ^ Nat.card ι`.

This is the degree theorem in the form needed for genus-field generator lists coming from prime
discriminants of a quadratic discriminant. -/
theorem finrank_adjoin_roots_primeDiscriminantRadicands_of_forall_isEvenPrimeDiscriminant_eq
    {ι : Type*} [Finite ι] {L : Type*} [Field L] [Algebra ℚ L] (D : ι → ℤ)
    (hD : ∀ i, IsPrimeDiscriminant (D i)) (hinj : Function.Injective D)
    (heven_unique : ∀ i j,
      IsEvenPrimeDiscriminant (D i) → IsEvenPrimeDiscriminant (D j) → D i = D j)
    (root : ι → L)
    (hroot : ∀ i, root i ^ 2 = algebraMap ℚ L ((primeDiscriminantRadicand (D i) : ℤ) : ℚ)) :
    Module.finrank ℚ (IntermediateField.adjoin ℚ (Set.range root)) = 2 ^ Nat.card ι :=
  finrank_adjoin_roots_primeDiscriminantRadicands D hD hinj
    (not_all_three_evenPrimeDiscriminants_of_forall_isEvenPrimeDiscriminant_eq heven_unique) root
    hroot

/-- **Worked example.** The prime discriminants `-4` and `5` divide the discriminant `-20` of
`ℚ(√-5)`, and are its genus-field generators (`ℚ(√-5)` has genus field `ℚ(√-1, √5)`). They are
square-class independent: no nonempty subset product of their radicands `-1` and `5` is a
rational square. -/
example : ∀ S : Finset (Fin 2), S.Nonempty →
    ¬ IsSquare (∏ i ∈ S, ((primeDiscriminantRadicand (![(-4 : ℤ), 5] i) : ℤ) : ℚ)) := by
  refine not_isSquare_prod_primeDiscriminantRadicands _ (fun i => ?_) (fun a b h => ?_)
    ?_
  · fin_cases i
    · simp
    · have h5 : IsPrimeDiscriminant (5 : ℤ) := by
        have hoddDisc : oddPrimeDiscriminant 5 = (5 : ℤ) :=
          oddPrimeDiscriminant_of_mod_four_eq_one (by norm_num)
        rw [← hoddDisc]
        exact isPrimeDiscriminant_oddPrimeDiscriminant (by decide) (by decide)
      simpa using h5
  · fin_cases a <;> fin_cases b <;> simp_all
  · simp

end TauCeti.Multiquadratic
