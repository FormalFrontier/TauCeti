/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.Squarefree
public import TauCeti.NumberTheory.Multiquadratic.EvenPrimeDiscriminant
public import TauCeti.NumberTheory.Multiquadratic.Prime.Discriminant.Basic
public import Mathlib.Data.Rat.Lemmas
import TauCeti.NumberTheory.LegendreSymbol.SquareClass

/-!
# Prime discriminants

The genus-field layer of the multiquadratic roadmap uses the **prime discriminants**
`-4`, `8`, `-8`, and `p* = (-1)^((p - 1) / 2) p` for odd primes `p`. The files
`PrimeDiscriminant` and `EvenPrimeDiscriminant` develop the odd and 2-adic pieces separately;
this file packages them into one predicate and one radicand map for later genus-field
constructions.

For an odd prime discriminant the radicand is the discriminant itself. For an even prime
discriminant `D ∈ {-4, 8, -8}`, the radicand is `D / 4`, so the three even cases give
`-1`, `2`, and `-2`.

## Main definitions and results

* `TauCeti.Multiquadratic.IsPrimeDiscriminant`: the union of the even prime discriminants and
  odd prime discriminants.
* `TauCeti.Multiquadratic.primeDiscriminantRadicand`: the associated squarefree integer
  radicand.
* `TauCeti.Multiquadratic.dvd_primeDiscriminant_iff_dvd_radicand`: away from `2`, an integer
  and its associated radicand have the same prime divisors.
* `TauCeti.Multiquadratic.squarefree_primeDiscriminantRadicand`: the associated radicand is
  squarefree.
* `TauCeti.Multiquadratic.not_isSquare_primeDiscriminantRadicand_rat`: the associated rational
  radicand is not a square.
-/

public section

namespace TauCeti.Multiquadratic

/-- The prime discriminants: the even prime discriminants `-4`, `8`, `-8`, together with
the odd prime discriminants `p*` for odd natural primes `p`. -/
def IsPrimeDiscriminant (D : ℤ) : Prop :=
  IsEvenPrimeDiscriminant D ∨ ∃ p : ℕ, p.Prime ∧ Odd p ∧ D = oddPrimeDiscriminant p

/-- The defining disjunction for `IsPrimeDiscriminant`. -/
theorem isPrimeDiscriminant_iff {D : ℤ} :
    IsPrimeDiscriminant D ↔
      IsEvenPrimeDiscriminant D ∨ ∃ p : ℕ, p.Prime ∧ Odd p ∧ D = oddPrimeDiscriminant p :=
  Iff.rfl

/-- Every even prime discriminant is a prime discriminant. -/
theorem IsEvenPrimeDiscriminant.isPrimeDiscriminant {D : ℤ} (hD : IsEvenPrimeDiscriminant D) :
    IsPrimeDiscriminant D :=
  Or.inl hD

/-- The discriminant `-4` is a prime discriminant. -/
@[simp] theorem isPrimeDiscriminant_neg_four :
    IsPrimeDiscriminant (-4) :=
  isEvenPrimeDiscriminant_neg_four.isPrimeDiscriminant

/-- The discriminant `8` is a prime discriminant. -/
@[simp] theorem isPrimeDiscriminant_eight :
    IsPrimeDiscriminant 8 :=
  isEvenPrimeDiscriminant_eight.isPrimeDiscriminant

/-- The discriminant `-8` is a prime discriminant. -/
@[simp] theorem isPrimeDiscriminant_neg_eight :
    IsPrimeDiscriminant (-8) :=
  isEvenPrimeDiscriminant_neg_eight.isPrimeDiscriminant

/-- The odd prime discriminant attached to an odd natural prime is a prime discriminant. -/
theorem isPrimeDiscriminant_oddPrimeDiscriminant {p : ℕ} (hp : p.Prime) (hodd : Odd p) :
    IsPrimeDiscriminant (oddPrimeDiscriminant p) :=
  Or.inr ⟨p, hp, hodd, rfl⟩

/-- An odd prime discriminant is not one of the even prime discriminants. -/
theorem not_isEvenPrimeDiscriminant_oddPrimeDiscriminant {p : ℕ} (hodd : Odd p) :
    ¬ IsEvenPrimeDiscriminant (oddPrimeDiscriminant p) := by
  intro hD
  have hp_ne_four : p ≠ 4 := by
    intro hp4
    have hodd4 : Odd 4 := hp4 ▸ hodd
    rcases hodd4 with ⟨k, hk⟩
    omega
  have hp_ne_eight : p ≠ 8 := by
    intro hp8
    have hodd8 : Odd 8 := hp8 ▸ hodd
    rcases hodd8 with ⟨k, hk⟩
    omega
  rcases hD with hD | hD | hD
  · have hnat : p = 4 := by
      simpa [oddPrimeDiscriminant_natAbs] using congrArg Int.natAbs hD
    exact hp_ne_four hnat
  · have hnat : p = 8 := by
      simpa [oddPrimeDiscriminant_natAbs] using congrArg Int.natAbs hD
    exact hp_ne_eight hnat
  · have hnat : p = 8 := by
      simpa [oddPrimeDiscriminant_natAbs] using congrArg Int.natAbs hD
    exact hp_ne_eight hnat

/-- The squarefree radicand attached to a prime discriminant. In the even cases this divides by
`4`; in the odd cases the discriminant is already squarefree and is used as its own radicand. -/
@[expose] def primeDiscriminantRadicand (D : ℤ) : ℤ :=
  if D = -4 ∨ D = 8 ∨ D = -8 then evenPrimeDiscriminantRadicand D else D

/-- The defining equation for the prime-discriminant radicand. -/
theorem primeDiscriminantRadicand_def (D : ℤ) :
    primeDiscriminantRadicand D =
      if D = -4 ∨ D = 8 ∨ D = -8 then evenPrimeDiscriminantRadicand D else D :=
  rfl

/-- The prime-discriminant radicand of `-4` is `-1`. -/
theorem primeDiscriminantRadicand_neg_four :
    primeDiscriminantRadicand (-4) = -1 := by
  simp [primeDiscriminantRadicand]

/-- The prime-discriminant radicand of `8` is `2`. -/
theorem primeDiscriminantRadicand_eight :
    primeDiscriminantRadicand 8 = 2 := by
  simp [primeDiscriminantRadicand]

/-- The prime-discriminant radicand of `-8` is `-2`. -/
theorem primeDiscriminantRadicand_neg_eight :
    primeDiscriminantRadicand (-8) = -2 := by
  simp [primeDiscriminantRadicand]

/-- The radicand attached to an even prime discriminant is its even-prime radicand. -/
@[simp]
theorem primeDiscriminantRadicand_of_isEvenPrimeDiscriminant {D : ℤ}
    (hD : IsEvenPrimeDiscriminant D) :
    primeDiscriminantRadicand D = evenPrimeDiscriminantRadicand D := by
  rcases hD with rfl | rfl | rfl <;> simp [primeDiscriminantRadicand]

/-- The radicand attached to an odd prime discriminant is the discriminant itself. -/
@[simp]
theorem primeDiscriminantRadicand_oddPrimeDiscriminant {p : ℕ} (hodd : Odd p) :
    primeDiscriminantRadicand (oddPrimeDiscriminant p) = oddPrimeDiscriminant p := by
  have hnot : ¬ (oddPrimeDiscriminant p = -4 ∨
      oddPrimeDiscriminant p = 8 ∨ oddPrimeDiscriminant p = -8) := by
    simpa [IsEvenPrimeDiscriminant] using not_isEvenPrimeDiscriminant_oddPrimeDiscriminant hodd
  simp [primeDiscriminantRadicand, hnot]

/-- A prime discriminant is either its own radicand, or four times its radicand in the even
cases. -/
theorem primeDiscriminant_eq_radicand_or_eq_four_mul_radicand {D : ℤ} (hD : IsPrimeDiscriminant D) :
    D = primeDiscriminantRadicand D ∨ D = 4 * primeDiscriminantRadicand D := by
  rcases hD with hD | ⟨p, _hp, hodd, rfl⟩
  · exact Or.inr <| by
      rw [primeDiscriminantRadicand_of_isEvenPrimeDiscriminant hD]
      exact evenPrimeDiscriminant_eq_four_mul_radicand hD
  · exact Or.inl <| by rw [primeDiscriminantRadicand_oddPrimeDiscriminant hodd]

variable {q : ℕ} [Fact q.Prime]

/-- Away from `2`, divisibility of an integer is the same as divisibility of its associated
prime-discriminant radicand. In the even-prime cases the two differ by the square factor
`4`; in all other cases they are equal. Not a `simp` lemma: the right-hand side is again of
the form `(q : ℤ) ∣ _`, so as a rewrite rule it matches its own output and loops. -/
theorem dvd_primeDiscriminant_iff_dvd_radicand (D : ℤ) (hq : q ≠ 2) :
    (q : ℤ) ∣ D ↔ (q : ℤ) ∣ primeDiscriminantRadicand D := by
  have hq2 : ¬ (q : ℤ) ∣ (2 : ℤ) := by
    intro hdiv
    have hdiv_nat : q ∣ 2 := by exact_mod_cast hdiv
    exact hq ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp hdiv_nat)
  rcases eq_or_ne D (-4) with rfl | hneg4
  · simpa [pow_two] using (TauCeti.dvd_mul_sq_iff (p := q) (a := (-1 : ℤ)) (u := 2) hq2)
  rcases eq_or_ne D 8 with rfl | h8
  · simpa [pow_two] using (TauCeti.dvd_mul_sq_iff (p := q) (a := (2 : ℤ)) (u := 2) hq2)
  rcases eq_or_ne D (-8) with rfl | hneg8
  · simpa [pow_two] using (TauCeti.dvd_mul_sq_iff (p := q) (a := (-2 : ℤ)) (u := 2) hq2)
  · simp [primeDiscriminantRadicand, hneg4, h8, hneg8]

/-- Away from `2`, an indexed family of integers and its associated prime-discriminant
radicands have the same unramifiedness condition at `q`. -/
theorem forall_not_dvd_primeDiscriminant_iff_radicand {ι : Type*} (D : ι → ℤ) (hq : q ≠ 2) :
    (∀ i, ¬ (q : ℤ) ∣ D i) ↔
      ∀ i, ¬ (q : ℤ) ∣ primeDiscriminantRadicand (D i) := by
  refine forall_congr' fun i => ?_
  exact not_congr (dvd_primeDiscriminant_iff_dvd_radicand (q := q) (D i) hq)

/-- The radicand attached to a prime discriminant is nonzero. -/
theorem primeDiscriminantRadicand_ne_zero {D : ℤ} (hD : IsPrimeDiscriminant D) :
    primeDiscriminantRadicand D ≠ 0 := by
  rcases hD with hD | ⟨p, hp, hodd, rfl⟩
  · rw [primeDiscriminantRadicand_of_isEvenPrimeDiscriminant hD]
    exact evenPrimeDiscriminantRadicand_ne_zero hD
  · rw [primeDiscriminantRadicand_oddPrimeDiscriminant hodd]
    exact (oddPrimeDiscriminant_ne_zero).2 hp.ne_zero

/-- The radicand attached to a prime discriminant is squarefree. -/
theorem squarefree_primeDiscriminantRadicand {D : ℤ} (hD : IsPrimeDiscriminant D) :
    Squarefree (primeDiscriminantRadicand D) := by
  rcases hD with hD | ⟨p, hp, hodd, rfl⟩
  · rw [primeDiscriminantRadicand_of_isEvenPrimeDiscriminant hD]
    exact squarefree_evenPrimeDiscriminantRadicand hD
  · rw [primeDiscriminantRadicand_oddPrimeDiscriminant hodd]
    exact squarefree_oddPrimeDiscriminant hp.squarefree

/-- The radicand attached to a prime discriminant is not a rational square. -/
theorem not_isSquare_primeDiscriminantRadicand_rat {D : ℤ} (hD : IsPrimeDiscriminant D) :
    ¬ IsSquare ((primeDiscriminantRadicand D : ℤ) : ℚ) := by
  rcases hD with hD | ⟨p, hp, hodd, rfl⟩
  · rw [primeDiscriminantRadicand_of_isEvenPrimeDiscriminant hD]
    exact not_isSquare_evenPrimeDiscriminantRadicand_rat hD
  · rw [primeDiscriminantRadicand_oddPrimeDiscriminant hodd]
    rw [Rat.isSquare_intCast_iff]
    exact (squarefree_oddPrimeDiscriminant hp.squarefree).not_isSquare
      (by
        rw [Int.isUnit_iff_natAbs_eq]
        simpa [oddPrimeDiscriminant_natAbs] using hp.ne_one)

/-- An odd prime discriminant has odd radicand congruent to `1` modulo `4`. -/
theorem primeDiscriminantRadicand_mod_four_eq_one_of_odd {p : ℕ} (hodd : Odd p) :
    primeDiscriminantRadicand (oddPrimeDiscriminant p) % 4 = 1 := by
  rw [primeDiscriminantRadicand_oddPrimeDiscriminant hodd]
  exact oddPrimeDiscriminant_mod_four_eq_one hodd

/-- An even prime discriminant has radicand congruent to `3` or `2` modulo `4`. -/
theorem primeDiscriminantRadicand_mod_four_eq_three_or_two_of_even {D : ℤ}
    (hD : IsEvenPrimeDiscriminant D) :
    primeDiscriminantRadicand D % 4 = 3 ∨ primeDiscriminantRadicand D % 4 = 2 := by
  rw [primeDiscriminantRadicand_of_isEvenPrimeDiscriminant hD]
  exact evenPrimeDiscriminantRadicand_mod_four_eq_three_or_two hD

/-- A prime discriminant is either even, or its associated radicand is congruent to `1`
modulo `4`. -/
theorem isEvenPrimeDiscriminant_or_primeDiscriminantRadicand_mod_four_eq_one {D : ℤ}
    (hD : IsPrimeDiscriminant D) :
    IsEvenPrimeDiscriminant D ∨ primeDiscriminantRadicand D % 4 = 1 := by
  rcases isPrimeDiscriminant_iff.mp hD with hD | ⟨p, hp, hodd, rfl⟩
  · exact Or.inl hD
  · exact Or.inr (primeDiscriminantRadicand_mod_four_eq_one_of_odd hodd)

/-- The only prime discriminant whose radicand has absolute value `1` is `-4`. This is the
small exceptional case in the radicand map: the odd prime-discriminant radicands have prime
absolute value, and the other even prime-discriminant radicands have absolute value `2`. -/
theorem primeDiscriminantRadicand_natAbs_eq_one_iff {D : ℤ} (hD : IsPrimeDiscriminant D) :
    (primeDiscriminantRadicand D).natAbs = 1 ↔ D = -4 := by
  constructor
  · intro h
    rcases isPrimeDiscriminant_iff.mp hD with hev | ⟨p, hp, hodd, rfl⟩
    · rw [primeDiscriminantRadicand_of_isEvenPrimeDiscriminant hev] at h
      rcases hev with rfl | rfl | rfl
      · rfl
      · norm_num at h
      · norm_num at h
    · rw [primeDiscriminantRadicand_oddPrimeDiscriminant hodd,
        oddPrimeDiscriminant_natAbs] at h
      exact False.elim (hp.ne_one h)
  · intro h
    rw [h, primeDiscriminantRadicand_neg_four]
    norm_num

/-- Among prime discriminants, radicand `-1` comes only from the even prime discriminant
`-4`. -/
theorem primeDiscriminantRadicand_eq_neg_one_iff {D : ℤ} (hD : IsPrimeDiscriminant D) :
    primeDiscriminantRadicand D = -1 ↔ D = -4 := by
  constructor
  · intro h
    exact (primeDiscriminantRadicand_natAbs_eq_one_iff hD).mp (by rw [h]; norm_num)
  · intro h
    rw [h, primeDiscriminantRadicand_neg_four]

/-- Among prime discriminants, radicand `2` comes only from the even prime discriminant `8`. -/
theorem primeDiscriminantRadicand_eq_two_iff {D : ℤ} (hD : IsPrimeDiscriminant D) :
    primeDiscriminantRadicand D = 2 ↔ D = 8 := by
  constructor
  · intro h
    rcases isPrimeDiscriminant_iff.mp hD with hev | ⟨p, hp, hodd, rfl⟩
    · rw [primeDiscriminantRadicand_of_isEvenPrimeDiscriminant hev] at h
      exact (evenPrimeDiscriminantRadicand_eq_two_iff hev).mp h
    · have hp2 : p = 2 := by
        simpa [primeDiscriminantRadicand_oddPrimeDiscriminant hodd,
          oddPrimeDiscriminant_natAbs] using congrArg Int.natAbs h
      rcases hodd with ⟨k, hk⟩
      omega
  · intro h
    rw [h, primeDiscriminantRadicand_eight]

/-- Among prime discriminants, radicand `-2` comes only from the even prime discriminant
`-8`. -/
theorem primeDiscriminantRadicand_eq_neg_two_iff {D : ℤ} (hD : IsPrimeDiscriminant D) :
    primeDiscriminantRadicand D = -2 ↔ D = -8 := by
  constructor
  · intro h
    rcases isPrimeDiscriminant_iff.mp hD with hev | ⟨p, hp, hodd, rfl⟩
    · rw [primeDiscriminantRadicand_of_isEvenPrimeDiscriminant hev] at h
      exact (evenPrimeDiscriminantRadicand_eq_neg_two_iff hev).mp h
    · have hp2 : p = 2 := by
        simpa [primeDiscriminantRadicand_oddPrimeDiscriminant hodd,
          oddPrimeDiscriminant_natAbs] using congrArg Int.natAbs h
      rcases hodd with ⟨k, hk⟩
      omega
  · intro h
    rw [h, primeDiscriminantRadicand_neg_eight]

/-- The radicand map is injective on prime discriminants. This is the bookkeeping that lets
later genus-field code pass between a list of prime discriminants and the corresponding
multiquadratic radicands without identifying two different quadratic factors. -/
theorem eq_of_primeDiscriminantRadicand_eq {D E : ℤ}
    (hD : IsPrimeDiscriminant D) (hE : IsPrimeDiscriminant E)
    (h : primeDiscriminantRadicand D = primeDiscriminantRadicand E) :
    D = E := by
  rcases isPrimeDiscriminant_iff.mp hD with hevD | ⟨p, hp, hpodd, rfl⟩
  · rcases isPrimeDiscriminant_iff.mp hE with hevE | ⟨q, hq, hqodd, rfl⟩
    · rcases hevD with rfl | rfl | rfl
      · have hE' : E = -4 :=
          (primeDiscriminantRadicand_eq_neg_one_iff (Or.inl hevE)).mp (by simpa using h.symm)
        rw [hE']
      · have hE' : E = 8 :=
          (primeDiscriminantRadicand_eq_two_iff (Or.inl hevE)).mp (by simpa using h.symm)
        rw [hE']
      · have hE' : E = -8 :=
          (primeDiscriminantRadicand_eq_neg_two_iff (Or.inl hevE)).mp (by simpa using h.symm)
        rw [hE']
    · have habs := congrArg Int.natAbs h
      rw [primeDiscriminantRadicand_of_isEvenPrimeDiscriminant hevD,
        primeDiscriminantRadicand_oddPrimeDiscriminant hqodd,
        oddPrimeDiscriminant_natAbs] at habs
      rcases evenPrimeDiscriminantRadicand_natAbs_eq_one_or_two hevD with h1 | h2
      · rw [h1] at habs
        exact False.elim (hq.ne_one habs.symm)
      · rw [h2] at habs
        rcases hqodd with ⟨k, hk⟩
        omega
  · rcases isPrimeDiscriminant_iff.mp hE with hevE | ⟨q, hq, hqodd, rfl⟩
    · have habs := congrArg Int.natAbs h
      rw [primeDiscriminantRadicand_oddPrimeDiscriminant hpodd,
        primeDiscriminantRadicand_of_isEvenPrimeDiscriminant hevE,
        oddPrimeDiscriminant_natAbs] at habs
      rcases evenPrimeDiscriminantRadicand_natAbs_eq_one_or_two hevE with h1 | h2
      · rw [h1] at habs
        exact False.elim (hp.ne_one habs)
      · rw [h2] at habs
        rcases hpodd with ⟨k, hk⟩
        omega
    · rw [primeDiscriminantRadicand_oddPrimeDiscriminant hpodd,
        primeDiscriminantRadicand_oddPrimeDiscriminant hqodd] at h
      have hpq : p = q := by
        simpa [oddPrimeDiscriminant_natAbs] using congrArg Int.natAbs h
      rw [hpq]

/-- `primeDiscriminantRadicand` is injective on the set of prime discriminants. -/
theorem injOn_primeDiscriminantRadicand :
    Set.InjOn primeDiscriminantRadicand {D : ℤ | IsPrimeDiscriminant D} := by
  intro D hD E hE h
  exact eq_of_primeDiscriminantRadicand_eq hD hE h

/-- For a family of prime discriminants, injectivity is unchanged after replacing each
discriminant by its multiquadratic radicand. -/
theorem injective_primeDiscriminantRadicand_comp_iff {ι : Type*} {D : ι → ℤ}
    (hD : ∀ i, IsPrimeDiscriminant (D i)) :
    Function.Injective (fun i => primeDiscriminantRadicand (D i)) ↔
      Function.Injective D := by
  simpa only [Function.comp_def] using
    (Set.InjOn.injective_iff {D : ℤ | IsPrimeDiscriminant D} injOn_primeDiscriminantRadicand
      (by rintro _ ⟨i, rfl⟩; exact hD i))

end TauCeti.Multiquadratic
