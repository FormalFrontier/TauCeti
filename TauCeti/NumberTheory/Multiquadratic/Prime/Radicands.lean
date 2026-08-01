/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.Squarefree
public import TauCeti.NumberTheory.Multiquadratic.Degree
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Rat.Lemmas
public import Mathlib.Data.Nat.Squarefree

/-!
# Multiquadratic fields with prime radicands

The field-generic degree theorem `TauCeti.Multiquadratic.finrank_adjoin_range` says that a
multiquadratic field has degree `2ⁿ` once the radicands are **square-class independent**: no
nonempty subset product of them is a square. This file supplies that hypothesis for the most
common concrete source of square-class independent radicands — a family of **distinct primes** —
and so derives the prime-indexed degree corollary `[ℚ(√p₁, …, √pₙ) : ℚ] = 2ⁿ` (a genus-theory
input) and the smallest non-vacuity example `[ℚ(√2, √3) : ℚ] = 4`.

The square-class independence of distinct primes is elementary: a nonempty subset product of
distinct primes is squarefree (the primes are pairwise coprime) and is not a unit (it has a prime
factor), so it is not a square.

## Main results

* `TauCeti.Multiquadratic.not_isSquare_prod_primes`: for distinct primes `p i`, no nonempty subset
  product `∏_{i ∈ S} (p i : ℚ)` is a square — square-class independence in the form the degree
  theorem consumes.
* `TauCeti.Multiquadratic.not_isSquare_prod_primes_of_injective`: the same square-class
  independence, packaged from an injective family of primes — the shape the multiquadratic degree
  and Galois-group theorems consume directly.
* `TauCeti.Multiquadratic.finrank_adjoin_sqrt_primes`: `[ℚ(√p₁, …, √pₙ) : ℚ] = 2^|ι|` for a finite
  family of distinct primes.
* `TauCeti.Multiquadratic.finrank_adjoin_sqrt_two_three`: `[ℚ(√2, √3) : ℚ] = 4`.
-/

public section

open scoped Function

namespace TauCeti.Multiquadratic

/-- **Square-class independence of distinct primes.** If the selected `p i` are prime and pairwise
distinct, then no nonempty subset product `∏_{i ∈ S} (p i : ℚ)` is a square in `ℚ`. This is the
hypothesis the multiquadratic degree theorem `finrank_adjoin_range` consumes. -/
theorem not_isSquare_prod_primes {ι : Type*} (p : ι → ℕ) {S : Finset ι} (hp : ∀ i ∈ S, (p i).Prime)
    (hdist : Set.Pairwise (S : Set ι) (fun i j => p i ≠ p j)) (hS : S.Nonempty) :
    ¬ IsSquare (∏ i ∈ S, (p i : ℚ)) := by
  rw [← Nat.cast_prod, Rat.isSquare_natCast_iff]
  refine Squarefree.not_isSquare ?_ ?_
  · refine Finset.squarefree_prod_of_pairwise_isCoprime (fun i hi j hj hij => ?_)
      (fun i hi => (hp i hi).prime.squarefree)
    exact Nat.coprime_iff_isRelPrime.mp
      ((Nat.coprime_primes (hp i hi) (hp j hj)).mpr fun h => hdist hi hj hij h)
  · rw [Nat.isUnit_iff]
    obtain ⟨i, hi⟩ := hS
    intro hprod
    exact (hp i hi).ne_one (Nat.dvd_one.mp (hprod ▸ Finset.dvd_prod_of_mem p hi))

/-- The real square root of a natural number squares back to its rational value, in the form
`(√n)² = algebraMap ℚ ℝ n`. This supplies the `hroot` hypothesis that the multiquadratic degree and
Galois-group theorems consume for the family of square roots of a prime family. It is the `0 ≤ n`
special case of `sq_sqrt_intCast`. -/
theorem sq_sqrt_natCast (n : ℕ) : (Real.sqrt n) ^ 2 = algebraMap ℚ ℝ (n : ℚ) := by
  have h := sq_sqrt_intCast (n := (n : ℤ)) (Int.natCast_nonneg n)
  rwa [Int.cast_natCast, Int.cast_natCast] at h

/-- **Square-class independence of an injective family of primes.** If `p : ι → ℕ` is injective and
each `p i` is prime, then no nonempty subset product `∏_{i ∈ S} (p i : ℚ)` is a square. This is the
`hindep` hypothesis the multiquadratic degree and Galois-group theorems consume directly. -/
theorem not_isSquare_prod_primes_of_injective {ι : Type*} (p : ι → ℕ)
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p) :
    ∀ S : Finset ι, S.Nonempty → ¬ IsSquare (∏ i ∈ S, (p i : ℚ)) :=
  fun _ hS => not_isSquare_prod_primes p (fun i _ => hp i)
    (fun _ _ _ _ hij h => hij (hinj h)) hS

/-- **Degree of a prime-radicand multiquadratic field.** For a finite family of distinct primes
`p : ι → ℕ`, the field generated over `ℚ` by their real square roots has degree `2^|ι|`. This is the
prime-indexed corollary of the field-generic degree theorem `finrank_adjoin_range`. -/
theorem finrank_adjoin_sqrt_primes {ι : Type*} [Finite ι] (p : ι → ℕ)
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p) :
    Module.finrank ℚ
        (IntermediateField.adjoin ℚ (Set.range fun i => (Real.sqrt (p i) : ℝ)))
      = 2 ^ Nat.card ι :=
  finrank_adjoin_range (d := fun i => (p i : ℚ)) (root := fun i => Real.sqrt (p i))
    (fun i => sq_sqrt_natCast (p i)) (not_isSquare_prod_primes_of_injective p hp hinj)

/-- **Worked example: `[ℚ(√2, √3) : ℚ] = 4`.** The smallest nontrivial multiquadratic degree,
obtained from `finrank_adjoin_sqrt_primes` with the primes `2` and `3`. -/
theorem finrank_adjoin_sqrt_two_three :
    Module.finrank ℚ
      (IntermediateField.adjoin ℚ {Real.sqrt 2, Real.sqrt 3} : IntermediateField ℚ ℝ) = 4 := by
  have h := finrank_adjoin_sqrt_primes ![2, 3] (by decide) (by decide)
  have hset : (Set.range fun i : Fin 2 => Real.sqrt ((![2, 3] : Fin 2 → ℕ) i))
      = {Real.sqrt 2, Real.sqrt 3} := by
    ext x
    simp [Fin.exists_fin_two, eq_comm]
  rw [hset] at h
  rw [h]
  simp

end TauCeti.Multiquadratic
