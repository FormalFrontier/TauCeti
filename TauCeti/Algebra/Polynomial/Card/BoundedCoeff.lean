/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Set.Card

/-!
# Counting polynomials of bounded degree and bounded coefficients

For a (semi)ring `R` and a finite set `U` of allowed coefficient values, the polynomials of
degree at most `d` all of whose coefficients lie in `U` form a set of cardinality at most
`#U ^ (d + 1)`: a polynomial of degree `≤ d` is determined by its `d + 1` coefficients
`coeff 0, …, coeff d`, each of which ranges over `U`.

Mathlib uses the *finiteness* of this set inline, as the engine of its `bUnion_roots_finite`
(the set of roots of all polynomials of bounded degree with coefficients in a finite set is
finite), where the same injection `f ↦ (f.coeff i)ᵢ` appears, but exposes neither that finiteness
nor the explicit cardinality bound; this file supplies both.

The integer specialisation counts the polynomials of degree `≤ d` whose coefficients are bounded
in absolute value by `B`: there are at most `(2 * B + 1) ^ (d + 1)` of them. This is the
elementary counting input named by the Layer-2 ("effective Hermite–Minkowski") target of the
effective-bounds roadmap: Mathlib's `NumberField.finite_of_discr_bdd` already bounds the degree
and coefficient height of a generating polynomial of a number field of bounded discriminant
(`natDegree_le_rankOfDiscrBdd`, `boundOfDiscBdd`), so an explicit *count* of number fields of
bounded discriminant needs an explicit count of the polynomials of bounded degree and height.

The cardinality bound counts a number but does not by itself record finiteness (`Set.ncard` is
`0` on an infinite set), so each count is paired with the matching finiteness statement: these are
what turn an injection of some family into one of these boxes into an explicit count of the family,
the counting step the Layer-2 effective Hermite–Minkowski target needs. Mathlib proves this
finiteness only inline, inside `Polynomial.bUnion_roots_finite`, rather than exposing it.

## Main results

* `TauCeti.Polynomial.ncard_natDegree_le_coeff_mem_le`: at most `#U ^ (d + 1)` polynomials of
  degree `≤ d` with every coefficient in a finite set `U`.
* `TauCeti.Polynomial.finite_setOf_natDegree_le_coeff_mem`: that family is finite.
* `TauCeti.Polynomial.ncard_natDegree_le_abs_intCoeff_le`: at most `(2 * B + 1) ^ (d + 1)`
  integer polynomials of degree `≤ d` with every coefficient bounded by `B` in absolute value.
* `TauCeti.Polynomial.finite_setOf_natDegree_le_abs_intCoeff_le`: that family is finite.
-/

public section

open Polynomial

namespace TauCeti.Polynomial

variable {R : Type*} [Semiring R]

/-- The coefficient map `f ↦ (f.coeff i)ᵢ` into `Fin (d + 1) → R` is injective on the polynomials
of degree at most `d`: such a polynomial is determined by its first `d + 1` coefficients. This is
the shared injection behind both the count and the finiteness of the bounded-coefficient family. -/
private theorem coeff_injOn_natDegree_le (d : ℕ) :
    Set.InjOn (fun (f : R[X]) (i : Fin (d + 1)) => f.coeff i) {f | f.natDegree ≤ d} := by
  intro f hf g hg hfg
  rw [Set.mem_ofPred_eq] at hf hg
  exact (ext_iff_natDegree_le hf hg).2 fun i hi => congrFun hfg ⟨i, Nat.lt_succ_of_le hi⟩

/-- The polynomials of degree at most `d` whose coefficients all lie in a finite set `U` number
at most `#U ^ (d + 1)`: such a polynomial is determined by the `d + 1` coefficients
`coeff 0, …, coeff d`, each ranging over `U`, so the coefficient map injects the set into the
`(d + 1)`-fold product `Fin (d + 1) → U`. -/
theorem ncard_natDegree_le_coeff_mem_le (d : ℕ) (U : Finset R) :
    {f : R[X] | f.natDegree ≤ d ∧ ∀ i, f.coeff i ∈ U}.ncard ≤ U.card ^ (d + 1) := by
  classical
  set S : Set R[X] := {f | f.natDegree ≤ d ∧ ∀ i, f.coeff i ∈ U} with hS
  -- The coefficient map sends `S` into the finite product `Fin (d + 1) → U`.
  set T : Finset (Fin (d + 1) → R) := Fintype.piFinset (fun _ => U) with hT
  have hcard : (T : Set (Fin (d + 1) → R)).ncard = U.card ^ (d + 1) := by
    rw [Set.ncard_coe_finset, hT, Fintype.card_piFinset_const]
  rw [← hcard]
  refine Set.ncard_le_ncard_of_injOn (fun f i => f.coeff i) ?_ ?_ T.finite_toSet
  · intro f hf
    rw [Finset.mem_coe, Fintype.mem_piFinset]
    exact fun i => hf.2 i
  · exact (coeff_injOn_natDegree_le d).mono fun f hf => hf.1

/-- The polynomials of degree at most `d` whose coefficients all lie in a finite set `U` form a
finite set: the same coefficient map that gives the count above injects them into the finite
product `Fin (d + 1) → U`. Finiteness needs no computable finset data, so `U` is an arbitrary
finite `Set`. (Mathlib proves this only inline, inside `Polynomial.bUnion_roots_finite`.) -/
theorem finite_setOf_natDegree_le_coeff_mem (d : ℕ) {U : Set R} (hU : U.Finite) :
    {f : R[X] | f.natDegree ≤ d ∧ ∀ i, f.coeff i ∈ U}.Finite := by
  classical
  let π : R[X] → Fin (d + 1) → R := fun f i => f.coeff i
  refine ((Set.Finite.pi fun _ => hU).subset ?_).of_finite_image
    (?_ : Set.InjOn π _)
  · refine Set.image_subset_iff.2 fun f hf => ?_
    exact fun i _ => hf.2 i
  · exact (coeff_injOn_natDegree_le d).mono fun f hf => hf.1

/-- Bounding an integer coefficient by `B` in absolute value is membership in the interval
`[-B, B]`, so the two spellings of the bounded-degree, bounded-coefficient family agree. -/
private theorem setOf_abs_intCoeff_le_eq (d B : ℕ) :
    {f : ℤ[X] | f.natDegree ≤ d ∧ ∀ i, |f.coeff i| ≤ (B : ℤ)} =
      {f : ℤ[X] | f.natDegree ≤ d ∧ ∀ i, f.coeff i ∈ Finset.Icc (-(B : ℤ)) B} := by
  ext f
  simp only [Set.mem_ofPred_eq, Finset.mem_Icc, abs_le]

/-- The integer polynomials of degree at most `d` all of whose coefficients are bounded by `B` in
absolute value number at most `(2 * B + 1) ^ (d + 1)`: each of the `d + 1` coefficients
`coeff 0, …, coeff d` ranges over the `2 * B + 1` integers in `[-B, B]`. -/
theorem ncard_natDegree_le_abs_intCoeff_le (d B : ℕ) :
    {f : ℤ[X] | f.natDegree ≤ d ∧ ∀ i, |f.coeff i| ≤ (B : ℤ)}.ncard ≤ (2 * B + 1) ^ (d + 1) := by
  have hU : (Finset.Icc (-(B : ℤ)) B).card = 2 * B + 1 := by
    rw [Int.card_Icc]; omega
  rw [setOf_abs_intCoeff_le_eq]
  calc {f : ℤ[X] | f.natDegree ≤ d ∧ ∀ i, f.coeff i ∈ Finset.Icc (-(B : ℤ)) B}.ncard
      ≤ (Finset.Icc (-(B : ℤ)) B).card ^ (d + 1) :=
        ncard_natDegree_le_coeff_mem_le d _
    _ = (2 * B + 1) ^ (d + 1) := by rw [hU]

/-- The integer polynomials of degree at most `d` all of whose coefficients are bounded by `B` in
absolute value form a finite set: their coefficients range over the finite interval `[-B, B]`. -/
theorem finite_setOf_natDegree_le_abs_intCoeff_le (d B : ℕ) :
    {f : ℤ[X] | f.natDegree ≤ d ∧ ∀ i, |f.coeff i| ≤ (B : ℤ)}.Finite := by
  rw [setOf_abs_intCoeff_le_eq]
  exact finite_setOf_natDegree_le_coeff_mem d (Finset.Icc (-(B : ℤ)) B).finite_toSet

end TauCeti.Polynomial
