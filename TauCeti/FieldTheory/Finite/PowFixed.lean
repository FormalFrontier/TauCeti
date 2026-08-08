/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.FieldTheory.Finite.FrobeniusFixed

/-!
# Rings fixed by a power map

This file records two elementary consequences of every element of a ring being fixed by a power
map: a commutative ring fixed by a nontrivial power map is reduced, and a domain extension of a
finite field fixed by the cardinality power map is the base field itself.

These are general finite-ring prerequisites for the good-prime structure theorem in the roadmap
`RepresentationTheory/CharacterTheory`, Layer 6.

## Main results

* `TauCeti.isReduced_of_pow_eq_self`: a commutative ring fixed by a nontrivial power map is reduced.
* `TauCeti.algebraMap_bijective_of_pow_card_eq_self`: an extension fixed by the base-field
  cardinality power map is the base field itself.
-/

public section

namespace TauCeti

/-- A commutative ring in which `x ^ q = x` for some `q > 1` has no nonzero nilpotents: iterating
gives `x ^ q ^ m = x`, and `q ^ m` outruns any nilpotency exponent. -/
theorem isReduced_of_pow_eq_self {R : Type*} [CommRing R] {q : ℕ} (hq : 1 < q)
    (h : ∀ x : R, x ^ q = x) : IsReduced R := by
  refine ⟨fun x hx => ?_⟩
  obtain ⟨n, hn⟩ := hx
  have key : ∀ m : ℕ, x ^ q ^ m = x := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ, pow_mul, ih, h]
  have hle : n ≤ q ^ n := (Nat.lt_pow_self hq).le
  calc x = x ^ q ^ n := (key n).symm
    _ = x ^ n * x ^ (q ^ n - n) := by rw [← pow_add]; congr 1; omega
    _ = 0 := by rw [hn, zero_mul]

/-- **A field extension in which `x ^ |K| = x` is `K` itself.** Every element of the extension is
then in the range of the algebra map by the finite-field Frobenius fixed-point criterion. -/
theorem algebraMap_bijective_of_pow_card_eq_self {K L : Type*} [Field K] [Fintype K] [CommRing L]
    [IsDomain L] [Algebra K L] (h : ∀ x : L, x ^ Fintype.card K = x) :
    Function.Bijective (algebraMap K L) :=
  ⟨(algebraMap K L).injective,
    fun x => (FiniteField.pow_card_eq_self_iff_mem_range_algebraMap x).mp (h x)⟩

end TauCeti
