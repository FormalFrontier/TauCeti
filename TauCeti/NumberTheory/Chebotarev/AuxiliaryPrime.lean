/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Cyclotomic.IrreducibleOfUnramified
public import TauCeti.NumberTheory.NumberField.RamifiedPrimes
public import Mathlib.NumberTheory.PrimesCongruentOne

/-!
# The auxiliary prime

The Chebotarev density argument repeatedly needs a rational prime that is simultaneously large,
congruent to `1` modulo a prescribed level, unramified in two number fields, and such that the
cyclotomic polynomial stays irreducible over the base. This file produces one, with all of those
conditions as conclusions rather than as obligations left to the caller.

## Main results

* `NumberField.exists_auxiliaryPrime`

## Implementation notes

The conditions are conclusions rather than obligations on the caller because they are needed
together: a caller holding only the congruence would have to re-derive the bound against the
ramified primes of both fields before it could discharge the rest.
-/

public section

open Polynomial
open scoped NumberField

namespace NumberField

/-- **The auxiliary prime.** Given number fields `K` and `L`, a level `n ≠ 0` and a bound `N`,
there is a rational prime `q` with `N < q`, congruent to `1` modulo `n`, unramified in both `K`
and `L`, and with `Φ_q` irreducible over `K`.

`n ∣ q - 1` is recorded alongside `q ≡ 1 [MOD n]` because the two are used in different forms
downstream and the translation needs `1 ≤ q`, which is not available to a caller holding only the
congruence. -/
theorem exists_auxiliaryPrime (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    (n N : ℕ) (hn : n ≠ 0) :
    ∃ q : ℕ, q.Prime ∧ N < q ∧ q ≡ 1 [MOD n] ∧ n ∣ q - 1 ∧
      Algebra.IsUnramifiedIn (𝓞 K) (Ideal.span {(q : ℤ)}) ∧
      Algebra.IsUnramifiedIn (𝓞 L) (Ideal.span {(q : ℤ)}) ∧
      Irreducible (cyclotomic q K) := by
  -- Push the bound past every prime that ramifies in either field; both sets are finite.
  obtain ⟨SK, hSK⟩ := (finite_ramifiedPrimes (K := K)).bddAbove
  obtain ⟨SL, hSL⟩ := (finite_ramifiedPrimes (K := L)).bddAbove
  obtain ⟨q, hq, hqgt, hqmod⟩ := Nat.exists_prime_gt_modEq_one (k := n) (max N (max SK SL)) hn
  have hqN : N < q := lt_of_le_of_lt (le_max_left _ _) hqgt
  have hurK : Algebra.IsUnramifiedIn (𝓞 K) (Ideal.span {(q : ℤ)}) := by
    by_contra h
    have hle : q ≤ SK := hSK (mem_ramifiedPrimes_iff.mpr ⟨hq, h⟩)
    exact absurd hle (not_le.mpr
      (lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hqgt))
  have hurL : Algebra.IsUnramifiedIn (𝓞 L) (Ideal.span {(q : ℤ)}) := by
    by_contra h
    have hle : q ≤ SL := hSL (mem_ramifiedPrimes_iff.mpr ⟨hq, h⟩)
    exact absurd hle (not_le.mpr
      (lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hqgt))
  refine ⟨q, hq, hqN, hqmod, ?_, hurK, hurL,
    IsCyclotomicExtension.irreducible_cyclotomic_of_unramified K q hq hurK⟩
  exact (Nat.modEq_iff_dvd' hq.one_lt.le).mp hqmod.symm

end NumberField
