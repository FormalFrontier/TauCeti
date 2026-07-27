/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.NumberTheory.Multiquadratic.FundamentalDiscriminant.OfSquarefree
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import TauCeti.NumberTheory.Multiquadratic.FundamentalDiscriminant.Factorization
import TauCeti.NumberTheory.Multiquadratic.QuadraticSubfield

/-!
# A square root of the radicand in the prime-discriminant compositum

For an integer `d`, the *candidate genus field* of `ℚ(√d)` is the compositum of the quadratic
fields `ℚ(√(radicand D*))` over the prime discriminants `D*` dividing the fundamental discriminant
`fundamentalDiscriminant d`. This file proves the square-class fact underlying the genus-field
construction: that compositum contains an element squaring to `d`. Identifying this compositum
with the genus field itself (the maximal unramified abelian extension) is later work; here we only
establish that a square root of `d` lies in it.

The argument is a square-class computation. Writing `M = adjoin ℚ (root)` for the roots of the
radicands, the product of all the roots squares to the product of the radicands, which — because
each prime discriminant is its radicand or four times it, and `fundamentalDiscriminant d = c² · d`
— lies in the square class of `d`. Scaling that product root by the appropriate rational produces
an element of `M` squaring to `d`.

Combined with the degree theorem `Prime/Discriminant/Independence` (the compositum has degree
`2ᵗ`), this is a step toward exhibiting the genus field as a multiquadratic extension of `ℚ(√d)`.

The description of the genus field as the compositum of the prime-discriminant quadratic fields is
classical; see D. A. Cox, *Primes of the Form x² + ny²*, and F. Lemmermeyer, *Reciprocity Laws*.

## Main results

* `TauCeti.Multiquadratic.exists_mem_adjoin_sq_eq_of_prod_primeDiscriminant_eq`: for a finset of
  prime discriminants whose product is `fundamentalDiscriminant d`, the compositum of the roots of
  their radicands contains an element squaring to `d`.
* `TauCeti.Multiquadratic.exists_finset_primeDiscriminant_and_exists_mem_adjoin_sq_eq_of_squarefree`
  packages that with the factorization: for squarefree `d`, the prime-discriminant factorization of
  `fundamentalDiscriminant d` exists (with its at-most-one-even property) and its radicand
  compositum contains an element squaring to `d`.
-/

public section

namespace TauCeti.Multiquadratic

open Finset

/-- A prime discriminant is a nonzero square (`1` or `2²`) times its radicand. -/
private lemma primeDiscriminant_eq_sq_mul_radicand {P : ℤ} (hP : IsPrimeDiscriminant P) :
    ∃ c : ℤ, c ≠ 0 ∧ P = c ^ 2 * primeDiscriminantRadicand P := by
  rcases primeDiscriminant_eq_radicand_or_eq_four_mul_radicand hP with h | h
  · exact ⟨1, one_ne_zero, by linear_combination h⟩
  · exact ⟨2, two_ne_zero, by linear_combination h⟩

/-- **A square root of `d` in the prime-discriminant compositum.** Let `d : ℤ` and let `s` be a
finite set of prime discriminants whose product is the fundamental discriminant
`fundamentalDiscriminant d`. For any chosen square roots `root` of the radicands of the members of
`s` in a field `L` over `ℚ`, the compositum `adjoin ℚ (Set.range root)` contains an element
squaring to `d`. This is the square-class containment underlying the genus-field construction. -/
theorem exists_mem_adjoin_sq_eq_of_prod_primeDiscriminant_eq {d : ℤ} {s : Finset ℤ}
    (hs : ∀ P ∈ s, IsPrimeDiscriminant P) (hprod : ∏ P ∈ s, P = fundamentalDiscriminant d)
    {L : Type*} [Field L] [Algebra ℚ L] (root : {P // P ∈ s} → L)
    (hroot : ∀ P : {P // P ∈ s},
      root P ^ 2 = algebraMap ℚ L ((primeDiscriminantRadicand P.val : ℤ) : ℚ)) :
    ∃ x ∈ IntermediateField.adjoin ℚ (Set.range root), x ^ 2 = algebraMap ℚ L ((d : ℤ) : ℚ) := by
  classical
  -- Per-factor square multiplier `c P` with `P = (c P)² · radicand P`.
  choose c hc0 hcP using fun (P : ℤ) (hP : IsPrimeDiscriminant P) =>
    primeDiscriminant_eq_sq_mul_radicand hP
  -- `∏ P = (∏ c P)² · ∏ radicand P` over `s`, in `ℤ`.
  have hCprod : ∏ P ∈ s, P =
      (∏ P ∈ s.attach, c P.1 (hs P.1 P.2)) ^ 2 *
        ∏ P ∈ s.attach, primeDiscriminantRadicand P.1 := by
    rw [← Finset.prod_pow, ← Finset.prod_mul_distrib, ← Finset.prod_attach s (fun P => P)]
    exact Finset.prod_congr rfl fun P _ => hcP P.1 (hs P.1 P.2)
  obtain ⟨c0, hc0ne, hfd⟩ := exists_sq_mul_eq_fundamentalDiscriminant d
  set C : ℤ := ∏ P ∈ s.attach, c P.1 (hs P.1 P.2) with hC
  set R : ℤ := ∏ P ∈ s.attach, primeDiscriminantRadicand P.1 with hR
  have hCne : C ≠ 0 := Finset.prod_ne_zero_iff.mpr fun P _ => hc0 P.1 (hs P.1 P.2)
  have hkey : C ^ 2 * R = c0 ^ 2 * d := by rw [← hCprod, hprod, hfd]
  -- In `ℚ`, `R` is a nonzero square times `d`.
  set a : ℚ := (c0 : ℚ) / (C : ℚ) with ha
  have hCQ : (C : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hCne
  have hc0Q : (c0 : ℚ) ≠ 0 := Int.cast_ne_zero.mpr (by rcases hc0ne with h | h <;> simp [h])
  have hane : a ≠ 0 := by rw [ha]; exact div_ne_zero hc0Q hCQ
  have hRa : (R : ℚ) = a ^ 2 * ((d : ℤ) : ℚ) := by
    have hcast : (C : ℚ) ^ 2 * (R : ℚ) = (c0 : ℚ) ^ 2 * ((d : ℤ) : ℚ) := by exact_mod_cast hkey
    rw [ha, div_pow]
    field_simp
    linear_combination hcast
  -- The product of all roots lies in `M` and squares to `R` (reusing the subset-product API).
  set x0 : L := ∏ P ∈ s.attach, root P with hx0
  have hx0mem : x0 ∈ IntermediateField.adjoin ℚ (Set.range root) := prod_root_mem_adjoin s.attach
  have hx0sq : x0 ^ 2 = algebraMap ℚ L (R : ℚ) := by
    rw [hx0, prod_root_sq hroot s.attach, hR, Int.cast_prod]
  -- Scale by `a⁻¹` to land a square root of `d`.
  have ha_inv_sq : a⁻¹ ^ 2 * a ^ 2 = 1 := by rw [← mul_pow, inv_mul_cancel₀ hane, one_pow]
  refine ⟨algebraMap ℚ L a⁻¹ * x0, mul_mem (IntermediateField.algebraMap_mem _ _) hx0mem, ?_⟩
  rw [mul_pow, hx0sq, hRa, ← map_pow, ← map_mul]
  congr 1
  rw [← mul_assoc, ha_inv_sq, one_mul]

/-- **The prime-discriminant compositum of a squarefree radicand contains a square root of `d`.**
For squarefree `d`, the fundamental discriminant `fundamentalDiscriminant d` factors into a finite
set `s` of prime discriminants, and for any roots of their radicands the compositum contains an
element squaring to `d`. This packages `exists_mem_adjoin_sq_eq_of_prod_primeDiscriminant_eq` with
the factorization `IsFundamentalDiscriminant.exists_finset_primeDiscriminant`, so callers need only
supply `d` squarefree. -/
theorem exists_finset_primeDiscriminant_and_exists_mem_adjoin_sq_eq_of_squarefree {d : ℤ}
    (hd : Squarefree d) :
    ∃ s : Finset ℤ, (∀ P ∈ s, IsPrimeDiscriminant P) ∧
      (∀ P ∈ s, ∀ Q ∈ s, IsEvenPrimeDiscriminant P → IsEvenPrimeDiscriminant Q → P = Q) ∧
      ∏ P ∈ s, P = fundamentalDiscriminant d ∧
      ∀ {L : Type*} [Field L] [Algebra ℚ L] (root : {P // P ∈ s} → L),
        (∀ P, root P ^ 2 = algebraMap ℚ L ((primeDiscriminantRadicand P.val : ℤ) : ℚ)) →
          ∃ x ∈ IntermediateField.adjoin ℚ (Set.range root), x ^ 2 = algebraMap ℚ L ((d : ℤ) : ℚ) :=
  have ⟨s, hs, hev, hprod⟩ :=
    (isFundamentalDiscriminant_fundamentalDiscriminant hd).exists_finset_primeDiscriminant
  ⟨s, hs, hev, hprod, fun root hroot =>
    exists_mem_adjoin_sq_eq_of_prod_primeDiscriminant_eq hs hprod root hroot⟩

end TauCeti.Multiquadratic
