/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
public import TauCeti.NumberTheory.HeckeRing.GLn.PolynomialRing.Basic

/-!
# The leading elementary-divisor vector of a Hecke monomial

Towards **Shimura's Theorem 3.20** at general `n`: the `p`-local Hecke ring `pLocalSubring` is
the polynomial ring `ℤ[X₁, …, Xₙ]` on the diagonal prime cosets `heckeGen k = T(1, …, 1, p, …, p)`.
The injectivity half is a leading-term argument. Multiplying double cosets multiplies their
elementary divisors "up to lower terms", so the monomial `∏ k, heckeGen k ^ e k` has a
distinguished term, the diagonal coset whose elementary divisors are the products of those of the
factors, and the argument is that this leading term determines the exponent vector `e`.

This file is the combinatorial half of that argument: the exponent vector `leadingExponent e` of
that distinguished diagonal — entry `i` counts, with multiplicity `e k`, the generators whose
diagonal carries `p` in position `i`, which are the `k` with `n - 1 - i ≤ k` — together with the
properties the leading-term argument consumes, above all that the exponents are recovered from it.

The vector is the suffix sums of `e` read from the last position backwards, and suffix sums are
Mathlib's `Fin.accumulate`, the device of the fundamental theorem of symmetric polynomials (the same
leading-term argument, for the elementary symmetric polynomials): `leadingExponent e` is
`Fin.accumulate n n e` precomposed with `Fin.rev`, the recovery of the exponents is
`Fin.accumulate_injective`, and the explicit inverse is `Fin.invAccumulate`.

Multiplying Hecke monomials adds their exponent vectors, so `leadingExponent` is bundled as an
`AddMonoidHom`, as `Fin.accumulate` itself is. Its `map_zero`, `map_add`, `map_sum` and `map_nsmul`
are then the generic ones: a product over a finite family of monomials, or a monomial raised to a
power, needs no lemma of its own here.

## Main definitions

* `HeckeRing.GLn.leadingExponent`: the exponent vector of the leading elementary-divisor diagonal
  of the Hecke monomial with exponents `e`, the suffix sums `i ↦ ∑ k ≥ n - 1 - i, e k`, as an
  additive homomorphism `(Fin n → ℕ) →+ (Fin n → ℕ)`.

## Main results

* `HeckeRing.GLn.leadingExponent_injective`: **the exponents of a Hecke monomial are recovered
  from its leading elementary-divisor vector** — `Fin.accumulate_injective` transported along
  `Fin.rev`.
* `HeckeRing.GLn.isDvdChain_primePowDiag_leadingExponent`: the vector is monotone
  (`HeckeRing.GLn.leadingExponent_monotone`), so the leading diagonal `T(p ^ leadingExponent e)`
  is a divisibility chain — for `0 < p` a canonical diagonal, by `primePowDiag_pos`.
* `HeckeRing.GLn.primePowDiag_leadingExponent_single`: on the generator `X k` the leading
  diagonal is `heckeGenDiag k` itself; `map_add` and `primePowDiag_add` then give the leading
  diagonal of a product of monomials as the product of theirs.
* `HeckeRing.GLn.sum_leadingExponent`: the weight `∑ k, (k + 1) * e k` of the leading diagonal —
  the exponent of its determinant `p ^ ∑ i, leadingExponent e i`, which is that determinant's
  `p`-adic valuation once `p` is prime.

## Implementation notes

The other half of the leading-term argument — that the leading coset occurs in the monomial with
coefficient `1` and every other coset of its support lies below it — is the triangular expansion,
and is not proved here. At `n = 1, 2` Theorem 3.20 is `PolynomialRing/Injective.lean`, by direct
computation with the leading coset `T(p ^ e 1, p ^ (e 0 + e 1))` written out; that computation is
not rerouted through this vector.

This is original work filling the general-`n` gap the roadmap records: the AINTLIB source
(`LeanModularForms/HeckeRIngs/GLn/PolynomialRing.lean`) proves Theorem 3.20 at `n = 1, 2` only and
has no general-`n` leading-term device.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.2, Theorem 3.20.
-/

public section

open Finset

namespace HeckeRing.GLn

variable {n : ℕ}

/-- The exponent vector of the leading elementary-divisor diagonal of the Hecke monomial
`∏ k, heckeGen k ^ e k`: entry `i` counts, with multiplicity `e k`, the generators `heckeGen k`
whose diagonal `heckeGenDiag k` carries `p` in position `i` — those with `n - 1 - i ≤ k`, i.e.
`Fin.rev i ≤ k` — so it is the suffix sum `Fin.accumulate n n e` of `e` at `Fin.rev i`.

Additive, because multiplying Hecke monomials adds their exponents; bundled, so that `map_zero`,
`map_add`, `map_sum` and `map_nsmul` are available generically. -/
def leadingExponent : (Fin n → ℕ) →+ (Fin n → ℕ) where
  toFun e i := Fin.accumulate n n e (Fin.rev i)
  map_zero' := by ext i; simp only [map_zero, Pi.zero_apply]
  map_add' e f := by ext i; simp only [map_add, Pi.add_apply]

/-- Defining equation for the sealed definition `leadingExponent`. -/
lemma leadingExponent_apply (e : Fin n → ℕ) (i : Fin n) :
    leadingExponent e i = Fin.accumulate n n e (Fin.rev i) :=
  (rfl)

/-- The leading exponent vector as a sum over an interval: position `i` sees the generators
`k ≥ Fin.rev i`. -/
lemma leadingExponent_eq_sum_Ici (e : Fin n → ℕ) (i : Fin n) :
    leadingExponent e i = ∑ k ∈ Ici (Fin.rev i), e k := by
  simp only [leadingExponent_apply, Fin.accumulate_apply, Fin.val_fin_le, Finset.filter_le_eq_Ici]

/-- Read from the last position backwards, the leading exponent vector is the suffix sums of the
exponents: position `n - 1 - k` sees exactly the generators `k' ≥ k`. -/
lemma leadingExponent_rev (e : Fin n → ℕ) (k : Fin n) :
    leadingExponent e (Fin.rev k) = ∑ k' ∈ Ici k, e k' := by
  rw [leadingExponent_eq_sum_Ici, Fin.rev_rev]

/-- On a single generator, the leading exponent vector is that generator's own exponent vector
`heckeGenExponent n k`. -/
@[simp]
lemma leadingExponent_single (k : Fin n) :
    leadingExponent (Pi.single k 1) = heckeGenExponent n k := by
  ext i
  rw [leadingExponent_eq_sum_Ici, Finset.sum_pi_single', heckeGenExponent_apply]
  simp only [Finset.mem_Ici, Fin.le_iff_val_le_val, Fin.val_rev]
  split_ifs <;> omega

/-- The leading diagonal of the generator `heckeGen k` is its defining diagonal `heckeGenDiag k`. -/
lemma primePowDiag_leadingExponent_single (p : ℕ) (k : Fin n) :
    primePowDiag n p (leadingExponent (Pi.single k 1)) = heckeGenDiag n p k := by
  rw [leadingExponent_single, heckeGenDiag_eq_primePowDiag]

/-- The leading exponent vector is monotone: a later position sees every generator an earlier one
does. -/
lemma leadingExponent_monotone (e : Fin n → ℕ) : Monotone (leadingExponent e) := by
  intro i j hij
  rw [leadingExponent_eq_sum_Ici, leadingExponent_eq_sum_Ici]
  exact Finset.sum_le_sum_of_subset (Finset.Ici_subset_Ici.2 (Fin.rev_le_rev.2 hij))

/-- The leading diagonal `T(p ^ leadingExponent e)` is a divisibility chain; together with
`primePowDiag_pos`, for `0 < p` it is a canonical diagonal coset. -/
lemma isDvdChain_primePowDiag_leadingExponent (p : ℕ) (e : Fin n → ℕ) :
    IsDvdChain (primePowDiag n p (leadingExponent e)) :=
  isDvdChain_primePowDiag n p _ (leadingExponent_monotone e)

/-- **The exponents are recovered from the leading elementary-divisor vector.** Its entries are
the suffix sums of the exponents, and suffix sums determine a vector
(`Fin.accumulate_injective`; the inverse is `Fin.invAccumulate`, the consecutive differences). -/
lemma leadingExponent_injective : Function.Injective (leadingExponent (n := n)) := by
  intro e f h
  refine Fin.accumulate_injective le_rfl (funext fun k ↦ ?_)
  simpa only [leadingExponent_apply, Fin.rev_rev] using congr_fun h (Fin.rev k)

/-- The weight of the leading diagonal: the total of the leading exponent vector is
`∑ k, (k + 1) * e k`, the generator `heckeGen k` contributing `k + 1` for each of its `e k`
factors. It is the exponent of the determinant `∏ i, primePowDiag n p (leadingExponent e) i`,
which is `p ^ ∑ i, leadingExponent e i`; once `p` is prime that exponent is the determinant's
`p`-adic valuation. -/
lemma sum_leadingExponent (e : Fin n → ℕ) :
    ∑ i, leadingExponent e i = ∑ k : Fin n, ((k : ℕ) + 1) * e k := by
  rw [← Equiv.sum_comp Fin.revPerm (leadingExponent e)]
  simp only [Fin.revPerm_apply, leadingExponent_rev]
  rw [Finset.sum_comm' (t' := Finset.univ) (s' := fun k ↦ Iic k) (by simp)]
  simp [Fin.card_Iic]

end HeckeRing.GLn
