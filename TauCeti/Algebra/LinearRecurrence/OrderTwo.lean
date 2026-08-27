/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Products in a second-order linear recurrence

Fix a commutative ring `R`, two elements `D S : R`, and a sequence `d : ℕ → R` obeying the
second-order recurrence

`d (r + 2) = D * d (r + 1) - S * d r`.

Two identities hold for every such sequence. Neither asks `d` to be a polynomial, and neither
asks `R` for an order, a characteristic, or an invertible `2`.

## Main results

* `TauCeti.linearRec₂_mul_eq_succ_add_mul_pred`: multiplying a term by `D` moves it one step up
  and leaves `S` times the term one step down,
  `D * d m = d (m + 1) + S * d (m - 1)` for `0 < m`.
  This is the recurrence itself, re-indexed so that the multiplication rather than the top term
  is the subject; in that form it is what an induction on a product can apply term by term.
* `TauCeti.linearRec₂_mul_eq_sum_pow_mul`: once `d` is normalised by `d 0 = 1` and `d 1 = D`,
  a product of two terms is a *sum* of single terms,
  `d r * d s = ∑ i ∈ Finset.range (r + 1), S ^ i * d (r + s - 2 * i)` for `r ≤ s`.

The second identity is the point. It is the Clebsch–Gordan shape: the product of two terms
collapses to a linear combination of single terms, with no product of `d`-values surviving on
the right. A recursion that multiplies two terms together can therefore be pushed through it and
re-read as a statement about single terms, which is what makes an induction over the two indices
terminate.

## Relation to Mathlib

Mathlib has three developments in this neighbourhood. None of them carries these identities, and
each fails to for a different reason.

* `Mathlib/Algebra/LinearRecurrence.lean` is about the *solution space* of a linear recurrence —
  `LinearRecurrence.IsSolution`, `mkSol`, `solSpace`, its `Module.Basis`, and the characteristic
  polynomial. It describes which sequences solve a recurrence; it proves no identity between the
  terms of one. The hypothesis used here is exactly `E.IsSolution d` for
  `E : LinearRecurrence R := ⟨2, ![-S, D]⟩`, but stating it that way would oblige every caller to
  build `E` and unfold a `Fin 2` sum to recover the recurrence it already has, so it is taken
  here in the unbundled form the callers actually hold.
* `Mathlib/RingTheory/Polynomial/Chebyshev.lean` fixes the coefficients. `Chebyshev.T` obeys
  `T (n + 2) = 2 * X * T (n + 1) - T n`, i.e. `D = 2 * X` and `S = 1`; its product identities
  (`T_mul_T`, `C_mul_C`) are two-term, and are identities of those specific families. An
  arbitrary `(D, S)` is not a specialisation of them.
* `Mathlib/RingTheory/Polynomial/Dickson.lean` comes closest, since `dickson k a` obeys
  `dickson k a (n + 2) = X * dickson k a (n + 1) - C a * dickson k a n`, a genuine two-parameter
  recurrence. But `D` there is pinned to the indeterminate `X`, so reaching an arbitrary `D : R`
  means passing to `R[X]` and specialising; and Mathlib proves no product formula for it in any
  case — `dickson_one_one_mul` composes at a product of *indices*, which is a different identity.

So the results below are proved directly for an arbitrary sequence, which is also the form in
which they are consumed.

## References

The consumer is the prime-power Hecke recurrence of `TauCetiRoadmap/ModularForms`,
`T_(p^(r+2)) = T_p * T_(p^(r+1)) - p^(k-1) * ⟨p⟩ * T_(p^r)`: taking `d r = T_(p^r)`, `D = T_p` and
`S = p^(k-1) * ⟨p⟩` turns `linearRec₂_mul_eq_sum_pow_mul` into the product formula for
`T_(p^r) * T_(p^s)`. That instantiation belongs to the Hecke tree, and nothing in this file
mentions a Hecke operator.

## Provenance

Ported from AINTLIB (`github.com/CBirkbeck/AINTLIB`, Apache-2.0), the roadmap's nominated source
for `TauCetiRoadmap/ModularForms`, at commit `2baa76f742bdb4fb8ee323fabba41203bd390e08`,
`projects/LeanModularForms/LeanModularForms/HeckeRIngs/GL2/Unified/Gamma0RingDn.lean`, section
`FormalChebyshev` (lines 63-109), where the two results are the `private` lemmas `formal_D_mul_d`
and `formal_ppow_mul`.

They are ported public here rather than kept private: they are the reusable content of that
block, and a private copy would have to be re-ported by every consumer. The hypotheses are
AINTLIB's, unchanged; `D`, `S` and `d` become `variable`s, the names follow Mathlib's
statement-describing convention instead of the source's `formal_*` working names, and the first
proof spells out the step that the source discharges with `grind`.
-/

public section

namespace TauCeti

open Finset

variable {R : Type*} [CommRing R] {D S : R} {d : ℕ → R}

/-- **Multiplying by `D` shifts a term up.** For a sequence obeying
`d (r + 2) = D * d (r + 1) - S * d r`, multiplication by `D` sends `d m` to the next term plus
`S` times the previous one. This is the recurrence re-indexed, with the product as the subject. -/
theorem linearRec₂_mul_eq_succ_add_mul_pred
    (hd : ∀ r, d (r + 2) = D * d (r + 1) - S * d r) {m : ℕ} (hm : 0 < m) :
    D * d m = d (m + 1) + S * d (m - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rw [show k + 1 + 1 = k + 2 by omega, Nat.add_sub_cancel, hd k]
  ring

/-- **A product of two terms is a sum of single terms.** For a sequence obeying
`d (r + 2) = D * d (r + 1) - S * d r` and normalised by `d 0 = 1`, `d 1 = D`, the product
`d r * d s` with `r ≤ s` equals `∑ i ∈ range (r + 1), S ^ i * d (r + s - 2 * i)`: no product of
`d`-values survives on the right. -/
theorem linearRec₂_mul_eq_sum_pow_mul (h0 : d 0 = 1) (h1 : d 1 = D)
    (hd : ∀ r, d (r + 2) = D * d (r + 1) - S * d r) :
    ∀ {r s : ℕ}, r ≤ s → d r * d s = ∑ i ∈ range (r + 1), S ^ i * d (r + s - 2 * i) := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    intro s hrs
    match r, ih with
    | 0, _ => simp [h0]
    | 1, _ =>
      rw [h1, linearRec₂_mul_eq_succ_add_mul_pred hd (m := s) (by omega),
        sum_range_succ, sum_range_one, pow_zero, one_mul, pow_one,
        show 1 + s - 2 * 0 = s + 1 by omega, show 1 + s - 2 * 1 = s - 1 by omega]
    | (r + 2), ih =>
      have key : ∀ i ∈ range (r + 2),
          D * (S ^ i * d (r + 1 + s - 2 * i)) =
            S ^ i * d (r + 2 + s - 2 * i) + S ^ (i + 1) * d (r + s - 2 * i) := by
        intro i hi
        rw [mem_range] at hi
        have h := linearRec₂_mul_eq_succ_add_mul_pred hd (m := r + 1 + s - 2 * i) (by omega)
        rw [show r + 1 + s - 2 * i + 1 = r + 2 + s - 2 * i by omega,
          show r + 1 + s - 2 * i - 1 = r + s - 2 * i by omega] at h
        linear_combination S ^ i * h
      have hL : d (r + 2) * d s = D * (d (r + 1) * d s) - S * (d r * d s) := by
        linear_combination d s * hd r
      rw [hL, ih (r + 1) (by omega) (by omega), ih r (by omega) (by omega),
        mul_sum, sum_congr rfl key, sum_add_distrib]
      have hshift : S * ∑ i ∈ range (r + 1), S ^ i * d (r + s - 2 * i) =
          ∑ i ∈ range (r + 1), S ^ (i + 1) * d (r + s - 2 * i) := by
        rw [mul_sum]
        exact sum_congr rfl fun i _ ↦ by ring
      rw [hshift, sum_range_succ (fun i ↦ S ^ (i + 1) * d (r + s - 2 * i)) (r + 1),
        sum_range_succ (fun i ↦ S ^ i * d (r + 2 + s - 2 * i)) (r + 2),
        show r + 2 + s - 2 * (r + 2) = r + s - 2 * (r + 1) by omega]
      ring

end TauCeti
