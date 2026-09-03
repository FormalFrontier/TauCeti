/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs

/-!
# Integrality as an explicit monic relation of positive degree

`IsIntegral S x` says a monic polynomial over `S` kills `x`. For arguments that adjust the
coefficients one at a time it is more convenient to have the relation written out, and written
so that its degree is visibly positive:

```text
x ^ (n + 1) + ∑ i ∈ Finset.range (n + 1), c i * x ^ i = 0,   with `c i ∈ S` for `i < n + 1`.
```

This file gives that form and its converse. Both directions are pure ring theory — no topology
appears — and they are stated for a subring of an arbitrary commutative ring.

Writing the degree as `n + 1` rather than carrying a separate `0 < p.natDegree` hypothesis is
what lets a caller perturb the constant coefficient without disturbing the leading one, which is
the shape Huber's approximation arguments need.

## Main results

* `TauCeti.exists_pow_add_sum_eq_zero_of_isIntegral`: an integral element satisfies such a
  relation.
* `TauCeti.isIntegral_of_pow_add_sum_eq_zero`: conversely, such a relation exhibits integrality.
-/

public section

namespace TauCeti

open Polynomial

/-- An element integral over a subring `S` satisfies a monic relation of positive degree whose
coefficients lie in `S`. Membership is asserted only on `i < n + 1`, the range the relation sums
over; a caller reading off coefficients gets no promise about the tail and needs none. Writing the
degree as `n + 1` builds the positivity into the shape, which is what lets the constant coefficient
be adjusted without disturbing the leading one. -/
theorem exists_pow_add_sum_eq_zero_of_isIntegral {R : Type*} [CommRing R] {S : Subring R}
    {x : R} (hx : IsIntegral S x) : ∃ (n : ℕ) (c : ℕ → R), (∀ i < n + 1, c i ∈ S) ∧ x ^ (n + 1) +
      ∑ i ∈ Finset.range (n + 1), c i * x ^ i = 0 := by
  obtain ⟨p, hmonic, heval⟩ := hx
  -- multiplying the relation by `x` shifts the coefficients up by one, which makes the degree
  -- positive even when `p` is constant
  refine ⟨p.natDegree, fun i ↦ Nat.casesOn i 0 fun j ↦ (p.coeff j : R), ?_, ?_⟩
  · rintro (_ | j) _
    · exact S.zero_mem
    · exact (p.coeff j).2
  · have h0 : (∑ i ∈ Finset.range p.natDegree, (p.coeff i : R) * x ^ i) + x ^ p.natDegree = 0 := by
      rw [← heval, eval₂_eq_sum_range, Finset.sum_range_succ, hmonic.coeff_natDegree]
      simp [Algebra.algebraMap_ofSubsemiring_apply]
    rw [Finset.sum_range_succ', add_comm]
    simpa [add_mul, Finset.sum_mul, mul_assoc, ← pow_succ] using congrArg (· * x) h0

/-- The converse of `TauCeti.exists_pow_add_sum_eq_zero_of_isIntegral`: a monic relation of
positive degree with coefficients in a subring `S` exhibits its root as integral over `S`. Only the
coefficients actually summed over, `i < n + 1`, are required to lie in `S`. -/
theorem isIntegral_of_pow_add_sum_eq_zero {R : Type*} [CommRing R] {S : Subring R} {x : R}
    {n : ℕ} {c : ℕ → R} (hcS : ∀ i < n + 1, c i ∈ S)
    (h : x ^ (n + 1) + ∑ i ∈ Finset.range (n + 1), c i * x ^ i = 0) : IsIntegral S x :=
  -- the witness sums over `Fin (n + 1)`, the shape `degree_sum_fin_lt` bounds directly
  ⟨X ^ (n + 1) + ∑ i : Fin (n + 1), C (⟨c i, hcS i i.isLt⟩ : S) * X ^ (i : ℕ),
    monic_X_pow_add (degree_sum_fin_lt _), by
      simpa [eval₂_finsetSum, Finset.sum_range, Algebra.algebraMap_ofSubsemiring_apply] using h⟩

end TauCeti
