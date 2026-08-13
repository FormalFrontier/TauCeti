/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RingTheory.Binomial

/-!
# Products of generalized binomial coefficients

This file gives the linearization formula for the product of two generalized binomial
coefficients in a binomial ring. In the binomial basis, the formula reads

```text
(r choose m) (r choose n) =
  ∑ i + j = n, (m choose j) (m + i choose m) (r choose (m + i)).
```

The coefficients are natural numbers. Consequently the additive subgroup spanned by the
coefficients `(r choose n)` is already a subring. This integral form is the Cartan--Cartan
multiplication rule used when normal-ordering the generators of the Kostant integral form:
products of the generators `(h choose n)` remain integral linear combinations of generators of
the same kind.

The proof combines Mathlib's Chu--Vandermonde identity `Ring.add_choose_eq` with its shifted
factorization `Ring.choose_smul_choose`. No polynomial expansion or division by factorials is
needed.

## Main result

* `TauCeti.choose_mul_choose`: the product expansion in the binomial basis.
* `TauCeti.ringChooseSpan`: the additive subgroup spanned by the binomial coefficients in one
  element.
* `TauCeti.ringChooseSubring`: that span, bundled as a subring.
* `TauCeti.subringClosure_range_ringChoose`: the generated subring has no further additive
  elements beyond this span.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §26.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

namespace TauCeti

open Finset

variable {R : Type*} [Ring R] [BinomialRing R]

/-- The product of two generalized binomial coefficients, expanded as an integral linear
combination of generalized binomial coefficients in the same element.

The pair `(i, j)` runs over `i + j = n`. Thus the summand has binomial degree `m + i` and
coefficient `(m choose j) * (m + i choose m)`. Terms with `m < j` vanish automatically. -/
theorem choose_mul_choose (r : R) (m n : ℕ) :
    Ring.choose r m * Ring.choose r n =
      ∑ ij ∈ antidiagonal n,
        (Nat.choose m ij.2 * Nat.choose (m + ij.1) m) • Ring.choose r (m + ij.1) := by
  have hcomm : Commute (r - (m : R)) (m : R) :=
    (Nat.cast_commute m r).symm.sub_left (Commute.refl (m : R))
  calc
    Ring.choose r m * Ring.choose r n =
        Ring.choose r m * Ring.choose ((r - (m : R)) + (m : R)) n := by
      rw [sub_add_cancel]
    _ = Ring.choose r m *
        ∑ ij ∈ antidiagonal n,
          Ring.choose (r - (m : R)) ij.1 * Ring.choose (m : R) ij.2 := by
      rw [Ring.add_choose_eq n hcomm]
    _ = ∑ ij ∈ antidiagonal n,
        Ring.choose r m *
          (Ring.choose (r - (m : R)) ij.1 * Ring.choose (m : R) ij.2) := by
      rw [mul_sum]
    _ = ∑ ij ∈ antidiagonal n,
        (Nat.choose m ij.2 * Nat.choose (m + ij.1) m) •
          Ring.choose r (m + ij.1) := by
      apply sum_congr rfl
      intro ij _
      rw [Ring.choose_natCast, ← mul_assoc]
      rw [← (Nat.cast_commute (Nat.choose m ij.2)
        (Ring.choose r m * Ring.choose (r - (m : R)) ij.1)).eq]
      rw [← nsmul_eq_mul]
      have hproduct :
          Nat.choose (m + ij.1) m • Ring.choose r (m + ij.1) =
            Ring.choose r m * Ring.choose (r - (m : R)) ij.1 := by
        simpa using Ring.choose_smul_choose r (Nat.le_add_right m ij.1)
      rw [← hproduct, smul_smul]

/-! ## The integral span -/

/-- The additive subgroup spanned by all generalized binomial coefficients in `r`. -/
def ringChooseSpan (r : R) : AddSubgroup R :=
  AddSubgroup.closure (Set.range (Ring.choose r))

/-- Every generalized binomial coefficient in `r` belongs to its integral span. -/
theorem ringChoose_mem_ringChooseSpan (r : R) (n : ℕ) :
    Ring.choose r n ∈ ringChooseSpan r :=
  AddSubgroup.subset_closure ⟨n, rfl⟩

/-- The integral span of the generalized binomial coefficients contains one. -/
theorem one_mem_ringChooseSpan (r : R) : 1 ∈ ringChooseSpan r := by
  rw [← Ring.choose_zero_right r]
  exact ringChoose_mem_ringChooseSpan r 0

/-- The integral span of the generalized binomial coefficients is closed under multiplication.

This is the algebraic content of `choose_mul_choose`: its natural-number coefficients act by
repeated addition, so every product of spanning generators remains in the same additive span. -/
theorem mul_mem_ringChooseSpan (r : R) {x y : R} (hx : x ∈ ringChooseSpan r)
    (hy : y ∈ ringChooseSpan r) : x * y ∈ ringChooseSpan r := by
  rw [ringChooseSpan] at hx hy ⊢
  induction hx, hy using AddSubgroup.closure_induction₂ with
  | mem x y hx hy =>
      obtain ⟨m, rfl⟩ := hx
      obtain ⟨n, rfl⟩ := hy
      rw [choose_mul_choose]
      exact sum_mem fun ij _ =>
        AddSubgroup.nsmul_mem _ (ringChoose_mem_ringChooseSpan r (m + ij.1)) _
  | zero_left => simp
  | zero_right => simp
  | add_left _ _ _ _ _ _ hx hy => simpa [add_mul] using AddSubgroup.add_mem _ hx hy
  | add_right _ _ _ _ _ _ hx hy => simpa [mul_add] using AddSubgroup.add_mem _ hx hy
  | neg_left _ _ _ _ hx => simpa [neg_mul] using AddSubgroup.neg_mem _ hx
  | neg_right _ _ _ _ hx => simpa [mul_neg] using AddSubgroup.neg_mem _ hx

/-- The subring whose underlying additive group is spanned by all generalized binomial
coefficients in `r`. The nontrivial multiplication field is `mul_mem_ringChooseSpan`. -/
def ringChooseSubring (r : R) : Subring R where
  toAddSubgroup := ringChooseSpan r
  one_mem' := one_mem_ringChooseSpan r
  mul_mem' := mul_mem_ringChooseSpan r

/-- Membership in `ringChooseSubring r` is membership in the integral additive span of the
generalized binomial coefficients in `r`. -/
@[simp]
theorem mem_ringChooseSubring_iff {r x : R} :
    x ∈ ringChooseSubring r ↔ x ∈ ringChooseSpan r :=
  Iff.rfl

/-- The subring generated by the generalized binomial coefficients in one element is exactly
their integral additive span. -/
theorem subringClosure_range_ringChoose (r : R) :
    Subring.closure (Set.range (Ring.choose r)) = ringChooseSubring r := by
  apply le_antisymm
  · refine Subring.closure_le.2 ?_
    rintro x ⟨n, hn⟩
    rw [← hn]
    exact ringChoose_mem_ringChooseSpan r n
  · intro x hx
    rw [mem_ringChooseSubring_iff, ringChooseSpan] at hx
    induction hx using AddSubgroup.closure_induction with
    | mem x hx => exact Subring.subset_closure hx
    | zero => exact Subring.zero_mem _
    | add _ _ _ _ hx hy => exact Subring.add_mem _ hx hy
    | neg _ _ hx => exact Subring.neg_mem _ hx

end TauCeti
