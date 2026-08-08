/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.CompletelyMonotone.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Half-line closure for completely monotone functions

This file extends the API for `TauCeti.IsCompletelyMonotoneOnIoi`, the ordinary-derivative
version of complete monotonicity on `(0, ∞)`, with the multiplicative and differential closure
properties needed by the Bernstein-function part of the one-parameter-semigroups roadmap, and
derives the corresponding multiplicative closure for the closed-half-line predicate
`TauCeti.IsCompletelyMonotoneOnIci`.

The closed-half-line predicate `TauCeti.IsCompletelyMonotone` already has product and
negated-derivative closure in `TauCeti.Analysis.CompletelyMonotone.Closure`. The open version is
not just a corollary of that file: Bernstein functions are allowed to have a singular right
derivative at `0`, so their derivative is naturally completely monotone only on `(0, ∞)`.

## Main declarations

* `TauCeti.IsCompletelyMonotoneOnIoi.mul`: closure under pointwise multiplication.
* `TauCeti.IsCompletelyMonotoneOnIoi.prod`: closure under finite products.
* `TauCeti.IsCompletelyMonotoneOnIoi.pow`: closure under natural powers.
* `TauCeti.IsCompletelyMonotoneOnIoi.neg_one_pow_mul_iteratedDeriv`: every alternating ordinary
  iterated derivative of a completely monotone function on `(0, ∞)` is again completely monotone
  there.
* `TauCeti.IsCompletelyMonotoneOnIoi.neg_deriv`: the negated ordinary derivative of a completely
  monotone function on `(0, ∞)` is completely monotone there.
* `TauCeti.IsCompletelyMonotoneOnIci.mul`, `TauCeti.IsCompletelyMonotoneOnIci.prod`,
  `TauCeti.IsCompletelyMonotoneOnIci.pow`: the closed-half-line predicate is closed under
  pointwise multiplication, finite products, and natural powers.

## References

* R. Schilling, R. Song, Z. Vondraček, *Bernstein Functions: Theory and Applications*
  (de Gruyter, 2nd ed. 2012).
-/

public section

open Set
open scoped ContDiff

namespace TauCeti

private theorem iteratedDeriv_iteratedDeriv (f : ℝ → ℝ) (n k : ℕ) :
    iteratedDeriv n (iteratedDeriv k f) = iteratedDeriv (n + k) f := by
  simp [iteratedDeriv_eq_iterate, Function.iterate_add_apply]

namespace IsCompletelyMonotoneOnIoi

variable {f g : ℝ → ℝ}

/-- Completely monotone functions on `(0, ∞)` are closed under pointwise multiplication. -/
theorem mul (hf : IsCompletelyMonotoneOnIoi f) (hg : IsCompletelyMonotoneOnIoi g) :
    IsCompletelyMonotoneOnIoi (f * g) := by
  refine ⟨hf.contDiffOn.mul hg.contDiffOn, fun n t ht => ?_⟩
  have hfn : ContDiffAt ℝ (n : WithTop ℕ∞) f t :=
    (hf.contDiffOn.contDiffAt (isOpen_Ioi.mem_nhds ht)).of_le (by exact_mod_cast le_top)
  have hgn : ContDiffAt ℝ (n : WithTop ℕ∞) g t :=
    (hg.contDiffOn.contDiffAt (isOpen_Ioi.mem_nhds ht)).of_le (by exact_mod_cast le_top)
  rw [iteratedDeriv_mul hfn hgn, Finset.mul_sum]
  refine Finset.sum_nonneg fun i hi => ?_
  have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have e1 := hf.neg_one_pow_mul_iteratedDeriv_nonneg i ht
  have e2 := hg.neg_one_pow_mul_iteratedDeriv_nonneg (n - i) ht
  have hsign : ((-1 : ℝ)) ^ n = (-1) ^ i * (-1) ^ (n - i) := by
    rw [← pow_add, Nat.add_sub_cancel' hin]
  have key : (-1 : ℝ) ^ n * ((n.choose i : ℝ) * iteratedDeriv i f t
        * iteratedDeriv (n - i) g t)
      = (n.choose i : ℝ) * ((-1) ^ i * iteratedDeriv i f t)
        * ((-1) ^ (n - i) * iteratedDeriv (n - i) g t) := by
    rw [hsign]
    ring
  rw [key]
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) e1) e2

/-- Completely monotone functions on `(0, ∞)` are closed under finite products. -/
theorem prod {ι : Type*} {s : Finset ι} {f : ι → ℝ → ℝ}
    (hf : ∀ i ∈ s, IsCompletelyMonotoneOnIoi (f i)) :
    IsCompletelyMonotoneOnIoi (fun t => ∏ i ∈ s, f i t) := by
  have h := Finset.prod_induction f IsCompletelyMonotoneOnIoi
    (fun _ _ => IsCompletelyMonotoneOnIoi.mul)
    (isCompletelyMonotone_const zero_le_one).isCompletelyMonotoneOnIoi hf
  have heq : (∏ i ∈ s, f i) = fun t => ∏ i ∈ s, f i t := funext fun t => Finset.prod_apply t s f
  rwa [heq] at h

/-- Completely monotone functions on `(0, ∞)` are closed under taking natural powers. -/
theorem pow (hf : IsCompletelyMonotoneOnIoi f) (k : ℕ) : IsCompletelyMonotoneOnIoi (f ^ k) := by
  induction k with
  | zero => rw [pow_zero]; exact (isCompletelyMonotone_const zero_le_one).isCompletelyMonotoneOnIoi
  | succ k ih => rw [pow_succ]; exact ih.mul hf

/-- Every alternating ordinary iterated derivative of a completely monotone function on
`(0, ∞)` is completely monotone there. -/
theorem neg_one_pow_mul_iteratedDeriv (hf : IsCompletelyMonotoneOnIoi f) (k : ℕ) :
    IsCompletelyMonotoneOnIoi (fun t => (-1 : ℝ) ^ k * iteratedDeriv k f t) := by
  have hcont : ContDiffOn ℝ ∞ (iteratedDeriv k f) (Ioi 0) := by
    induction k with
    | zero => simpa [iteratedDeriv_zero] using hf.contDiffOn
    | succ k ih =>
        simpa [iteratedDeriv_succ] using
          ih.deriv_of_isOpen isOpen_Ioi (by simp)
  refine ⟨?_, fun n t ht => ?_⟩
  · simpa [smul_eq_mul] using hcont.const_smul ((-1 : ℝ) ^ k)
  have hsign := hf.neg_one_pow_mul_iteratedDeriv_nonneg (n + k) ht
  have hiter :
      iteratedDeriv n (fun t => (-1 : ℝ) ^ k * iteratedDeriv k f t) t =
        (-1 : ℝ) ^ k * iteratedDeriv (n + k) f t := by
    rw [iteratedDeriv_const_mul_field, iteratedDeriv_iteratedDeriv f n k]
  rw [hiter]
  have key :
      (-1 : ℝ) ^ n * ((-1 : ℝ) ^ k * iteratedDeriv (n + k) f t) =
        (-1 : ℝ) ^ (n + k) * iteratedDeriv (n + k) f t := by
    rw [pow_add]
    ring
  rwa [key]

/-- The negated ordinary derivative of a completely monotone function on `(0, ∞)` is completely
monotone there. -/
theorem neg_deriv (hf : IsCompletelyMonotoneOnIoi f) :
    IsCompletelyMonotoneOnIoi (fun t => -deriv f t) := by
  simpa [pow_one, iteratedDeriv_one] using hf.neg_one_pow_mul_iteratedDeriv 1

end IsCompletelyMonotoneOnIoi

namespace IsCompletelyMonotoneOnIci

variable {f g : ℝ → ℝ}

/-- Closed-half-line complete monotonicity is closed under pointwise multiplication. -/
protected lemma mul (hf : IsCompletelyMonotoneOnIci f) (hg : IsCompletelyMonotoneOnIci g) :
    IsCompletelyMonotoneOnIci (f * g) :=
  isCompletelyMonotoneOnIci_iff.mpr ⟨hf.continuousOn.mul hg.continuousOn,
    hf.isCompletelyMonotoneOnIoi.mul hg.isCompletelyMonotoneOnIoi⟩

/-- Closed-half-line complete monotonicity is closed under finite products. -/
protected lemma prod {ι : Type*} {s : Finset ι} {F : ι → ℝ → ℝ}
    (hF : ∀ i ∈ s, IsCompletelyMonotoneOnIci (F i)) :
    IsCompletelyMonotoneOnIci (fun t => ∏ i ∈ s, F i t) := by
  have h := Finset.prod_induction F IsCompletelyMonotoneOnIci
    (fun _ _ => IsCompletelyMonotoneOnIci.mul)
    (of_isCompletelyMonotone (isCompletelyMonotone_const zero_le_one)) hF
  have heq : (∏ i ∈ s, F i) = fun t => ∏ i ∈ s, F i t := funext fun t => Finset.prod_apply t s F
  rwa [heq] at h

/-- Closed-half-line complete monotonicity is closed under natural powers. -/
protected lemma pow (hf : IsCompletelyMonotoneOnIci f) (k : ℕ) :
    IsCompletelyMonotoneOnIci (f ^ k) :=
  isCompletelyMonotoneOnIci_iff.mpr
    ⟨hf.continuousOn.pow k, hf.isCompletelyMonotoneOnIoi.pow k⟩

end IsCompletelyMonotoneOnIci

end TauCeti
