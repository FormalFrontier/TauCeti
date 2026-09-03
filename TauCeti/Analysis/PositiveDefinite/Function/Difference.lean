/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.ForwardDiff
public import TauCeti.Analysis.PositiveDefinite.Basic
public import TauCeti.Analysis.PositiveDefinite.Kernel.Shift

/-!
# Differences of bounded positive-definite functions

On an involutive commutative additive monoid `M`, a *bounded* positive-definite function `F`
dominates each of its translates by a self-adjoint element: if `star s = s`, then

`x ↦ F x - F (x + s)`

is again positive definite. This is the function-level form of
`TauCeti.posSemidef_sub_comp_shift`; self-adjointness of `s` is exactly what makes translation by
`s` a symmetric shift of the kernel `(a, b) ↦ F (a + star b)`.

That difference is the negative of Mathlib's forward difference `Δ_[s] F`, so iterating gives that
the alternating iterated differences `(-1) ^ n Δ_[s]^[n] F` are positive definite too, in operator
form and in the explicit binomial form

`x ↦ ∑ k ≤ n, (-1) ^ k (n choose k) F (x + k • s)`.

Positive definiteness is a statement about quadratic forms, not a pointwise sign; the values
themselves are nonnegative at the "norm points" `a + star a`.

Boundedness is only ever assumed at the "norm points" `a + star a`, the diagonal of the kernel:
Cauchy--Schwarz propagates a bound there to every point of the form `p + star q`. It is essential
and is not a technical artefact: `t ↦ exp t` is positive definite on the involutive monoid
`(ℝ≥0, +)` with the trivial involution, and it *increases*. The statement is
proved by a purely numerical moment-problem estimate on the finite quadratic forms; no topology,
measurability, or representing measure is assumed or produced here.

This advances `TauCetiRoadmap/OneParameterSemigroups/README.md`, Part C: it is the closure property
of the generic `IsPositiveDefinite` predicate that the Berg--Christensen--Ressel representation
(Milestone 2) runs on. The zero-spatial time axis `t ↦ F (t, 0)` of a bounded positive-definite
function on `ℝ≥0 × V` is such a function, for the trivial involution on `ℝ≥0`, and
`TauCeti/Analysis/PositiveDefinite/SemigroupGroup/Time/Difference.lean` reads its complete
monotonicity off the results below. The two-variable statements on `ℝ≥0 × V` itself are *not*
instances of them — the involutive-monoid wrapper carrying the Berg--Christensen--Ressel involution
is private to `TauCeti/Analysis/PositiveDefinite/SemigroupGroup/Basic.lean` — and are proved there
from the Kolmogorov decomposition of the Berg--Christensen--Ressel kernel; only the
forward-difference bookkeeping below is shared.

## Main declarations

* `TauCeti.neg_one_pow_mul_fwdDiff_iter_succ`: one differencing step advances the alternating
  iterated forward difference by one.
* `TauCeti.neg_one_pow_mul_fwdDiff_iter_eq_alternating_sum`: the binomial expansion of the
  alternating iterated forward difference.
* `TauCeti.IsPositiveDefinite.norm_apply_add_star_le`: a bound at the "norm points" `a + star a`
  bounds a positive-definite function at every point `p + star q`.
* `TauCeti.IsPositiveDefinite.sub_shift`: the difference of a bounded positive-definite function
  and its translate by a self-adjoint element is positive definite.
* `TauCeti.IsPositiveDefinite.neg_one_pow_mul_fwdDiff_iter` and
  `TauCeti.IsPositiveDefinite.alternating_sum`: the alternating iterated differences are positive
  definite, in forward-difference and in binomial form.
* `TauCeti.IsPositiveDefinite.sub_shift_add_star_self_nonneg`,
  `TauCeti.IsPositiveDefinite.neg_one_pow_mul_fwdDiff_iter_add_star_self_nonneg` and
  `TauCeti.IsPositiveDefinite.alternating_sum_add_star_self_nonneg`: the resulting nonnegativity at
  the "norm points" `a + star a`.

## References

* C. Berg, J. P. R. Christensen, P. Ressel, *Harmonic Analysis on Semigroups* (GTM 100, 1984),
  Chapter 4.
-/

public section

open scoped ComplexOrder fwdDiff

namespace TauCeti

/-! ## Forward-difference bookkeeping

Pure identities about Mathlib's forward difference operator; no positive definiteness is involved.
-/

section FwdDiff

variable {M : Type*} [AddCommMonoid M]

/-- Differencing once advances the alternating iterated forward difference by one step. This is the
bookkeeping behind every induction on the number of differencing steps. -/
theorem neg_one_pow_mul_fwdDiff_iter_succ (n : ℕ) (F : M → ℂ) (s : M) :
    (fun x : M => (-1 : ℂ) ^ n * Δ_[s]^[n] (-Δ_[s] F) x)
      = fun x : M => (-1 : ℂ) ^ (n + 1) * Δ_[s]^[n + 1] F x := by
  have hiter : Δ_[s]^[n] (-Δ_[s] F) = -Δ_[s]^[n + 1] F := by
    rw [Function.iterate_succ_apply, ← neg_one_zsmul (Δ_[s] F), fwdDiff_iter_const_smul,
      neg_one_zsmul]
  rw [hiter]
  funext x
  simp only [Pi.neg_apply, pow_succ]
  ring

/-- The alternating iterated forward difference as an explicit alternating binomial sum. -/
theorem neg_one_pow_mul_fwdDiff_iter_eq_alternating_sum (n : ℕ) (F : M → ℂ) (s x : M) :
    (-1 : ℂ) ^ n * Δ_[s]^[n] F x
      = ∑ k ∈ Finset.range (n + 1), (-1 : ℂ) ^ k * (n.choose k) * F (x + k • s) := by
  rw [fwdDiff_iter_eq_sum_shift, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hexp : n + (n - k) = 2 * (n - k) + k := by omega
  have hsign : (-1 : ℂ) ^ n * (-1 : ℂ) ^ (n - k) = (-1 : ℂ) ^ k := by
    rw [← pow_add, hexp, pow_add, pow_mul]
    simp
  rw [zsmul_eq_mul]
  push_cast
  rw [← mul_assoc, ← mul_assoc, hsign]

end FwdDiff

/-! ## Differences of bounded positive-definite functions -/

namespace IsPositiveDefinite

variable {M : Type*} [AddCommMonoid M] [StarAddMonoid M] {F : M → ℂ} {C : ℝ} {s : M}

/-- A positive-definite function bounded at the "norm points" `a + star a` is bounded at every
point of the form `p + star q`, by Cauchy--Schwarz for its kernel. -/
theorem norm_apply_add_star_le (hF : IsPositiveDefinite F)
    (hbdd : ∀ a, ‖F (a + star a)‖ ≤ C) (p q : M) : ‖F (p + star q)‖ ≤ C :=
  hF.posSemidef.norm_le_of_norm_apply_self_le hbdd p q

/-- **A bounded positive-definite function dominates its translate by a self-adjoint element.**
Translation by `s` with `star s = s` is a symmetric shift of the kernel `(a, b) ↦ F (a + star b)`,
so the bounded-kernel estimate `TauCeti.posSemidef_sub_comp_shift` applies; only the diagonal of
that kernel, the values at the "norm points" `a + star a`, has to be bounded. Boundedness cannot be
dropped: `t ↦ exp t` is positive definite on `ℝ≥0` with the trivial involution and increases. -/
theorem sub_shift (hF : IsPositiveDefinite F) (hbdd : ∀ a, ‖F (a + star a)‖ ≤ C)
    (hs : star s = s) : IsPositiveDefinite fun x => F x - F (x + s) := by
  have hkey := posSemidef_sub_comp_shift (K := fun a b : M => F (a + star b))
    (σ := fun a : M => a + s) hF.posSemidef (fun p q => ?_) (fun p => hbdd p)
  · refine IsPositiveDefinite.of_posSemidef ?_
    have heq : (fun a b : M => F (a + star b) - F (a + s + star b)) =
        fun a b : M => F (a + star b) - F (a + star b + s) := by
      funext a b
      rw [add_right_comm]
    rw [heq] at hkey
    exact hkey
  · rw [star_add, hs, add_assoc, add_comm s (star q)]

/-- The difference of a bounded positive-definite function and its translate by a self-adjoint
element is nonnegative at every "norm point" `a + star a`. -/
theorem sub_shift_add_star_self_nonneg (hF : IsPositiveDefinite F)
    (hbdd : ∀ a, ‖F (a + star a)‖ ≤ C) (hs : star s = s) (a : M) :
    0 ≤ F (a + star a) - F (a + star a + s) :=
  (hF.sub_shift hbdd hs).add_star_self_nonneg a

/-- If `F` is bounded by `C` at the "norm points", so is its translate by `s`; hence the difference
is bounded there by `2 * C`. Only used to propagate the bound through the induction in
`neg_one_pow_mul_fwdDiff_iter`. -/
private theorem norm_sub_shift_add_star_self_le (hF : IsPositiveDefinite F)
    (hbdd : ∀ a, ‖F (a + star a)‖ ≤ C) (a : M) :
    ‖F (a + star a) - F (a + star a + s)‖ ≤ 2 * C := by
  refine (norm_sub_le _ _).trans ?_
  have h₁ := hbdd a
  have h₂ : ‖F (a + star a + s)‖ ≤ C := by
    have h := hF.norm_apply_add_star_le hbdd (a + s) a
    rwa [add_right_comm] at h
  linarith

/-- **The alternating iterated differences of a bounded positive-definite function are positive
definite.** This is the iterate of `IsPositiveDefinite.sub_shift`: each differencing step doubles
the admissible bound, which is harmless because only the existence of *some* bound is used. -/
theorem neg_one_pow_mul_fwdDiff_iter (n : ℕ) (hF : IsPositiveDefinite F)
    (hbdd : ∀ a, ‖F (a + star a)‖ ≤ C) (hs : star s = s) :
    IsPositiveDefinite fun x : M => (-1 : ℂ) ^ n * Δ_[s]^[n] F x := by
  induction n generalizing F C with
  | zero => simpa using hF
  | succ n ih =>
      have hG := ih (hF.sub_shift hbdd hs) (norm_sub_shift_add_star_self_le hF hbdd)
      have hneg : (fun x => F x - F (x + s)) = -Δ_[s] F := by
        funext x
        simp [fwdDiff]
      rwa [hneg, neg_one_pow_mul_fwdDiff_iter_succ] at hG

/-- The alternating iterated difference of a bounded positive-definite function is nonnegative at
every "norm point" `a + star a`. -/
theorem neg_one_pow_mul_fwdDiff_iter_add_star_self_nonneg (n : ℕ) (hF : IsPositiveDefinite F)
    (hbdd : ∀ a, ‖F (a + star a)‖ ≤ C) (hs : star s = s) (a : M) :
    0 ≤ (-1 : ℂ) ^ n * Δ_[s]^[n] F (a + star a) :=
  (hF.neg_one_pow_mul_fwdDiff_iter n hbdd hs).add_star_self_nonneg a

/-- **The alternating iterated differences, expanded as binomial sums, are positive definite.**
This is `IsPositiveDefinite.neg_one_pow_mul_fwdDiff_iter` with the forward-difference operator
resolved into the explicit alternating sum over an arithmetic progression of translates. -/
theorem alternating_sum (n : ℕ) (hF : IsPositiveDefinite F) (hbdd : ∀ a, ‖F (a + star a)‖ ≤ C)
    (hs : star s = s) :
    IsPositiveDefinite fun x : M =>
      ∑ k ∈ Finset.range (n + 1), (-1 : ℂ) ^ k * (n.choose k) * F (x + k • s) := by
  simpa only [neg_one_pow_mul_fwdDiff_iter_eq_alternating_sum] using
    hF.neg_one_pow_mul_fwdDiff_iter n hbdd hs

/-- The alternating binomial sums of a bounded positive-definite function are nonnegative at every
"norm point" `a + star a`: complete monotonicity in the finite-difference sense, along the
arithmetic progression starting there. -/
theorem alternating_sum_add_star_self_nonneg (n : ℕ) (hF : IsPositiveDefinite F)
    (hbdd : ∀ a, ‖F (a + star a)‖ ≤ C) (hs : star s = s) (a : M) :
    0 ≤ ∑ k ∈ Finset.range (n + 1), (-1 : ℂ) ^ k * (n.choose k) * F (a + star a + k • s) :=
  (hF.alternating_sum n hbdd hs).add_star_self_nonneg a

end IsPositiveDefinite

end TauCeti
