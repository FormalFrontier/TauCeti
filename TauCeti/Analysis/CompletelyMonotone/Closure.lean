/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.CompletelyMonotone.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Closure of completely monotone functions under products and differentiation

This file extends the basic API of `TauCeti.IsCompletelyMonotone` (sums and nonnegative scalar
multiples, in `TauCeti.Analysis.CompletelyMonotone.Basic`) with two further closure properties
called for by the `OneParameterSemigroups` roadmap:

* the **product** of two completely monotone functions is completely monotone, hence so is any
  finite product and any natural power;
* if `f` is completely monotone then so is `t ↦ -f'(t)`, the **negated derivative**.

Both are elementary consequences of the sign-alternation definition. For the product, the
Leibniz rule expands `(-1)ⁿ (fg)⁽ⁿ⁾` as a nonnegative combination
`∑ₖ (n choose k) · [(-1)ᵏ f⁽ᵏ⁾] · [(-1)ⁿ⁻ᵏ g⁽ⁿ⁻ᵏ⁾]` of products of the (nonnegative) alternating
derivatives of `f` and `g`. For the negated derivative, the `(n+1)`-st alternating derivative of
`f` is the `n`-th alternating derivative of `-f'`. Mathlib has the analogous closure lemmas for
`AbsolutelyMonotoneOn` only up to sums and scalar multiples (`AbsolutelyMonotoneOn.add`,
`AbsolutelyMonotoneOn.smul`), so the multiplicative and differential closure built here is new.

These workhorses combine with the prototypes `t ↦ e^{-x t}` to manufacture completely monotone
functions: e.g. any finite sum `∑ⱼ cⱼ e^{-xⱼ t}` with `cⱼ, xⱼ ≥ 0`, or a product like
`t ↦ e^{-x t} / (1 + t)`-style mixtures once their factors are known completely monotone. The
negated-derivative closure is the first step towards the completely-monotone ↔ Bernstein-function
correspondence (a Bernstein function is a nonnegative function whose derivative is completely
monotone).

## Main declarations

* `TauCeti.IsCompletelyMonotone.mul`: completely monotone functions are closed under pointwise
  multiplication.
* `TauCeti.IsCompletelyMonotone.prod`: closure under finite products.
* `TauCeti.IsCompletelyMonotone.pow`: closure under natural powers.
* `TauCeti.IsCompletelyMonotone.neg_one_pow_mul_iteratedDerivWithin`: every alternating
  iterated derivative of a completely monotone function is completely monotone.
* `TauCeti.IsCompletelyMonotone.neg_derivWithin`: the negated derivative within `[0, ∞)` of a
  completely monotone function is completely monotone.

## References

* R. Schilling, R. Song, Z. Vondraček, *Bernstein Functions: Theory and Applications*
  (de Gruyter, 2nd ed. 2012).
-/

public section

open Set
open scoped ContDiff

namespace TauCeti

namespace IsCompletelyMonotone

variable {f g : ℝ → ℝ}

/-- Completely monotone functions are closed under pointwise multiplication. -/
theorem mul (hf : IsCompletelyMonotone f) (hg : IsCompletelyMonotone g) :
    IsCompletelyMonotone (f * g) := by
  refine ⟨hf.contDiffOn.mul hg.contDiffOn, fun n t ht => ?_⟩
  have hmem : t ∈ Ici (0 : ℝ) := mem_Ici.mpr ht
  have hu : UniqueDiffOn ℝ (Ici (0 : ℝ)) := uniqueDiffOn_Ici 0
  have hfn : ContDiffWithinAt ℝ n f (Ici 0) t :=
    (hf.contDiffOn.contDiffWithinAt hmem).of_le (by exact_mod_cast le_top)
  have hgn : ContDiffWithinAt ℝ n g (Ici 0) t :=
    (hg.contDiffOn.contDiffWithinAt hmem).of_le (by exact_mod_cast le_top)
  rw [iteratedDerivWithin_mul hmem hu hfn hgn, Finset.mul_sum]
  refine Finset.sum_nonneg fun i hi => ?_
  have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have e1 := hf.neg_one_pow_mul_iteratedDerivWithin_nonneg i ht
  have e2 := hg.neg_one_pow_mul_iteratedDerivWithin_nonneg (n - i) ht
  have hsign : ((-1 : ℝ)) ^ n = (-1) ^ i * (-1) ^ (n - i) := by
    rw [← pow_add, Nat.add_sub_cancel' hin]
  have key : (-1 : ℝ) ^ n * ((n.choose i : ℝ) * iteratedDerivWithin i f (Ici 0) t
        * iteratedDerivWithin (n - i) g (Ici 0) t)
      = (n.choose i : ℝ) * ((-1) ^ i * iteratedDerivWithin i f (Ici 0) t)
        * ((-1) ^ (n - i) * iteratedDerivWithin (n - i) g (Ici 0) t) := by
    rw [hsign]; ring
  rw [key]
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) e1) e2

/-- Completely monotone functions are closed under finite products. -/
theorem prod {ι : Type*} {s : Finset ι} {f : ι → ℝ → ℝ} (hf : ∀ i ∈ s, IsCompletelyMonotone (f i)) :
    IsCompletelyMonotone (fun t => ∏ i ∈ s, f i t) := by
  have h := Finset.prod_induction f IsCompletelyMonotone
    (fun _ _ => IsCompletelyMonotone.mul) (isCompletelyMonotone_const zero_le_one) hf
  have heq : (∏ i ∈ s, f i) = fun t => ∏ i ∈ s, f i t := funext fun t => Finset.prod_apply t s f
  rwa [heq] at h

/-- Completely monotone functions are closed under taking natural powers. -/
theorem pow (hf : IsCompletelyMonotone f) (k : ℕ) : IsCompletelyMonotone (f ^ k) := by
  induction k with
  | zero => rw [pow_zero]; exact isCompletelyMonotone_const zero_le_one
  | succ k ih => rw [pow_succ]; exact ih.mul hf

/-- Every alternating iterated derivative of a completely monotone function is completely
monotone. -/
theorem neg_one_pow_mul_iteratedDerivWithin (hf : IsCompletelyMonotone f) (k : ℕ) :
    IsCompletelyMonotone (fun t => (-1 : ℝ) ^ k * iteratedDerivWithin k f (Ici 0) t) := by
  have hu : UniqueDiffOn ℝ (Ici (0 : ℝ)) := uniqueDiffOn_Ici 0
  have hcont : ContDiffOn ℝ ∞ (iteratedDerivWithin k f (Ici 0)) (Ici 0) := by
    induction k with
    | zero => simpa [iteratedDerivWithin_zero] using hf.contDiffOn
    | succ k ih =>
        simpa [iteratedDerivWithin_succ] using ih.derivWithin (m := ∞) hu (by simp)
  refine ⟨?_, fun n t ht => ?_⟩
  · simpa [smul_eq_mul] using hcont.const_smul ((-1 : ℝ) ^ k)
  have hshift :
      iteratedDerivWithin n (iteratedDerivWithin k f (Ici 0)) (Ici 0) =
        iteratedDerivWithin (n + k) f (Ici 0) := by
    induction n with
    | zero => simp [iteratedDerivWithin_zero]
    | succ n ih =>
        rw [iteratedDerivWithin_succ, ih, ← iteratedDerivWithin_succ]
        congr 1
        omega
  have hsign := hf.neg_one_pow_mul_iteratedDerivWithin_nonneg (n + k) ht
  have hiter :
      iteratedDerivWithin n
          (fun t => (-1 : ℝ) ^ k * iteratedDerivWithin k f (Ici 0) t) (Ici 0) t =
        (-1 : ℝ) ^ k * iteratedDerivWithin (n + k) f (Ici 0) t := by
    rw [iteratedDerivWithin_const_mul_field, hshift]
  rw [hiter]
  have key :
      (-1 : ℝ) ^ n * ((-1 : ℝ) ^ k * iteratedDerivWithin (n + k) f (Ici 0) t) =
        (-1 : ℝ) ^ (n + k) * iteratedDerivWithin (n + k) f (Ici 0) t := by
    rw [pow_add]
    ring
  rwa [key]

/-- The negated derivative within `[0, ∞)` of a completely monotone function is completely
monotone. -/
theorem neg_derivWithin (hf : IsCompletelyMonotone f) :
    IsCompletelyMonotone (fun t => -derivWithin f (Ici 0) t) := by
  simpa [pow_one, iteratedDerivWithin_one] using hf.neg_one_pow_mul_iteratedDerivWithin 1

end IsCompletelyMonotone

end TauCeti
