/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CompletelyMonotone.Closure
public import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# Complete monotonicity is closed under nonnegative affine reparametrization

This file extends the closure API of `TauCeti.IsCompletelyMonotone` (sums, nonnegative scalar
multiples, products and differentiation, in `TauCeti.Analysis.CompletelyMonotone.Basic` and
`TauCeti.Analysis.CompletelyMonotone.Closure`) with closure under **reparametrizing the
argument by a nonnegative affine map** `t ↦ c · t + a` (`c, a ≥ 0`), as called for by the
`OneParameterSemigroups` roadmap's completely-monotone closure programme.

Both nonnegativity conditions are essential and are exactly what keeps the reparametrized
argument inside `[0, ∞)`, where the sign-alternation of `f` lives: scaling `t ↦ c · t` needs
`c ≥ 0` so that `c · t ≥ 0`, and it multiplies the `n`-th alternating derivative by the
nonnegative factor `cⁿ`; shifting `t ↦ t + a` needs `a ≥ 0` so that `t + a ≥ 0`, and it leaves
the alternating derivative unchanged, only evaluated further to the right. A negative scaling
`c < 0` reflects the half-line and turns complete monotonicity into absolute monotonicity, so
the sign condition genuinely fails; a negative shift `a < 0` samples `f` to the left of `0`,
where nothing is assumed.

The scaling step is a direct consequence of Mathlib's `iteratedDerivWithin_comp_const_smul`; the
shift step uses `iteratedDerivWithin_comp_add_const`, whose reparametrized set `a +ᵥ [0, ∞)` is
`[a, ∞)`, and there the alternating derivative of `f` agrees with its value within `[0, ∞)`
because `f` is smooth across the interior of the half-line. Combining the two gives the general
nonnegative affine reparametrization.

These closure lemmas manufacture new completely monotone functions from old: for instance
`t ↦ e^{-x (c t + a)}` is completely monotone whenever `x, c, a ≥ 0`, and every resolvent kernel
`t ↦ (λ + t)⁻¹` reparametrized by a nonnegative affine map stays completely monotone.

## Main declarations

* `TauCeti.IsCompletelyMonotone.comp_const_mul`: if `f` is completely monotone and `0 ≤ c`, then
  `t ↦ f (c · t)` is completely monotone.
* `TauCeti.IsCompletelyMonotone.comp_add_const`: if `f` is completely monotone and `0 ≤ a`, then
  `t ↦ f (t + a)` is completely monotone.
* `TauCeti.IsCompletelyMonotone.sub_comp_add_const`: if `f` is completely monotone and `0 ≤ a`,
  then `t ↦ f t - f (t + a)` is completely monotone.
* `TauCeti.IsCompletelyMonotone.comp_affine`: if `f` is completely monotone and `0 ≤ c`, `0 ≤ a`,
  then `t ↦ f (c · t + a)` is completely monotone.

## References

* R. Schilling, R. Song, Z. Vondraček, *Bernstein Functions: Theory and Applications*
  (de Gruyter, 2nd ed. 2012).
-/

public section

open Set
open scoped ContDiff Pointwise

namespace TauCeti

namespace IsCompletelyMonotone

variable {f : ℝ → ℝ}

/-- Completely monotone functions are closed under scaling the argument by a nonnegative
constant: if `f` is completely monotone and `0 ≤ c`, then `t ↦ f (c · t)` is completely
monotone. The `n`-th alternating derivative is multiplied by the nonnegative factor `cⁿ`. -/
theorem comp_const_mul (hf : IsCompletelyMonotone f) {c : ℝ} (hc : 0 ≤ c) :
    IsCompletelyMonotone (fun t => f (c * t)) := by
  have hmaps : Set.MapsTo (c * ·) (Ici (0 : ℝ)) (Ici 0) := fun t ht =>
    mem_Ici.mpr (mul_nonneg hc (mem_Ici.mp ht))
  refine ⟨hf.contDiffOn.comp (by fun_prop) hmaps, fun n t ht => ?_⟩
  have hct : (0 : ℝ) ≤ c * t := mul_nonneg hc ht
  rw [iteratedDerivWithin_comp_const_smul (mem_Ici.mpr ht) (uniqueDiffOn_Ici 0)
    (hf.contDiffOn.of_le (by exact_mod_cast le_top)) c hmaps, smul_eq_mul]
  have hsign := hf.neg_one_pow_mul_iteratedDerivWithin_nonneg n hct
  have key : (-1 : ℝ) ^ n * (c ^ n * iteratedDerivWithin n f (Ici 0) (c * t)) =
      c ^ n * ((-1) ^ n * iteratedDerivWithin n f (Ici 0) (c * t)) := by ring
  rw [key]
  exact mul_nonneg (pow_nonneg hc n) hsign

/-- Completely monotone functions are closed under shifting the argument by a nonnegative
constant: if `f` is completely monotone and `0 ≤ a`, then `t ↦ f (t + a)` is completely
monotone. The alternating derivative is unchanged, evaluated at the shifted point. -/
theorem comp_add_const (hf : IsCompletelyMonotone f) {a : ℝ} (ha : 0 ≤ a) :
    IsCompletelyMonotone (fun t => f (t + a)) := by
  have hmaps : Set.MapsTo (· + a) (Ici (0 : ℝ)) (Ici 0) := fun t ht =>
    mem_Ici.mpr (add_nonneg (mem_Ici.mp ht) ha)
  have hset : a +ᵥ Ici (0 : ℝ) = Ici a := by
    ext x
    simp only [Set.mem_vadd_set, mem_Ici, vadd_eq_add]
    constructor
    · rintro ⟨y, hy, rfl⟩; linarith
    · intro hx; exact ⟨x - a, by linarith, by ring⟩
  refine ⟨hf.contDiffOn.comp (by fun_prop) hmaps, fun n t ht => ?_⟩
  have hval := congrFun
    (iteratedDerivWithin_comp_add_const (f := f) (n := n) (s := Ici (0 : ℝ)) a) t
  simp only [hset] at hval
  rw [hval]
  have hta : a ≤ t + a := by linarith
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ t + a by linarith) with h0 | h0
  · -- boundary case `t + a = 0`, forcing `t = a = 0`
    have hta0 : t + a = (0 : ℝ) := h0.symm
    have ha0 : a = 0 := by linarith
    subst ha0
    simpa [hta0] using hf.neg_one_pow_mul_iteratedDerivWithin_nonneg n (le_of_eq hta0.symm)
  · -- interior case `t + a > 0`, where the within-derivatives agree with the ordinary one
    have hcat : ContDiffAt ℝ (n : WithTop ℕ∞) f (t + a) :=
      (hf.contDiffOn.contDiffAt
        (Filter.mem_of_superset (isOpen_Ioi.mem_nhds h0) Ioi_subset_Ici_self)).of_le
        (by exact_mod_cast le_top)
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ici a) hcat (mem_Ici.mpr hta)]
    exact hf.neg_one_pow_mul_iteratedDeriv_nonneg n h0

/-- Iterated derivatives within `[0, ∞)` are compatible with a nonnegative shift of the
argument. -/
theorem iteratedDerivWithin_Ici_comp_add_const (hs : ContDiffOn ℝ ∞ f (Ici 0)) (n : ℕ) {a t : ℝ}
    (ha : 0 ≤ a) (ht : 0 ≤ t) :
    iteratedDerivWithin n (fun s => f (s + a)) (Ici 0) t
      = iteratedDerivWithin n f (Ici 0) (t + a) := by
  rcases eq_or_lt_of_le ha with rfl | ha'
  · simp
  · have hset : a +ᵥ Ici (0 : ℝ) = Ici a := by
      ext x
      simp only [Set.mem_vadd_set, mem_Ici, vadd_eq_add]
      exact ⟨by rintro ⟨y, hy, rfl⟩; linarith, fun hx => ⟨x - a, by linarith, by ring⟩⟩
    have hval := congrFun
      (iteratedDerivWithin_comp_add_const (f := f) (n := n) (s := Ici (0 : ℝ)) a) t
    simp only [hset] at hval
    rw [hval]
    have h0 : 0 < t + a := by linarith
    have hcat : ContDiffAt ℝ (n : WithTop ℕ∞) f (t + a) :=
      (hs.contDiffAt (Filter.mem_of_superset (isOpen_Ioi.mem_nhds h0) Ioi_subset_Ici_self)).of_le
        (by exact_mod_cast le_top)
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ici a) hcat
        (mem_Ici.mpr (by linarith)),
      iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ici 0) hcat (mem_Ici.mpr h0.le)]

/-- The forward difference of a completely monotone function, with the sign reversed, is again
completely monotone: every alternating derivative `(-1)ⁿ f⁽ⁿ⁾` is itself completely monotone,
hence nonincreasing, which is exactly the sign condition for `t ↦ f t - f (t + a)`. -/
theorem sub_comp_add_const (hf : IsCompletelyMonotone f) {a : ℝ} (ha : 0 ≤ a) :
    IsCompletelyMonotone (fun t => f t - f (t + a)) := by
  have hshift : IsCompletelyMonotone (fun t => f (t + a)) := hf.comp_add_const ha
  refine ⟨hf.contDiffOn.sub hshift.contDiffOn, fun n t ht => ?_⟩
  have hsub : iteratedDerivWithin n (fun t => f t - f (t + a)) (Ici 0) t
      = iteratedDerivWithin n f (Ici 0) t
        - iteratedDerivWithin n (fun t => f (t + a)) (Ici 0) t := by
    have := iteratedDerivWithin_sub (n := n) (f := f) (g := fun t => f (t + a))
      (s := Ici (0 : ℝ)) (x := t) (mem_Ici.mpr ht) (uniqueDiffOn_Ici 0)
      ((hf.contDiffOn t (mem_Ici.mpr ht)).of_le (by exact_mod_cast le_top))
      ((hshift.contDiffOn t (mem_Ici.mpr ht)).of_le (by exact_mod_cast le_top))
    simpa [Pi.sub_def] using this
  rw [hsub, iteratedDerivWithin_Ici_comp_add_const hf.contDiffOn n ha ht, mul_sub, sub_nonneg]
  have hcm := hf.neg_one_pow_mul_iteratedDerivWithin n
  exact hcm.antitoneOn (mem_Ici.mpr ht) (mem_Ici.mpr (by linarith)) (by linarith)

/-- Completely monotone functions are closed under nonnegative affine reparametrization of the
argument: if `f` is completely monotone and `0 ≤ c`, `0 ≤ a`, then `t ↦ f (c · t + a)` is
completely monotone. -/
theorem comp_affine (hf : IsCompletelyMonotone f) {c a : ℝ} (hc : 0 ≤ c) (ha : 0 ≤ a) :
    IsCompletelyMonotone (fun t => f (c * t + a)) :=
  (hf.comp_add_const ha).comp_const_mul hc

end IsCompletelyMonotone

end TauCeti
