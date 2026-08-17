/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic

/-!
# Prescribing the signs of a number field element at the real places

Weak approximation says that a number field `K` is dense in the product of its completions at the
infinite places; Mathlib records the diagonal form of this,
`NumberField.InfinitePlace.denseRange_algebraMap_pi`, on the product of the copies of `K` carrying
the topology of each infinite place. This file turns that topological statement into the
arithmetic one it is used for: an element of `K` may be prescribed, independently at each real
place, to be positive or negative there.

The passage is the usual one. Approximating the tuple whose entry at a place is `1` or `-1` to
within `1` forces the sign of each real embedding of the approximating element, because a real
number within distance `1` of `±1` has the sign of `±1`; the same estimate at any one place, real
or complex, keeps the element away from `0`.

## Main results

* `NumberField.exists_forall_infinitePlace_sub_lt`: weak approximation at the infinite
  places in `ε`-`δ` form, with targets in `K` measured by the places themselves.
* `NumberField.exists_ne_zero_forall_isReal_pos`: a nonzero element of `K` whose real
  embeddings have prescribed signs.
* `NumberField.exists_ne_zero_neg_iff_mem`: the same statement with the prescription given
  as the set of real places at which the element is to be negative.

## References

The weak approximation theorem for pairwise inequivalent absolute values is Artin--Whaples; see
E. Artin and G. Whaples, *Axiomatic characterization of fields by the product formula for
valuations*, Bull. Amer. Math. Soc. **51** (1945), and, for the number field statement,
J. W. S. Cassels and A. Fröhlich, *Algebraic Number Theory*, Chapter II.
-/

public section

open NumberField NumberField.InfinitePlace

namespace NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- **Weak approximation at the infinite places.** Given one target `a v : K` and one positive
tolerance `r v` for each infinite place `v` of a number field, some single `x : K` is within `r v`
of every target, as measured by the place at which that target was prescribed.

This is `NumberField.InfinitePlace.denseRange_algebraMap_pi` with the topology of the finite
product unwound into the individual places. -/
theorem exists_forall_infinitePlace_sub_lt (a : InfinitePlace K → K)
    (r : InfinitePlace K → ℝ) (hr : ∀ v, 0 < r v) :
    ∃ x : K, ∀ v : InfinitePlace K, v (x - a v) < r v := by
  let δ := Finset.univ.inf' Finset.univ_nonempty r
  have hδ : 0 < δ := (Finset.lt_inf'_iff _).2 fun v _ => hr v
  obtain ⟨x, hx⟩ := Metric.denseRange_iff.mp (InfinitePlace.denseRange_algebraMap_pi K)
    (fun v => WithAbs.toAbs v.1 (a v)) δ hδ
  refine ⟨x, fun v => ?_⟩
  have h := (dist_pi_lt_iff hδ).mp hx v
  rw [dist_eq_norm, WithAbs.norm_eq_apply_ofAbs, WithAbs.ofAbs_sub] at h
  rw [coe_apply, AbsoluteValue.map_sub]
  exact h.trans_le (Finset.inf'_le r (Finset.mem_univ v))

/-- **A nonzero element with prescribed signs at the real places.** For any family of nonzero
reals `s`, indexed by the real infinite places of a number field `K`, some nonzero `x : K` has
`s w` and the image of `x` under the real embedding at `w` of the same sign, at every real place
`w` simultaneously. -/
theorem exists_ne_zero_forall_isReal_pos (s : {w : InfinitePlace K // w.IsReal} → ℝ)
    (hs : ∀ w, s w ≠ 0) :
    ∃ x : K, x ≠ 0 ∧
      ∀ w : {w : InfinitePlace K // w.IsReal}, 0 < s w * embedding_of_isReal w.2 x := by
  classical
  -- Aim at `1` where the prescribed sign is positive and at `-1` where it is negative; at a
  -- complex place the target is irrelevant, and `1` serves.
  set a : InfinitePlace K → K := fun v =>
    if h : v.IsReal then (if 0 < s ⟨v, h⟩ then 1 else -1) else 1 with ha
  have hreal : ∀ w : {w : InfinitePlace K // w.IsReal}, a w.1 = if 0 < s w then 1 else -1 := by
    intro w
    simp [ha, w.2]
  -- Every target has absolute value `1` at its own place, so it stays away from `0`.
  have habs : ∀ v : InfinitePlace K, v (a v) = 1 := by
    intro v
    have h : a v = 1 ∨ a v = -1 := by
      simp only [ha]
      split_ifs <;> simp
    rw [coe_apply]
    rcases h with h | h <;> rw [h] <;> simp
  obtain ⟨x, hx⟩ := exists_forall_infinitePlace_sub_lt a (fun _ => 1) fun _ => one_pos
  have hx0 : x ≠ 0 := by
    rintro rfl
    have h := hx (Classical.arbitrary (InfinitePlace K))
    rw [coe_apply, zero_sub, AbsoluteValue.map_neg, ← coe_apply, habs] at h
    exact lt_irrefl 1 h
  refine ⟨x, hx0, fun w => ?_⟩
  -- At a real place the place is the absolute value of the real embedding.
  have hσ : |embedding_of_isReal w.2 x - embedding_of_isReal w.2 (a w.1)| < 1 := by
    rw [← map_sub, ← Real.norm_eq_abs, norm_embedding_of_isReal]
    exact hx w.1
  by_cases h' : 0 < s w
  · have hax : a w.1 = 1 := by rw [hreal w]; simp [h']
    rw [hax, map_one, abs_lt] at hσ
    exact mul_pos h' (by linarith [hσ.1])
  · have hax : a w.1 = -1 := by rw [hreal w]; simp [h']
    rw [hax, map_neg, map_one, sub_neg_eq_add, abs_lt] at hσ
    exact mul_pos_of_neg_of_neg (lt_of_le_of_ne (not_lt.mp h') (hs w)) (by linarith [hσ.2])

/-- **A nonzero element of `K` negative at exactly a prescribed set of real places.** Since the
real places at which an element is negative determine its sign pattern, this is
`NumberField.exists_ne_zero_forall_isReal_pos` with the pattern presented as a set. -/
theorem exists_ne_zero_neg_iff_mem (S : Set {w : InfinitePlace K // w.IsReal}) :
    ∃ x : K, x ≠ 0 ∧
      ∀ w : {w : InfinitePlace K // w.IsReal}, embedding_of_isReal w.2 x < 0 ↔ w ∈ S := by
  classical
  obtain ⟨x, hx0, hx⟩ :=
    exists_ne_zero_forall_isReal_pos (K := K) (fun w => if w ∈ S then -1 else 1)
      fun w => by split_ifs <;> norm_num
  refine ⟨x, hx0, fun w => ?_⟩
  have h := hx w
  by_cases hw : w ∈ S
  · simp only [hw, ite_true, neg_one_mul, neg_pos] at h
    exact iff_of_true h hw
  · simp only [hw, ite_false, one_mul] at h
    exact iff_of_false (asymm h) hw

end NumberField
