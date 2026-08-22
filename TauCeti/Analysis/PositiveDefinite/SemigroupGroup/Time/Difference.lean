/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Analysis.Normed.Group.Pointwise
import TauCeti.Analysis.PositiveDefinite.Kernel.Kolmogorov
public import TauCeti.Analysis.PositiveDefinite.Function.Difference
public import TauCeti.Analysis.PositiveDefinite.SemigroupGroup.Time.Axis

/-!
# Time differences of bounded semigroup-group positive-definite functions

This file proves the alternating finite-difference property needed for the existence half of the
Berg--Christensen--Ressel representation theorem. If `F` is bounded and positive definite on the
involutive semigroup `ℝ≥0 × V`, then every iterated time difference built from

`(t, v) ↦ F (t, v) - F (t + h, v)`

is again positive definite.

The argument uses the canonical Kolmogorov decomposition of the BCR kernel. For any finite linear
combination of feature vectors, translating every time coordinate by `s` gives a vector `w s` whose
Gram function depends only on the sum of the two translation parameters. Its diagonal values form
a bounded nonnegative log-convex sequence along any arithmetic progression. Such a sequence is
decreasing, which is exactly positivity of the time difference.

Applying Bochner's theorem to those differences makes the corresponding alternating differences
of the spatial Bochner measures positive, the time-regularity input required to assemble the BCR
representing measure.

An iterated time difference expands into the alternating binomial sum
`(t, v) ↦ ∑ k ≤ n, (-1) ^ k (n choose k) F (t + k • h, v)`, so that sum is positive definite too.
Positive definiteness is a statement about quadratic forms, not a pointwise sign: nonnegativity of
the values themselves is asserted only along the zero-spatial axis, where positive definiteness
specializes to the alternating sign law `0 ≤ (-1) ^ n * Δ_[h]^[n] (fun s => F (s, 0)) t` and hence
to the classical statement that `t ↦ F (t, 0)` is *completely monotone in the finite-difference
sense*:

`0 ≤ ∑ k ≤ n, (-1) ^ k (n choose k) F (t + k h, 0)`.

Those one-variable statements are exactly the generic `TauCeti.IsPositiveDefinite` theory of
`TauCeti/Analysis/PositiveDefinite/Function/Difference.lean`, applied to the positive-definite
function `t ↦ F (t, 0)` on `ℝ≥0` with its trivial involution, and are obtained from it here.
Accordingly they assume only that the *time axis* is bounded, `‖F (t, 0)‖ ≤ C`, rather than that
`F` is bounded on all of `ℝ≥0 × V`.

## Main declarations

* `TauCeti.timeDifference`: the one-step alternating time difference, the negative of Mathlib's
  forward difference `fwdDiff` applied in the time coordinate.
* `TauCeti.listTimeDifference`: the alternating difference along a finite list of time steps, and
  `TauCeti.iteratedTimeDifference`: its equal-step specialization.
* `TauCeti.iteratedTimeDifference_eq_alternating_sum`: the binomial expansion of an iterated time
  difference.
* `TauCeti.IsSemigroupGroupPD.timeDifference`: a bounded BCR-positive-definite function remains
  positive definite after subtracting a nonnegative forward time translate.
* `TauCeti.IsSemigroupGroupPD.listTimeDifference` and
  `TauCeti.IsSemigroupGroupPD.iteratedTimeDifference`: every alternating time difference of a
  bounded BCR-positive-definite function, along arbitrary or repeated steps, is positive definite,
  and `TauCeti.IsSemigroupGroupPD.alternating_sum` says the same in binomial form.
* `TauCeti.isBounded_range_listTimeDifference` and
  `TauCeti.isBounded_range_iteratedTimeDifference`: those differences stay bounded, so they can be
  differenced again.
* `TauCeti.IsSemigroupGroupPD.timeAxis_alternating_sum_nonneg`,
  `TauCeti.IsSemigroupGroupPD.timeAxis_alternating_sum_re_nonneg` and
  `TauCeti.IsSemigroupGroupPD.timeAxis_iteratedTimeDifference_nonneg`: a bounded time axis
  `t ↦ F (t, 0)` is completely monotone in the finite-difference sense, in the order of `ℂ` and
  for real parts.
* `TauCeti.IsSemigroupGroupPD.timeAxis_sub_nonneg` and
  `TauCeti.IsSemigroupGroupPD.timeAxis_re_antitone`: a bounded time axis is nonincreasing.

## References

* C. Berg, J. P. R. Christensen, P. Ressel, *Harmonic Analysis on Semigroups* (GTM 100, 1984),
  Theorem 4.1.13 and its bounded-semigroup argument.

* Roadmap: `TauCetiRoadmap/OneParameterSemigroups/README.md`, Part C, Milestone 2
  ("BCR semigroup--Bochner").
-/

public section

open ComplexConjugate InnerProductSpace Set
open scoped ComplexOrder NNReal Pointwise fwdDiff

namespace TauCeti

private lemma antitone_of_nonneg_logConvex_bddAbove {u : ℕ → ℝ}
    (hnonneg : ∀ n, 0 ≤ u n)
    (hlog : ∀ n, u (n + 1) ^ 2 ≤ u n * u (n + 2))
    (hbdd : BddAbove (range u)) : Antitone u := by
  suffices hstep : ∀ n, u (n + 1) ≤ u n by
    exact antitone_nat_of_succ_le hstep
  intro n
  by_contra hle
  have hlt : u n < u (n + 1) := lt_of_not_ge hle
  let d := u (n + 1) - u n
  have hd : 0 < d := sub_pos.mpr hlt
  have hinc : ∀ k, d ≤ u (n + k + 1) - u (n + k) := by
    intro k
    induction k with
    | zero => simp [d]
    | succ k ih =>
        have hmono : u (n + k) ≤ u (n + k + 1) := by nlinarith [ih]
        have hpos : 0 < u (n + k) := by
          by_contra h
          have hz : u (n + k) = 0 := le_antisymm (not_lt.mp h) (hnonneg _)
          have := hlog (n + k)
          have hu1pos : 0 < u (n + k + 1) := by nlinarith [ih, hd]
          rw [hz, zero_mul] at this
          exact (not_le_of_gt (sq_pos_of_pos hu1pos)) this
        have hlog' := hlog (n + k)
        have hnext : u (n + k + 1) - u (n + k) ≤
            u (n + k + 2) - u (n + k + 1) := by
          nlinarith
        simpa only [Nat.add_assoc, Nat.succ_eq_add_one] using ih.trans hnext
  have hlower : ∀ k : ℕ, u n + (k : ℝ) * d ≤ u (n + k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        have hk := hinc k
        calc
          u n + (↑(k + 1) : ℝ) * d = (u n + (k : ℝ) * d) + d := by
            push_cast
            ring
          _ ≤ u (n + k) + d := by simpa [add_comm] using add_le_add_right ih d
          _ ≤ u (n + k + 1) := by linarith
          _ = u (n + (k + 1)) := by congr 1
  obtain ⟨B, hB⟩ := hbdd
  obtain ⟨k : ℕ, hk⟩ := exists_nat_gt ((B - u n) / d)
  have hrange : u (n + k) ≤ B := hB ⟨n + k, rfl⟩
  have hk' : B - u n < (k : ℝ) * d := (div_lt_iff₀ hd).mp (by exact_mod_cast hk)
  nlinarith [hlower k]

universe u

section

variable {V : Type u} {F : ℝ≥0 × V → ℂ}

/-- The first alternating time difference with step `h`:
`timeDifference h F (t, v) = F (t, v) - F (t + h, v)`. It is the negative of Mathlib's forward
difference `fwdDiff` applied in the time coordinate. -/
def timeDifference (h : ℝ≥0) (F : ℝ≥0 × V → ℂ) : ℝ≥0 × V → ℂ :=
  fun p => -fwdDiff h (fun t => F (t, p.2)) p.1

/-- The first time difference evaluated at a point. -/
@[simp]
theorem timeDifference_apply (h : ℝ≥0) (F : ℝ≥0 × V → ℂ) (p : ℝ≥0 × V) :
    timeDifference h F p = F p - F (p.1 + h, p.2) := by
  simp [timeDifference, fwdDiff]

/-- The time difference with step zero is the zero function. -/
@[simp]
theorem timeDifference_zero (F : ℝ≥0 × V → ℂ) : timeDifference 0 F = 0 := by
  ext p
  simp

/-- The alternating time difference along a finite list of steps, one application of
`timeDifference` per entry of the list. -/
def listTimeDifference (l : List ℝ≥0) (F : ℝ≥0 × V → ℂ) : ℝ≥0 × V → ℂ :=
  l.foldr timeDifference F

/-- Differencing along no steps at all is the identity. -/
@[simp]
theorem listTimeDifference_nil (F : ℝ≥0 × V → ℂ) : listTimeDifference [] F = F := by
  rw [listTimeDifference, List.foldr_nil]

/-- Differencing along `h :: l` is one further first difference with step `h`. -/
@[simp]
theorem listTimeDifference_cons (h : ℝ≥0) (l : List ℝ≥0) (F : ℝ≥0 × V → ℂ) :
    listTimeDifference (h :: l) F = timeDifference h (listTimeDifference l F) := by
  rw [listTimeDifference, List.foldr_cons, ← listTimeDifference]

/-- The `n`-th alternating time difference, obtained by iterating `timeDifference h`. -/
def iteratedTimeDifference (n : ℕ) (h : ℝ≥0) (F : ℝ≥0 × V → ℂ) : ℝ≥0 × V → ℂ :=
  (timeDifference h)^[n] F

/-- The zeroth time difference is the original function. -/
@[simp]
theorem iteratedTimeDifference_zero (h : ℝ≥0) (F : ℝ≥0 × V → ℂ) :
    iteratedTimeDifference 0 h F = F := by
  simp [iteratedTimeDifference]

/-- The successor time difference is one further first difference. -/
@[simp]
theorem iteratedTimeDifference_succ (n : ℕ) (h : ℝ≥0) (F : ℝ≥0 × V → ℂ) :
    iteratedTimeDifference (n + 1) h F = timeDifference h (iteratedTimeDifference n h F) := by
  simp only [iteratedTimeDifference, Function.iterate_succ_apply']

/-- Iterating the step `h` is differencing along the constant list of `n` copies of `h`. -/
theorem iteratedTimeDifference_eq_listTimeDifference (n : ℕ) (h : ℝ≥0) (F : ℝ≥0 × V → ℂ) :
    iteratedTimeDifference n h F = listTimeDifference (List.replicate n h) F := by
  induction n with
  | zero => simp
  | succ n ih => rw [iteratedTimeDifference_succ, ih, List.replicate_succ, listTimeDifference_cons]

/-- At a fixed spatial coordinate, the `n`-th time difference is the alternating `n`-th forward
difference of the one-variable function `t ↦ F (t, v)`. This is the bridge to the generic
finite-difference theory of `TauCeti/Analysis/PositiveDefinite/Function/Difference.lean`. -/
theorem iteratedTimeDifference_apply_eq_fwdDiff (n : ℕ) (h : ℝ≥0) (F : ℝ≥0 × V → ℂ) (t : ℝ≥0)
    (v : V) :
    iteratedTimeDifference n h F (t, v)
      = (-1 : ℂ) ^ n * Δ_[h]^[n] (fun s : ℝ≥0 => F (s, v)) t := by
  induction n generalizing F with
  | zero => simp
  | succ n ih =>
      have hsucc : iteratedTimeDifference (n + 1) h F
          = iteratedTimeDifference n h (timeDifference h F) :=
        Function.iterate_succ_apply _ _ _
      have hstep : (fun s : ℝ≥0 => timeDifference h F (s, v))
          = -Δ_[h] fun s : ℝ≥0 => F (s, v) := by
        funext s
        simp [timeDifference, fwdDiff]
      rw [hsucc, ih, hstep]
      exact congrFun (neg_one_pow_mul_fwdDiff_iter_succ n (fun s : ℝ≥0 => F (s, v)) h) t

/-- **The binomial expansion of an iterated time difference.** This is the form in which the
measure-theoretic half of the Berg--Christensen--Ressel representation slices the differences by
time. -/
theorem iteratedTimeDifference_eq_alternating_sum (n : ℕ) (h : ℝ≥0) (F : ℝ≥0 × V → ℂ) :
    iteratedTimeDifference n h F = fun p : ℝ≥0 × V =>
      ∑ k ∈ Finset.range (n + 1), (-1 : ℂ) ^ k * (n.choose k) * F (p.1 + k • h, p.2) := by
  funext p
  obtain ⟨t, v⟩ := p
  rw [iteratedTimeDifference_apply_eq_fwdDiff, neg_one_pow_mul_fwdDiff_iter_eq_alternating_sum]

/-- Boundedness is preserved by taking a first time difference. -/
theorem isBounded_range_timeDifference (hbounded : Bornology.IsBounded (range F)) (h : ℝ≥0) :
    Bornology.IsBounded (range (timeDifference h F)) :=
  (hbounded.sub hbounded).subset <| by
    rintro _ ⟨p, rfl⟩
    exact ⟨F p, mem_range_self p, F (p.1 + h, p.2), mem_range_self _,
      (timeDifference_apply h F p).symm⟩

/-- Boundedness is preserved by differencing along any finite list of steps. -/
theorem isBounded_range_listTimeDifference (hbounded : Bornology.IsBounded (range F))
    (l : List ℝ≥0) : Bornology.IsBounded (range (listTimeDifference l F)) := by
  induction l with
  | nil => simpa using hbounded
  | cons h l ih => simpa using isBounded_range_timeDifference ih h

/-- Boundedness is preserved by every iterated time difference. -/
theorem isBounded_range_iteratedTimeDifference (hbounded : Bornology.IsBounded (range F)) (n : ℕ)
    (h : ℝ≥0) : Bornology.IsBounded (range (iteratedTimeDifference n h F)) := by
  rw [iteratedTimeDifference_eq_listTimeDifference]
  exact isBounded_range_listTimeDifference hbounded _

end

variable {V : Type u} [AddCommGroup V] {F : ℝ≥0 × V → ℂ} {C : ℝ}

namespace IsSemigroupGroupPD

/-- A bounded BCR-positive-definite function remains positive definite after subtracting a forward
time translate. In other words, for every `h : ℝ≥0`, the first alternating time difference
`(t, v) ↦ F (t, v) - F (t + h, v)` is semigroup-group positive definite. -/
theorem timeDifference (hF : IsSemigroupGroupPD F)
    (hbounded : Bornology.IsBounded (range F)) (h : ℝ≥0) :
    IsSemigroupGroupPD (TauCeti.timeDifference h F) := by
  rw [isSemigroupGroupPD_iff_posSemidef]
  refine posSemidef_iff_finite_sum.{0, u, u}.mpr ?_
  refine ⟨fun p q => ?_, ?_⟩
  · rw [timeDifference_apply, timeDifference_apply, star_sub]
    -- Express scalar star as complex conjugation so the BCR symmetry lemma applies.
    change conj (F (p.1 + q.1, p.2 - q.2)) -
        conj (F (p.1 + q.1 + h, p.2 - q.2)) = _
    rw [hF.conj_symm p q]
    rw [add_right_comm p.1 q.1 h]
    have hs := hF.conj_symm (p.1 + h, p.2) q
    rw [hs]
    simp only [add_comm, add_left_comm]
  intro ι _ p c
  classical
  let K : (ℝ≥0 × V) → (ℝ≥0 × V) → ℂ :=
    fun a b => F (a.1 + b.1, a.2 - b.2)
  let hK : Matrix.PosSemidef K := hF.posSemidef
  let w (s : ℝ≥0) : Matrix.PosSemidef.KolmogorovSpace hK :=
    ∑ i, c i • hK.kolmogorovFeature ((p i).1 + s, (p i).2)
  let z (s : ℝ≥0) : ℂ := ∑ i, ∑ j, star (c i) *
    F ((p i).1 + (p j).1 + s, (p i).2 - (p j).2) * c j
  let q (s : ℝ≥0) : ℝ := RCLike.re (z s)
  have hinner (a b : ℝ≥0) : ⟪w a, w b⟫_ℂ = z (a + b) := by
    simp only [w, sum_inner, inner_sum, inner_smul_left, inner_smul_right,
      Matrix.PosSemidef.inner_kolmogorovFeature, K, RCLike.star_def, z]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [add_add_add_comm]
    ring
  have hq_inner (s : ℝ≥0) : q s = ‖w (s / 2)‖ ^ 2 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ) (w (s / 2)), hinner, add_halves]
  have hq_nonneg (s : ℝ≥0) : 0 ≤ q s := by rw [hq_inner]; positivity
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hbounded
  let B : ℝ := ∑ i, ∑ j, ‖c i‖ * C * ‖c j‖
  have hq_le (s : ℝ≥0) : q s ≤ B := by
    calc
      q s ≤ ‖z s‖ := RCLike.re_le_norm _
      _ ≤ ∑ i, ‖∑ j, star (c i) * F ((p i).1 + (p j).1 + s,
          (p i).2 - (p j).2) * c j‖ := by
            simpa only [z] using norm_sum_le (Finset.univ : Finset ι) fun i =>
              ∑ j, star (c i) * F ((p i).1 + (p j).1 + s, (p i).2 - (p j).2) * c j
      _ ≤ ∑ i, ∑ j, ‖star (c i) * F ((p i).1 + (p j).1 + s,
          (p i).2 - (p j).2) * c j‖ := by
            apply Finset.sum_le_sum
            intro (i : ι) _
            exact norm_sum_le (Finset.univ : Finset ι) fun j =>
              star (c i) * F ((p i).1 + (p j).1 + s, (p i).2 - (p j).2) * c j
      _ ≤ B := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        simp only [norm_mul, norm_star]
        gcongr
        exact hC _ ⟨_, rfl⟩
  let u (n : ℕ) : ℝ := q (n • h)
  have hu_nonneg (n : ℕ) : 0 ≤ u n := hq_nonneg _
  have hu_bdd : BddAbove (range u) := ⟨B, by rintro _ ⟨n, rfl⟩; exact hq_le _⟩
  have hu_log (n : ℕ) : u (n + 1) ^ 2 ≤ u n * u (n + 2) := by
    let a := (n • h) / 2
    let b := ((n + 2) • h) / 2
    let m := (n + 1) • h
    have hmid : (n • h) / 2 + ((n + 2) • h) / 2 = (n + 1) • h := by
      ext
      simp only [NNReal.coe_add, NNReal.coe_div, NNReal.coe_ofNat, NNReal.coe_nsmul]
      ring
    have hcross : ⟪w a, w b⟫_ℂ = (q m : ℂ) := by
      calc
        ⟪w a, w b⟫_ℂ = z m := by
          rw [hinner]
          exact congrArg z (by simpa only [a, b, m] using hmid)
        _ = ⟪w (m / 2), w (m / 2)⟫_ℂ := by rw [hinner, add_halves]
        _ = (‖w (m / 2)‖ : ℂ) ^ 2 := inner_self_eq_norm_sq_to_K _
        _ = (q m : ℂ) := by rw [hq_inner]; norm_cast
    have hnorm := norm_inner_le_norm (𝕜 := ℂ) (w a) (w b)
    have hsquare : ‖⟪w a, w b⟫_ℂ‖ ^ 2 ≤ (‖w a‖ * ‖w b‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2 hnorm
    rw [hcross, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hq_nonneg m), mul_pow,
      ← hq_inner, ← hq_inner] at hsquare
    simpa [u, a, b, m] using hsquare
  have hanti : Antitone u := antitone_of_nonneg_logConvex_bddAbove hu_nonneg hu_log hu_bdd
  have hdiff : 0 ≤ q 0 - q h := by
    simpa [u] using sub_nonneg.mpr (hanti (Nat.zero_le 1))
  have hz_eq (s : ℝ≥0) : z s = (q s : ℂ) := by
    calc
      z s = ⟪w (s / 2), w (s / 2)⟫_ℂ := by rw [hinner, add_halves]
      _ = (‖w (s / 2)‖ : ℂ) ^ 2 := inner_self_eq_norm_sq_to_K _
      _ = (q s : ℂ) := by rw [hq_inner]; norm_cast
  have hnonneg : (0 : ℂ) ≤ (q 0 : ℂ) - (q h : ℂ) := by
    rw [Complex.nonneg_iff]
    exact ⟨by simpa using hdiff, by simp⟩
  rw [← hz_eq 0, ← hz_eq h] at hnonneg
  refine hnonneg.trans_eq ?_
  simp only [z]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  simp only [add_zero, timeDifference_apply]
  ring_nf

/-- Every alternating time difference along a finite list of steps of a bounded
BCR-positive-definite function is again semigroup-group positive definite. -/
theorem listTimeDifference (hF : IsSemigroupGroupPD F)
    (hbounded : Bornology.IsBounded (range F)) (l : List ℝ≥0) :
    IsSemigroupGroupPD (TauCeti.listTimeDifference l F) := by
  induction l with
  | nil => simpa using hF
  | cons h l ih =>
      rw [TauCeti.listTimeDifference_cons]
      exact ih.timeDifference (isBounded_range_listTimeDifference hbounded l) h

/-- Every iterated alternating time difference of a bounded BCR-positive-definite function is
again semigroup-group positive definite. -/
theorem iteratedTimeDifference (hF : IsSemigroupGroupPD F)
    (hbounded : Bornology.IsBounded (range F)) (n : ℕ) (h : ℝ≥0) :
    IsSemigroupGroupPD (TauCeti.iteratedTimeDifference n h F) := by
  rw [TauCeti.iteratedTimeDifference_eq_listTimeDifference]
  exact hF.listTimeDifference hbounded _

/-- **The alternating iterated time differences, expanded as binomial sums, are semigroup-group
positive definite.** This is `IsSemigroupGroupPD.iteratedTimeDifference` with the differencing
operator resolved into an explicit alternating sum over an arithmetic progression of times. -/
theorem alternating_sum (hF : IsSemigroupGroupPD F)
    (hbounded : Bornology.IsBounded (range F)) (n : ℕ) (h : ℝ≥0) :
    IsSemigroupGroupPD fun p : ℝ≥0 × V =>
      ∑ k ∈ Finset.range (n + 1), (-1 : ℂ) ^ k * (n.choose k) * F (p.1 + k • h, p.2) := by
  rw [← TauCeti.iteratedTimeDifference_eq_alternating_sum]
  exact hF.iteratedTimeDifference hbounded n h

/-! ## The zero-spatial axis

Positive definiteness constrains quadratic forms, not values. The values themselves are pinned
down along the zero-spatial axis, where the results above specialize to the classical complete
monotonicity of `t ↦ F (t, 0)`. Only that axis has to be bounded for this: the statements below are
the generic one-variable theory applied to the positive-definite function `t ↦ F (t, 0)` on `ℝ≥0`
with its trivial involution, evaluated at the norm point `t / 2 + star (t / 2) = t`.
-/

/-- **A semigroup-group positive-definite function with bounded time axis is completely monotone
along that axis, in the finite-difference sense:** all alternating binomial sums of its values
along an arithmetic progression of times are nonnegative. This is the form in which the Laplace
half of the Berg--Christensen--Ressel representation consumes positive definiteness. -/
theorem timeAxis_alternating_sum_nonneg (n : ℕ) (hF : IsSemigroupGroupPD F)
    (hbdd : ∀ t : ℝ≥0, ‖F (t, 0)‖ ≤ C) (h t : ℝ≥0) :
    0 ≤ ∑ k ∈ Finset.range (n + 1), (-1 : ℂ) ^ k * (n.choose k) * F (t + k • h, (0 : V)) := by
  have haxis := hF.timeAxis_isPositiveDefinite.alternating_sum_add_star_self_nonneg n (C := C)
    (fun a => hbdd _) (star_trivial h) (t / 2)
  simpa only [star_trivial, add_halves] using haxis

/-- The iterated time difference of a semigroup-group positive-definite function whose time axis is
bounded is nonnegative along the zero-spatial axis. Only the time axis has to be bounded, in
contrast with `IsSemigroupGroupPD.iteratedTimeDifference`. -/
theorem timeAxis_iteratedTimeDifference_nonneg (n : ℕ) (hF : IsSemigroupGroupPD F)
    (hbdd : ∀ t : ℝ≥0, ‖F (t, 0)‖ ≤ C) (h t : ℝ≥0) :
    0 ≤ TauCeti.iteratedTimeDifference n h F (t, (0 : V)) := by
  rw [TauCeti.iteratedTimeDifference_eq_alternating_sum]
  exact hF.timeAxis_alternating_sum_nonneg n hbdd h t

/-- The real-part form of `IsSemigroupGroupPD.timeAxis_alternating_sum_nonneg`: the alternating
binomial sums of `t ↦ (F (t, 0)).re` are nonnegative. This is the shape consumed by the
real-valued complete-monotonicity API. -/
theorem timeAxis_alternating_sum_re_nonneg (n : ℕ) (hF : IsSemigroupGroupPD F)
    (hbdd : ∀ t : ℝ≥0, ‖F (t, 0)‖ ≤ C) (h t : ℝ≥0) :
    0 ≤ ∑ k ∈ Finset.range (n + 1), (-1 : ℝ) ^ k * n.choose k * (F (t + k • h, (0 : V))).re := by
  have hre := (Complex.nonneg_iff.mp (hF.timeAxis_alternating_sum_nonneg n hbdd h t)).1
  rw [Complex.re_sum] at hre
  refine le_of_le_of_eq hre (Finset.sum_congr rfl fun k _ => ?_)
  have hcast : ((-1 : ℂ) ^ k * (n.choose k) : ℂ) = (((-1 : ℝ) ^ k * n.choose k : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hcast, Complex.re_ofReal_mul]

/-- Along the zero-spatial axis, a later value of a semigroup-group positive-definite function with
bounded time axis is dominated by an earlier one, in the order of `ℂ`. -/
theorem timeAxis_sub_nonneg (hF : IsSemigroupGroupPD F) (hbdd : ∀ t : ℝ≥0, ‖F (t, 0)‖ ≤ C)
    (h t : ℝ≥0) : 0 ≤ F (t, (0 : V)) - F (t + h, 0) := by
  have haxis := hF.timeAxis_isPositiveDefinite.sub_shift_add_star_self_nonneg (C := C)
    (fun a => hbdd _) (star_trivial h) (t / 2)
  simpa only [star_trivial, add_halves] using haxis

/-- The bounded time axis of a semigroup-group positive-definite function is nonincreasing: its
real part is an antitone function of time. -/
theorem timeAxis_re_antitone (hF : IsSemigroupGroupPD F) (hbdd : ∀ t : ℝ≥0, ‖F (t, 0)‖ ≤ C) :
    Antitone fun t : ℝ≥0 => (F (t, (0 : V))).re := by
  intro t u hle
  obtain ⟨h, rfl⟩ : ∃ h : ℝ≥0, u = t + h := ⟨u - t, (add_tsub_cancel_of_le hle).symm⟩
  have hre := (Complex.nonneg_iff.mp (hF.timeAxis_sub_nonneg hbdd h t)).1
  simp only [Complex.sub_re] at hre
  linarith

end IsSemigroupGroupPD

end TauCeti
