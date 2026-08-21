/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Analysis.PositiveDefinite.Kernel.Kolmogorov
public import TauCeti.Analysis.PositiveDefinite.SemigroupGroup.Basic

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

## Main declaration

* `TauCeti.IsSemigroupGroupPD.timeDifference`: a bounded BCR-positive-definite function remains
  positive definite after subtracting a nonnegative forward time translate.
* `TauCeti.IsSemigroupGroupPD.iteratedTimeDifference`: every iterated alternating time difference
  of a bounded BCR-positive-definite function is positive definite.

## References

* C. Berg, J. P. R. Christensen, P. Ressel, *Harmonic Analysis on Semigroups* (GTM 100, 1984),
  Theorem 4.1.13 and its bounded-semigroup argument.

* Roadmap: `TauCetiRoadmap/OneParameterSemigroups/README.md`, Part C, Milestone 2
  ("BCR semigroup--Bochner").
-/

public section

open ComplexConjugate InnerProductSpace Set
open scoped ComplexOrder NNReal

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

variable {V : Type u} [AddCommGroup V] {F : ℝ≥0 × V → ℂ}

/-- The first alternating time difference with step `h`:
`timeDifference h F (t, v) = F (t, v) - F (t + h, v)`. -/
def timeDifference (h : ℝ≥0) (F : ℝ≥0 × V → ℂ) : ℝ≥0 × V → ℂ :=
  fun p => F p - F (p.1 + h, p.2)

omit [AddCommGroup V] in
/-- The first time difference evaluated at a point. -/
@[simp]
theorem timeDifference_apply (h : ℝ≥0) (F : ℝ≥0 × V → ℂ) (p : ℝ≥0 × V) :
    timeDifference h F p = F p - F (p.1 + h, p.2) := by
  rw [timeDifference]

/-- The `n`-th alternating time difference, obtained by iterating `timeDifference h`. -/
def iteratedTimeDifference (n : ℕ) (h : ℝ≥0) (F : ℝ≥0 × V → ℂ) : ℝ≥0 × V → ℂ :=
  (timeDifference h)^[n] F

omit [AddCommGroup V] in
/-- The zeroth time difference is the original function. -/
@[simp]
theorem iteratedTimeDifference_zero (h : ℝ≥0) (F : ℝ≥0 × V → ℂ) :
    iteratedTimeDifference 0 h F = F := by
  simp [iteratedTimeDifference]

omit [AddCommGroup V] in
/-- The successor time difference is one further first difference. -/
@[simp]
theorem iteratedTimeDifference_succ (n : ℕ) (h : ℝ≥0) (F : ℝ≥0 × V → ℂ) :
    iteratedTimeDifference (n + 1) h F = timeDifference h (iteratedTimeDifference n h F) := by
  simp only [iteratedTimeDifference, Function.iterate_succ_apply']

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
    rw [show p.1 + q.1 + h = (p.1 + h) + q.1 by ac_rfl]
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
    rw [show (p i).1 + a + ((p j).1 + b) =
      (p i).1 + (p j).1 + (a + b) by ac_rfl]
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

omit [AddCommGroup V] in
/-- Boundedness is preserved by taking a first time difference. -/
theorem isBounded_range_timeDifference (hbounded : Bornology.IsBounded (range F)) (h : ℝ≥0) :
    Bornology.IsBounded (range (TauCeti.timeDifference h F)) := by
  rw [isBounded_iff_forall_norm_le] at hbounded ⊢
  obtain ⟨C, hC⟩ := hbounded
  refine ⟨2 * C, ?_⟩
  rintro _ ⟨p, rfl⟩
  calc
    ‖TauCeti.timeDifference h F p‖ ≤ ‖F p‖ + ‖F (p.1 + h, p.2)‖ := norm_sub_le _ _
    _ ≤ C + C := add_le_add (hC _ ⟨p, rfl⟩) (hC _ ⟨(p.1 + h, p.2), rfl⟩)
    _ = 2 * C := by ring

/-- Every iterated alternating time difference of a bounded BCR-positive-definite function is
again semigroup-group positive definite. -/
theorem iteratedTimeDifference (hF : IsSemigroupGroupPD F)
    (hbounded : Bornology.IsBounded (range F)) (n : ℕ) (h : ℝ≥0) :
    IsSemigroupGroupPD (TauCeti.iteratedTimeDifference n h F) := by
  have hpair : ∀ n : ℕ,
      IsSemigroupGroupPD (TauCeti.iteratedTimeDifference n h F) ∧
        Bornology.IsBounded (range (TauCeti.iteratedTimeDifference n h F)) := by
    intro k
    induction k with
    | zero => exact ⟨hF, hbounded⟩
    | succ k ih =>
        rw [show k + 1 = Nat.succ k by omega, Nat.succ_eq_add_one,
          TauCeti.iteratedTimeDifference_succ]
        exact ⟨ih.1.timeDifference ih.2 h, isBounded_range_timeDifference ih.2 h⟩
  exact (hpair n).1

end IsSemigroupGroupPD

end TauCeti
