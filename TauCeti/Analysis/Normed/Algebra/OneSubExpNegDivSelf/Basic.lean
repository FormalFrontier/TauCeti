/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Normed.Algebra.Exponential

/-!
# The quotient `(1 - exp (-a)) / a`

This basic file packages the power series representing `(1 - exp (-a)) / a` without requiring `a`
to be invertible. In a complete normed algebra over a normed characteristic-zero field the series is
summable at every point. It is the analytic factor in the differential of a Lie-group exponential
map.

## Main results

* `oneSubExpNegDivSelf`: the series `∑ n, (n + 1)!⁻¹ • (-a)ⁿ`.
* `summable_oneSubExpNegDivSelf`: the series is summable in a complete normed algebra.
* `commute_oneSubExpNegDivSelf`: the series commutes with its argument.
* `mul_oneSubExpNegDivSelf`: multiplying the series by `a` gives `1 - exp (-a)`.
* `oneSubExpNegDivSelf_mul`: the corresponding right-multiplication identity.
* `map_oneSubExpNegDivSelf`: continuous ring homomorphisms preserve the series.

## References

* [Lie groups and the Lie algebra correspondence roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieGroups/README.md),
  Deliverable A, Layer 1, "The conjugation formulas".
* Mathlib's `spectrum.exp_mem_exp`, whose proof supplies the shifted-exponential series argument
  adapted here.
-/

public section

open NormedSpace

noncomputable section

section Topological

variable {𝕂 A : Type*} [Field 𝕂] [Ring A] [Algebra 𝕂 A] [TopologicalSpace A]
  [IsTopologicalRing A]

/-- The value of `(1 - exp (-a)) / a` with its removable singularity filled in, defined by a power
series. The series is summable everywhere in the complete normed-algebra setting below. -/
noncomputable def oneSubExpNegDivSelf (𝕂 : Type*) [Field 𝕂] {A : Type*} [Ring A]
    [Algebra 𝕂 A] [TopologicalSpace A] [IsTopologicalRing A] (a : A) : A :=
  FormalMultilinearSeries.ofScalarsSum
    (E := A) (fun n ↦ ((n + 1).factorial⁻¹ : 𝕂)) (-a)

/-- The defining series for `oneSubExpNegDivSelf`. -/
theorem oneSubExpNegDivSelf_eq_tsum (a : A) :
    oneSubExpNegDivSelf 𝕂 a = ∑' n : ℕ, (((n + 1).factorial)⁻¹ : 𝕂) • (-a) ^ n := by
  exact FormalMultilinearSeries.ofScalars_sum_eq _ _

/-- The quotient with its removable singularity filled in takes the value `1` at zero. -/
@[simp]
theorem oneSubExpNegDivSelf_zero : oneSubExpNegDivSelf 𝕂 (0 : A) = 1 := by
  simp [oneSubExpNegDivSelf]

variable [T2Space A]

/-- The filled-in quotient commutes with its argument. -/
theorem commute_oneSubExpNegDivSelf (a : A) : Commute a (oneSubExpNegDivSelf 𝕂 a) := by
  rw [oneSubExpNegDivSelf_eq_tsum]
  exact Commute.tsum_right _ fun n ↦ ((Commute.refl a).neg_right.pow_right n).smul_right _

end Topological

section Normed

variable {𝕂 A : Type*} [NontriviallyNormedField 𝕂] [CharZero 𝕂] [ContinuousSMul ℚ 𝕂]
  [NormedRing A] [NormedAlgebra 𝕂 A] [CompleteSpace A]

/-- The series defining `oneSubExpNegDivSelf` is summable in a complete normed algebra. -/
theorem summable_oneSubExpNegDivSelf (a : A) :
    Summable fun n : ℕ ↦ ((n + 1).factorial⁻¹ : 𝕂) • (-a) ^ n := by
  let c : ℕ → 𝕂 := fun n ↦ ((n + 1).factorial⁻¹ : 𝕂)
  have hc : (FormalMultilinearSeries.ofScalars A c).radius = ⊤ := by
    apply FormalMultilinearSeries.ofScalars_radius_eq_top_of_tendsto A c
    · exact Filter.Eventually.of_forall fun n ↦ inv_ne_zero (Nat.cast_ne_zero.mpr
        (Nat.factorial_ne_zero (n + 1)))
    · have hratio :
          (fun n : ℕ ↦ ‖c n.succ‖ / ‖c n‖) =
            fun n ↦ ‖(((n + 2 : ℕ) : 𝕂))⁻¹‖ := by
        funext n
        dsimp [c]
        rw [← norm_div]
        congr 1
        -- Expose the outer successor so `Nat.factorial_succ` rewrites the denominator.
        have hsucc : n.succ + 1 = (n + 1) + 1 := by omega
        rw [hsucc, Nat.factorial_succ, Nat.cast_mul]
        field_simp [Nat.factorial_ne_zero]
      rw [hratio]
      simpa [Function.comp_def] using
        (tendsto_inv_atTop_nhds_zero_nat (𝕜 := 𝕂)).norm.comp
          (Filter.tendsto_add_atTop_nat 2)
  rw [← FormalMultilinearSeries.ofScalars_apply_eq'
    (c := c) (-a)]
  exact (FormalMultilinearSeries.ofScalars A c).summable
    (hc.symm ▸ edist_lt_top (-a) 0)

/-- Multiplying the filled-in quotient on the left by its argument recovers its numerator. -/
@[simp]
theorem mul_oneSubExpNegDivSelf (a : A) :
    a * oneSubExpNegDivSelf 𝕂 a = 1 - exp (-a) := by
  have hmul :
      (∑' n : ℕ, ((n + 1).factorial⁻¹ : 𝕂) • (-a) ^ (n + 1)) =
        (-a) * oneSubExpNegDivSelf 𝕂 a := by
    simpa only [oneSubExpNegDivSelf_eq_tsum, mul_smul_comm, pow_succ'] using
      (summable_oneSubExpNegDivSelf (𝕂 := 𝕂) a).tsum_mul_left (-a)
  simp only [exp_eq_tsum 𝕂]
  rw [(expSeries_summable' (𝕂 := 𝕂) (-a)).tsum_eq_zero_add]
  simp only [Nat.factorial_zero, Nat.cast_one, inv_one, one_smul, pow_zero]
  rw [hmul]
  noncomm_ring

/-- Multiplying the filled-in quotient on the right by its argument recovers its numerator. -/
@[simp]
theorem oneSubExpNegDivSelf_mul (a : A) :
    oneSubExpNegDivSelf 𝕂 a * a = 1 - exp (-a) := by
  rw [← (commute_oneSubExpNegDivSelf a).eq, mul_oneSubExpNegDivSelf]

/-- At an invertible argument, the filled-in quotient is left division by that argument. -/
theorem oneSubExpNegDivSelf_eq_invOf_mul (a : A) [Invertible a] :
    oneSubExpNegDivSelf 𝕂 a = ⅟ a * (1 - exp (-a)) := by
  rw [← mul_oneSubExpNegDivSelf (𝕂 := 𝕂), ← mul_assoc, invOf_mul_self, one_mul]

/-- At an invertible argument, the filled-in quotient is right division by that argument. -/
theorem oneSubExpNegDivSelf_eq_mul_invOf (a : A) [Invertible a] :
    oneSubExpNegDivSelf 𝕂 a = (1 - exp (-a)) * ⅟ a := by
  rw [← oneSubExpNegDivSelf_mul (𝕂 := 𝕂), mul_assoc, mul_invOf_self, mul_one]

end Normed

section Map

variable {𝕂 A B : Type*} [NontriviallyNormedField 𝕂] [CharZero 𝕂]
  [ContinuousSMul ℚ 𝕂] [NormedRing A] [NormedAlgebra 𝕂 A] [CompleteSpace A]
  [Ring B] [Algebra 𝕂 B] [TopologicalSpace B] [IsTopologicalRing B] [T2Space B]

/-- Any continuous ring homomorphism commutes with `oneSubExpNegDivSelf`. -/
theorem map_oneSubExpNegDivSelf {F : Type*} [FunLike F A B] [RingHomClass F A B]
    (f : F) (hf : Continuous f) (a : A) :
    f (oneSubExpNegDivSelf 𝕂 a) = oneSubExpNegDivSelf 𝕂 (f a) := by
  rw [oneSubExpNegDivSelf_eq_tsum, oneSubExpNegDivSelf_eq_tsum]
  refine ((summable_oneSubExpNegDivSelf (𝕂 := 𝕂) a).hasSum.map f hf).tsum_eq.symm.trans ?_
  dsimp only [Function.comp_def]
  apply tsum_congr
  intro n
  rw [map_inv_natCast_smul f 𝕂 𝕂]
  simp

end Map
