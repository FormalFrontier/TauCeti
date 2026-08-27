/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Distributions.Binomial
public import Mathlib.Probability.Independence.CharacteristicFunction
public import Mathlib.Probability.Moments.Basic
public import Mathlib.Probability.Moments.Variance

/-!
# Elementary theory of the binomial distribution

This file develops the moments, transforms, convolution law, and independent-sum
characterization of Mathlib's binomial measure.  The native law remains
`ProbabilityTheory.binomial n p` on `ℕ`; real-valued moments and transforms use its cast pushforward
`Bin(ℝ, n, p)`.

## Main results

* `TauCeti.Probability.variance_id_map_cast_binomial` computes the variance of the cast law;
* `TauCeti.Probability.mgf_id_map_cast_binomial` and
  `TauCeti.Probability.cgf_id_map_cast_binomial` compute its moment and cumulant generating
  functions;
* `TauCeti.Probability.charFun_map_cast_binomial` computes its characteristic function;
* `TauCeti.Probability.binomial_conv_binomial` proves additivity of the native binomial laws;
* `TauCeti.Probability.iIndepFun.hasLaw_sum_bernoulli` identifies a finite sum of independent
  Bernoulli variables with a binomial law.

## References

* N. L. Johnson, A. W. Kemp, S. Kotz, *Univariate Discrete Distributions*, 3rd ed., Wiley,
  2005, Chapter 3.
* `TauCetiRoadmap/StandardDistributions/README.md`, Layer 1, "Bernoulli and binomial".
* L. Laurance, [mathlib4 PR #40916](https://github.com/leanprover-community/mathlib4/pull/40916),
  revision `58ab4ff4561a0d87b42863a30f94761fad763dd4` (Apache-2.0), for the variance proof.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

open scoped ENNReal NNReal

namespace TauCeti

namespace Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

private theorem mgf_id_map_cast_binomial_aux (n : ℕ) (p : unitInterval) (t : ℝ) :
    mgf id Bin(ℝ, n, p) t =
      ∑ k ∈ Finset.Iic n, n.choose k * (p : ℝ) ^ k * (1 - p : ℝ) ^ (n - k) *
        Real.exp (t * k) := by
  rw [mgf, integral_map_cast_binomial]
  simp only [id_eq, smul_eq_mul]

/-- The moment generating function of the real-valued binomial law. -/
theorem mgf_id_map_cast_binomial (n : ℕ) (p : unitInterval) (t : ℝ) :
    mgf id Bin(ℝ, n, p) t = (1 - (p : ℝ) + (p : ℝ) * Real.exp t) ^ n := by
  rw [mgf_id_map_cast_binomial_aux, ← n.range_succ_eq_Iic]
  calc
    _ = ∑ k ∈ Finset.range (n + 1), n.choose k *
        ((p : ℝ) * Real.exp t) ^ k * (1 - p : ℝ) ^ (n - k) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [mul_comm t (k : ℝ), Real.exp_nat_mul, mul_pow]
      ring
    _ = ((p : ℝ) * Real.exp t + (1 - p : ℝ)) ^ n := by
      simpa only [Nat.cast_choose, nsmul_eq_mul, mul_assoc, mul_comm, mul_left_comm] using
        (add_pow ((p : ℝ) * Real.exp t) (1 - p : ℝ) n).symm
    _ = (1 - (p : ℝ) + (p : ℝ) * Real.exp t) ^ n := by ring

/-- The cumulant generating function of the real-valued binomial law. -/
theorem cgf_id_map_cast_binomial (n : ℕ) (p : unitInterval) (t : ℝ) :
    cgf id Bin(ℝ, n, p) t =
      Real.log ((1 - (p : ℝ) + (p : ℝ) * Real.exp t) ^ n) := by
  rw [cgf, mgf_id_map_cast_binomial]

/-!
### Variance

The calculation below is adapted from the proof proposed in mathlib4 PR #40916 at revision
`58ab4ff4561a0d87b42863a30f94761fad763dd4`.  That PR is the upstream API named by the roadmap;
the pinned Mathlib contains its prerequisite mean theorem but not yet its variance theorem.
-/

/-- The binomial weights of rank `m` sum to `1`; the normalization identity behind the variance
calculation below. -/
private theorem sum_binomial_weight (p : unitInterval) (m : ℕ) :
    ∑ x ∈ Finset.range (m + 1), (m.choose x : ℝ) * (p : ℝ) ^ x * (1 - p : ℝ) ^ (m - x) = 1 := by
  calc
    _ = ∑ x ∈ Finset.range (m + 1), (p : ℝ) ^ x * (1 - p : ℝ) ^ (m - x) * m.choose x :=
      Finset.sum_congr rfl fun x _ ↦ by ring
    _ = 1 := by rw [← add_pow]; simp

/-- A binomial sum of a constant `c` of rank `m` evaluates to `c`. -/
private theorem sum_binomial_weight_mul (p : unitInterval) (m : ℕ) (c : ℝ) :
    ∑ x ∈ Finset.range (m + 1), (m.choose x : ℝ) * (p : ℝ) ^ x * (1 - p : ℝ) ^ (m - x) * c = c := by
  rw [← Finset.sum_mul, sum_binomial_weight, one_mul]

/-- The variance of a real-valued binomial random variable with parameters `n` and `p` is
`p(1-p)n`. -/
theorem variance_of_hasLaw_binomial {n : ℕ} {p : unitInterval} {X : Ω → ℝ}
    (hX : HasLaw X Bin(ℝ, n, p) P) : Var[X; P] = p * (1 - p) * n := by
  have hmean := integral_of_hasLaw_binomial hX
  rw [hX.integral_eq] at hmean
  simp only [hX.variance_eq, variance_eq_integral aemeasurable_id, id_eq, hmean,
    integral_map_cast_binomial, ← n.range_succ_eq_Iic, Finset.sum_range_succ']
  match n with
  | 0 => norm_num
  | 1 =>
    simp only [Finset.range_one, Nat.cast_add, Finset.sum_singleton, Nat.choose_self,
      Nat.choose_succ_self_right]
    ring
  | n + 2 =>
    -- Expand the centered square and isolate the `x = 0` endpoint of the finite sum.
    calc
      _ = ∑ x ∈ Finset.range (n + 2), (n + 2).choose (x + 1) * p.val ^ (x + 1) *
            (1 - p) ^ (n + 1 - x) *
              ((x + 1) ^ 2 - 2 * (x + 1) * p * (n + 2) + (p * (n + 2)) ^ 2) +
          (1 - p.val) ^ (n + 2) * (p * (n + 2)) ^ 2 := by
        norm_num [sub_sq]
        grind
      _ = ∑ x ∈ Finset.range (n + 2), (n + 1 + 1).choose (x + 1) * (x + 1) * (x + 1) *
            p.val ^ (x + 1) * (1 - p) ^ (n + 1 - x) -
          ∑ x ∈ Finset.range (n + 2), (n + 1 + 1).choose (x + 1) * (x + 1) *
            p.val ^ (x + 1) * (1 - p) ^ (n + 1 - x) * 2 * p * (n + 2) +
          (∑ x ∈ Finset.range (n + 2), (n + 2).choose (x + 1) * p.val ^ (x + 1) *
            (1 - p) ^ (n + 1 - x) * (p * (n + 2)) ^ 2 +
          (1 - p.val) ^ (n + 2) * (p * (n + 2)) ^ 2) := by
        rw [← add_assoc, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        congr
        ext
        rw [mul_add, mul_sub]
        ring
      _ = ∑ x ∈ Finset.range (n + 2), (n + 1).choose x * (x + 1) * (n + 2) *
            p.val ^ (x + 1) * (1 - p) ^ (n + 1 - x) -
          ∑ x ∈ Finset.range (n + 2), (n + 1).choose x * (n + 2) * p.val ^ (x + 1) *
            (1 - p) ^ (n + 1 - x) * (2 * p * (n + 2)) +
          ∑ x ∈ Finset.range (n + 3), (n + 2).choose x * p.val ^ x *
            (1 - p) ^ (n + 2 - x) * (p * (n + 2)) ^ 2 := by
        congrm ?_ - ?_ + ?_
        any_goals
          congr
          ext
          norm_cast
          rw [← Nat.add_one_mul_choose_eq]
          group
        simp [Finset.sum_range_succ' (n := n + 2)]
      -- Shift factors of `x + 1` into the binomial coefficients.  The remaining expressions
      -- are ordinary binomial sums of ranks `n`, `n + 1`, and `n + 2`.
      _ = ∑ x ∈ Finset.range (n + 2), (n + 1).choose x * x * p.val ^ (x + 1) *
            (1 - p) ^ (n + 1 - x) * (n + 2) +
          ∑ x ∈ Finset.range (n + 2), (n + 1).choose x * p.val ^ x *
            (1 - p) ^ (n + 1 - x) * (p * (n + 2)) -
          ∑ x ∈ Finset.range (n + 2), (n + 1).choose x * p.val ^ x *
            (1 - p) ^ (n + 1 - x) * (2 * p * (n + 2) * p * (n + 2)) +
          (p * (n + 2)) ^ 2 := by
        congrm ?_ - ?_ + ?_
        · simp_rw [← Finset.sum_add_distrib, pow_add]
          group
        · simp_rw [pow_add]
          group
        · exact sum_binomial_weight_mul p (n + 2) _
      -- Evaluate the normalized sums at `p + (1 - p) = 1` by the binomial theorem.
      _ = ∑ x ∈ Finset.range (n + 1), n.choose x * p.val ^ (x + 2) *
            (1 - p) ^ (n + 1 - (x + 1)) * (n + 2) * (n + 1) +
          p * (n + 2) - 2 * p * (n + 2) * p * (n + 2) + (p * (n + 2)) ^ 2 := by
        congrm ?_ + ?_ - ?_ + _
        · norm_cast
          simp_rw [Finset.sum_range_succ', ← Nat.add_one_mul_choose_eq]
          grind
        all_goals exact sum_binomial_weight_mul p (n + 1) _
      _ = (∑ x ∈ Finset.range (n + 1), n.choose x * p.val ^ x *
            (1 - p) ^ (n + 1 - (x + 1))) * (p * p * (n + 2) * (n + 1)) +
          (1 - p * (n + 2)) * p * (n + 2) := by
        rw [Finset.sum_mul, add_sub_assoc, add_assoc]
        congr <;> grind
      _ = p.val * p * (n + 2) * (n + 1) +
          (1 - p * (n + 2)) * p * (n + 2) := by
        congrm ?_ + _
        simp only [Nat.add_sub_add_right]
        rw [sum_binomial_weight, one_mul]
      _ = _ := by grind

/-- The variance of the real-valued binomial measure itself. -/
theorem variance_id_map_cast_binomial (n : ℕ) (p : unitInterval) :
    Var[id; Bin(ℝ, n, p)] = (p : ℝ) * (1 - p) * n :=
  variance_of_hasLaw_binomial HasLaw.id

private theorem charFun_map_cast_binomial_aux (n : ℕ) (p : unitInterval) (t : ℝ) :
    charFun Bin(ℝ, n, p) t =
      ∑ k ∈ Finset.Iic n, (n.choose k : ℂ) * (p : ℂ) ^ k * (1 - p : ℂ) ^ (n - k) *
        Complex.exp (((k : ℝ) * t) * Complex.I) := by
  rw [charFun_apply, integral_map_cast_binomial]
  simp only [Real.inner_apply]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Complex.real_smul]
  push_cast
  ring

/-- The characteristic function of the real-valued binomial law. -/
theorem charFun_map_cast_binomial (n : ℕ) (p : unitInterval) (t : ℝ) :
    charFun Bin(ℝ, n, p) t =
      (1 - (p : ℂ) + (p : ℂ) * Complex.exp (Complex.I * t)) ^ n := by
  rw [charFun_map_cast_binomial_aux, ← n.range_succ_eq_Iic]
  calc
    _ = ∑ k ∈ Finset.range (n + 1), (n.choose k : ℂ) *
        ((p : ℂ) * Complex.exp (Complex.I * t)) ^ k * (1 - p : ℂ) ^ (n - k) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hexp : Complex.exp (((k : ℝ) * t) * Complex.I) =
          Complex.exp (Complex.I * t) ^ k := by
        rw [← Complex.exp_nat_mul]
        congr 1
        push_cast
        ring
      rw [hexp, mul_pow]
      ring
    _ = ((p : ℂ) * Complex.exp (Complex.I * t) + (1 - p : ℂ)) ^ n := by
      simpa only [Nat.cast_choose, nsmul_eq_mul, mul_assoc, mul_comm, mul_left_comm] using
        (add_pow ((p : ℂ) * Complex.exp (Complex.I * t)) (1 - p : ℂ) n).symm
    _ = (1 - (p : ℂ) + (p : ℂ) * Complex.exp (Complex.I * t)) ^ n := by ring

private theorem map_cast_binomial_conv_real (n m : ℕ) (p : unitInterval) :
    Bin(ℝ, n, p) ∗ Bin(ℝ, m, p) = Bin(ℝ, n + m, p) := by
  apply Measure.ext_of_charFun
  ext t
  simp only [charFun_conv, charFun_map_cast_binomial, ← pow_add]

/-- The convolution of two native binomial laws with the same success probability is binomial,
with the numbers of trials added. -/
theorem binomial_conv_binomial (n m : ℕ) (p : unitInterval) :
    Bin(n, p) ∗ Bin(m, p) = Bin(n + m, p) := by
  apply (MeasurableEmbedding.natCast (α := ℝ)).map_injective
  rw [← Nat.coe_castAddMonoidHom, Measure.map_conv_addMonoidHom _ (by fun_prop)]
  exact map_cast_binomial_conv_real n m p

/-- A finite sum of independent Bernoulli variables with common success probability `p` has the
native binomial law, with as many trials as the index type has elements. -/
theorem iIndepFun.hasLaw_sum_bernoulli {ι : Type*} [Fintype ι] {p : unitInterval} {X : ι → Ω → ℕ}
    (hindep : iIndepFun X P) (hX : ∀ i, HasLaw (X i) Ber((1 : ℕ), 0, p) P) :
    HasLaw (fun ω ↦ ∑ i, X i ω) Bin(Fintype.card ι, p) P := by
  -- `Bin(ℝ, n, p)` is *notation* for `Bin(n, p).map (Nat.cast : ℕ → ℝ)`, not a wrapper
  -- definition, so the `map_eq` field of `hnatCast` is a syntactic identity rather than an
  -- unfolding; stating it as a standalone lemma is a syntactic tautology.
  have hcast (i : ι) :
      HasLaw (fun ω ↦ (X i ω : ℝ)) Bin(ℝ, 1, p) P := by
    have hnatCast : HasLaw (Nat.cast : ℕ → ℝ) Bin(ℝ, 1, p) Bin(1, p) :=
      ⟨Measurable.of_discrete.aemeasurable, rfl⟩
    have hi := hX i
    rw [← binomial_one_eq_bernoulliMeasure] at hi
    simpa [Function.comp_def] using hnatCast.comp hi
  have hindepCast : iIndepFun (fun i ω ↦ (X i ω : ℝ)) P := by
    simpa [Function.comp_def] using
      hindep.comp (fun _ ↦ (Nat.cast : ℕ → ℝ)) (fun _ ↦ Measurable.of_discrete)
  let _ : IsProbabilityMeasure P := hindep.isProbabilityMeasure
  have hsumCast :
      P.map (fun ω ↦ ∑ i, (X i ω : ℝ)) = Bin(ℝ, Fintype.card ι, p) := by
    apply Measure.ext_of_charFun
    ext t
    calc
      charFun (P.map (fun ω ↦ ∑ i, (X i ω : ℝ))) t =
          (∏ i, charFun (P.map (fun ω ↦ (X i ω : ℝ)))) t := by
        exact congrFun (hindepCast.charFun_map_fun_sum_eq_prod fun i ↦ (hcast i).aemeasurable) t
      _ = ∏ _i : ι,
          (1 - (p : ℂ) + (p : ℂ) * Complex.exp (Complex.I * t)) := by
        rw [Fintype.prod_apply]
        apply Finset.prod_congr rfl
        intro i hi
        rw [(hcast i).map_eq, charFun_map_cast_binomial]
        simp
      _ = (1 - (p : ℂ) + (p : ℂ) * Complex.exp (Complex.I * t)) ^ Fintype.card ι := by simp
      _ = charFun Bin(ℝ, Fintype.card ι, p) t :=
        (charFun_map_cast_binomial (Fintype.card ι) p t).symm
  refine ⟨Finset.aemeasurable_fun_sum Finset.univ fun i _ ↦ (hX i).aemeasurable, ?_⟩
  apply (MeasurableEmbedding.natCast (α := ℝ)).map_injective
  rw [AEMeasurable.map_map_of_aemeasurable Measurable.of_discrete.aemeasurable
    (Finset.aemeasurable_fun_sum Finset.univ fun i _ ↦ (hX i).aemeasurable)]
  have hcomp : (Nat.cast : ℕ → ℝ) ∘ (fun ω ↦ ∑ i, X i ω) =
      fun ω ↦ ∑ i, (X i ω : ℝ) := by
    funext ω
    simp
  rw [hcomp]
  exact hsumCast

end Probability

end TauCeti
