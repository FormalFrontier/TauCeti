/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Semigroups.Resolvent.Identity
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# Differentiating a semigroup resolvent in the spectral parameter

The Laplace-transform resolvent `R(lambda) x = ∫₀^∞ e^{-lambda t} S(t)x dt` of a C₀-semigroup
`S` with growth bound `(omega, M)` is defined for `lambda > omega`, and it carries the proof
`omega < lambda` as an argument; `StronglyContinuousSemigroup.resolventFun` packages it as an
honest function of `lambda`, extended by the junk value `0` below the growth exponent.

The resolvent identity then upgrades to a second-order expansion

`R(mu) - R(lambda) + (mu - lambda) R(lambda)² = (mu - lambda)² R(lambda)² R(mu)`,

whose right-hand side is `O((mu - lambda)²)` because `‖R(mu)‖ ≤ M / (mu - omega)` stays bounded
near `lambda`. Hence `lambda ↦ R(lambda)` is differentiable *in operator norm* with

`R'(lambda) = -R(lambda)²`,

and inductively `dᵏR(lambda)/dlambdaᵏ = (-1)ᵏ k! R(lambda)^{k+1}`; in particular the resolvent
is smooth on `(omega, ∞)`.

## Main results

* `TauCeti.Semigroups.StronglyContinuousSemigroup.hasDerivAt_resolventFun`:
  `R'(lambda) = -R(lambda)²`.
* `TauCeti.Semigroups.StronglyContinuousSemigroup.hasDerivAt_resolventFun_pow`:
  the derivative of `lambda ↦ R(lambda)ⁿ` is `-n R(lambda)ⁿ⁺¹`.
* `TauCeti.Semigroups.StronglyContinuousSemigroup.iteratedDeriv_resolventFun`:
  `dᵏR(lambda)/dlambdaᵏ = (-1)ᵏ k! R(lambda)^{k+1}`.
* `TauCeti.Semigroups.StronglyContinuousSemigroup.contDiffOn_resolventFun`: the resolvent is
  smooth on `(omega, ∞)`.

The contraction case `(omega, M) = (0, 1)` is recorded as a corollary.

## Implementation notes

Mathlib's `spectrum.hasDerivAt_resolvent_const_left` proves the same derivative formula for the
resolvent of an element of a Banach algebra. It does not apply here: the generator of a
C₀-semigroup need not be bounded (it is a densely defined operator on a subspace, and is
bounded exactly for the uniformly continuous semigroups), so in general there is no algebra
element `a` with `R(lambda) = resolvent a lambda`. The present proof therefore runs off the
semigroup resolvent identity instead of off differentiability of `Ring.inverse`.

## References

Engel--Nagel, *One-Parameter Semigroups for Linear Evolution Equations*, Theorem II.1.10 and
Corollary IV.1.3; Pazy, *Semigroups of Linear Operators and Applications to PDE*, Chapter 1.
-/

public section

noncomputable section

open scoped ContDiff Nat NNReal Topology

namespace TauCeti.Semigroups

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

namespace StronglyContinuousSemigroup

variable (S : StronglyContinuousSemigroup X) {omega M : ℝ}

/-! ## The first derivative -/

/-- The second-order form of the resolvent identity: the remainder left by the candidate
derivative `-R(lambda)²` is exactly `(mu - lambda)² R(lambda)² R(mu)`. -/
private theorem resolventFun_second_order_eq (hb : S.HasGrowthBound omega M) {lambda mu : ℝ}
    (hl : omega < lambda) (hm : omega < mu) :
    S.resolventFun hb mu - S.resolventFun hb lambda
        + (mu - lambda) • S.resolventFun hb lambda ^ 2
      = (mu - lambda) ^ 2 • (S.resolventFun hb lambda ^ 2 * S.resolventFun hb mu) := by
  set a := S.resolventFun hb lambda
  set b := S.resolventFun hb mu
  set c := mu - lambda
  have h : a - b = c • (a * b) := S.resolventFun_sub_resolventFun hb hl hm
  have h2 : b - a + c • a ^ 2 = c • (a * (a - b)) := by
    rw [mul_sub, ← sq, smul_sub, ← h]
    abel
  rw [h2, h, mul_smul_comm, smul_smul, ← sq, ← mul_assoc, ← sq]

/-- The quantitative second-order estimate behind differentiability of the resolvent. -/
private theorem norm_resolventFun_second_order_le (hb : S.HasGrowthBound omega M) {lambda mu : ℝ}
    (hl : omega < lambda) (hm : omega < mu) :
    ‖S.resolventFun hb mu - S.resolventFun hb lambda
        + (mu - lambda) • S.resolventFun hb lambda ^ 2‖
      ≤ (mu - lambda) ^ 2 * ((M / (lambda - omega)) ^ 2 * (M / (mu - omega))) := by
  have hMpos : (0 : ℝ) < M := lt_of_lt_of_le zero_lt_one hb.one_le
  have hnorm : ‖S.resolventFun hb lambda ^ 2 * S.resolventFun hb mu‖
      ≤ (M / (lambda - omega)) ^ 2 * (M / (mu - omega)) := by
    calc ‖S.resolventFun hb lambda ^ 2 * S.resolventFun hb mu‖
        ≤ ‖S.resolventFun hb lambda ^ 2‖ * ‖S.resolventFun hb mu‖ := norm_mul_le _ _
      _ ≤ ‖S.resolventFun hb lambda‖ ^ 2 * ‖S.resolventFun hb mu‖ := by
          gcongr
          exact norm_pow_le' _ two_pos
      _ ≤ (M / (lambda - omega)) ^ 2 * (M / (mu - omega)) :=
          mul_le_mul
            (pow_le_pow_left₀ (norm_nonneg _) (S.resolventFun_norm_le hb hl) 2)
            (S.resolventFun_norm_le hb hm) (norm_nonneg _)
            (pow_nonneg (div_nonneg hMpos.le (by linarith)) 2)
  rw [S.resolventFun_second_order_eq hb hl hm, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg _)]
  exact mul_le_mul_of_nonneg_left hnorm (sq_nonneg _)

/-- **The resolvent is differentiable in the spectral parameter**, with derivative `-R(lambda)²`
taken in the operator norm. This is the semigroup analogue of Mathlib's
`spectrum.hasDerivAt_resolvent_const_left`, proved from the resolvent identity because the
generator need not be a bounded operator. -/
theorem hasDerivAt_resolventFun (hb : S.HasGrowthBound omega M) {lambda : ℝ}
    (hl : omega < lambda) :
    HasDerivAt (S.resolventFun hb) (-(S.resolventFun hb lambda ^ 2)) lambda := by
  have hMpos : (0 : ℝ) < M := lt_of_lt_of_le zero_lt_one hb.one_le
  have hd : (0 : ℝ) < lambda - omega := sub_pos.mpr hl
  set C : ℝ := (M / (lambda - omega)) ^ 2 * (M / ((lambda - omega) / 2)) with hC
  have hCpos : 0 < C := by
    have h1 : 0 < M / (lambda - omega) := div_pos hMpos hd
    exact mul_pos (pow_pos h1 2) (div_pos hMpos (by linarith))
  refine HasDerivAt.of_isLittleO (Asymptotics.isLittleO_iff.mpr ?_)
  intro c hc
  filter_upwards [Metric.ball_mem_nhds lambda
    (lt_min (half_pos hd) (div_pos hc hCpos))] with mu hmu
  rw [Metric.mem_ball, Real.dist_eq] at hmu
  have habs : |mu - lambda| < (lambda - omega) / 2 := lt_of_lt_of_le hmu (min_le_left _ _)
  have habs' : |mu - lambda| < c / C := lt_of_lt_of_le hmu (min_le_right _ _)
  have hmu_lb : (lambda - omega) / 2 < mu - omega := by
    have := neg_lt_of_abs_lt habs
    linarith
  have hm : omega < mu := by linarith
  have hstep : ‖S.resolventFun hb mu - S.resolventFun hb lambda
      - (mu - lambda) • -(S.resolventFun hb lambda ^ 2)‖
      ≤ (mu - lambda) ^ 2 * C := by
    rw [smul_neg, sub_neg_eq_add]
    refine (S.norm_resolventFun_second_order_le hb hl hm).trans ?_
    have hMdiv : M / (mu - omega) ≤ M / ((lambda - omega) / 2) := by gcongr
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hMdiv (sq_nonneg _)) (sq_nonneg _)
  refine hstep.trans ?_
  rw [Real.norm_eq_abs]
  calc (mu - lambda) ^ 2 * C = |mu - lambda| ^ 2 * C := by rw [sq_abs]
    _ = |mu - lambda| * (|mu - lambda| * C) := by ring
    _ ≤ |mu - lambda| * (c / C * C) := by gcongr
    _ = c * |mu - lambda| := by rw [div_mul_cancel₀ _ hCpos.ne']; ring

/-- The derivative of the resolvent in the spectral parameter. -/
theorem deriv_resolventFun (hb : S.HasGrowthBound omega M) {lambda : ℝ} (hl : omega < lambda) :
    deriv (S.resolventFun hb) lambda = -(S.resolventFun hb lambda ^ 2) :=
  (S.hasDerivAt_resolventFun hb hl).deriv

/-- The resolvent is differentiable on the half-line above the growth exponent. -/
theorem differentiableOn_resolventFun (hb : S.HasGrowthBound omega M) :
    DifferentiableOn ℝ (S.resolventFun hb) (Set.Ioi omega) := fun _ hl =>
  (S.hasDerivAt_resolventFun hb hl).differentiableAt.differentiableWithinAt

/-! ## Higher derivatives -/

/-- The derivative of `lambda ↦ R(lambda)ⁿ` is `-n R(lambda)ⁿ⁺¹`. -/
theorem hasDerivAt_resolventFun_pow (hb : S.HasGrowthBound omega M) {lambda : ℝ}
    (hl : omega < lambda) (n : ℕ) :
    HasDerivAt (fun l => S.resolventFun hb l ^ n)
      (-(n • S.resolventFun hb lambda ^ (n + 1))) lambda := by
  refine ((S.hasDerivAt_resolventFun hb hl).fun_pow' n).congr_deriv ?_
  cases n with
  | zero => simp
  | succ n =>
      have hterm : ∀ i ∈ Finset.range (n + 1),
          S.resolventFun hb lambda ^ ((n + 1).pred - i) * -(S.resolventFun hb lambda ^ 2)
              * S.resolventFun hb lambda ^ i
            = -(S.resolventFun hb lambda ^ (n + 1 + 1)) := by
        intro i hi
        have hexp : (n + 1).pred - i + 2 + i = n + 1 + 1 := by
          have := Finset.mem_range.mp hi
          simp only [Nat.pred_eq_sub_one]
          omega
        rw [mul_neg, neg_mul, ← pow_add, ← pow_add, hexp]
      rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, smul_neg]

/-- **The iterated derivative of the resolvent**:
`dⁿR(lambda)/dlambdaⁿ = (-1)ⁿ n! R(lambda)ⁿ⁺¹`. -/
theorem iteratedDeriv_resolventFun (hb : S.HasGrowthBound omega M) (n : ℕ) {lambda : ℝ}
    (hl : omega < lambda) :
    iteratedDeriv n (S.resolventFun hb) lambda
      = ((-1 : ℝ) ^ n * n !) • S.resolventFun hb lambda ^ (n + 1) := by
  induction n generalizing lambda with
  | zero => simp
  | succ n ih =>
      have heq : iteratedDeriv n (S.resolventFun hb)
          =ᶠ[𝓝 lambda] fun l => ((-1 : ℝ) ^ n * n !) • S.resolventFun hb l ^ (n + 1) := by
        filter_upwards [isOpen_Ioi.mem_nhds (Set.mem_Ioi.mpr hl)] with l hl' using ih hl'
      have hderiv : HasDerivAt
          (fun l => ((-1 : ℝ) ^ n * n !) • S.resolventFun hb l ^ (n + 1))
          (((-1 : ℝ) ^ n * n !) • -((n + 1) • S.resolventFun hb lambda ^ (n + 1 + 1))) lambda :=
        (S.hasDerivAt_resolventFun_pow hb hl (n + 1)).const_smul ((-1 : ℝ) ^ n * n !)
      rw [iteratedDeriv_succ, heq.deriv_eq, hderiv.deriv]
      match_scalars
      push_cast [Nat.factorial_succ]
      ring

/-- **The Hille--Yosida derivative bound**
`‖dⁿR(lambda)/dlambdaⁿ‖ ≤ n! (M / (lambda - omega))ⁿ⁺¹`, obtained by combining the iterated
derivative formula with `‖R(lambda)‖ ≤ M / (lambda - omega)`. -/
theorem norm_iteratedDeriv_resolventFun_le (hb : S.HasGrowthBound omega M) (n : ℕ) {lambda : ℝ}
    (hl : omega < lambda) :
    ‖iteratedDeriv n (S.resolventFun hb) lambda‖
      ≤ n ! * (M / (lambda - omega)) ^ (n + 1) := by
  have hscalar : ‖((-1 : ℝ) ^ n * n !)‖ = (n ! : ℝ) := by simp
  rw [S.iteratedDeriv_resolventFun hb n hl, norm_smul, hscalar]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  exact (norm_pow_le' _ n.succ_pos).trans
    (pow_le_pow_left₀ (norm_nonneg _) (S.resolventFun_norm_le hb hl) (n + 1))

/-- The resolvent is smooth on the half-line above the growth exponent. -/
theorem contDiffOn_resolventFun (hb : S.HasGrowthBound omega M) :
    ContDiffOn ℝ ∞ (S.resolventFun hb) (Set.Ioi omega) := by
  rw [contDiffOn_infty]
  intro n
  induction n with
  | zero => exact contDiffOn_zero.mpr (S.differentiableOn_resolventFun hb).continuousOn
  | succ n ih =>
      rw [Nat.cast_succ, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
      refine ⟨S.differentiableOn_resolventFun hb, by simp, ?_⟩
      exact ((ih.pow 2).neg).congr fun l hl => S.deriv_resolventFun hb hl

end StronglyContinuousSemigroup

/-! ## The contraction case -/

namespace ContractionSemigroup

variable (S : ContractionSemigroup X)

/-- The derivative of the contraction resolvent is `-R(lambda)²`. -/
theorem hasDerivAt_resolventFun {lambda : ℝ} (h : 0 < lambda) :
    HasDerivAt S.resolventFun (-(S.resolventFun lambda ^ 2)) lambda := by
  rw [S.resolventFun_eq]
  exact S.toStronglyContinuousSemigroup.hasDerivAt_resolventFun S.hasGrowthBound h

/-- The iterated derivative of the contraction resolvent. -/
theorem iteratedDeriv_resolventFun (n : ℕ) {lambda : ℝ} (h : 0 < lambda) :
    iteratedDeriv n S.resolventFun lambda
      = ((-1 : ℝ) ^ n * n !) • S.resolventFun lambda ^ (n + 1) := by
  rw [S.resolventFun_eq]
  exact S.toStronglyContinuousSemigroup.iteratedDeriv_resolventFun S.hasGrowthBound n h

/-- The Hille--Yosida derivative bound `‖dⁿR(lambda)/dlambdaⁿ‖ ≤ n! / lambdaⁿ⁺¹` in the
contraction case. -/
theorem norm_iteratedDeriv_resolventFun_le (n : ℕ) {lambda : ℝ} (h : 0 < lambda) :
    ‖iteratedDeriv n S.resolventFun lambda‖ ≤ n ! * (1 / lambda) ^ (n + 1) := by
  have := S.toStronglyContinuousSemigroup.norm_iteratedDeriv_resolventFun_le S.hasGrowthBound n h
  rw [sub_zero] at this
  rwa [S.resolventFun_eq]

/-- The contraction resolvent is smooth on `(0, ∞)`. -/
theorem contDiffOn_resolventFun : ContDiffOn ℝ ∞ S.resolventFun (Set.Ioi 0) := by
  rw [S.resolventFun_eq]
  exact S.toStronglyContinuousSemigroup.contDiffOn_resolventFun S.hasGrowthBound

end ContractionSemigroup

end TauCeti.Semigroups

end
