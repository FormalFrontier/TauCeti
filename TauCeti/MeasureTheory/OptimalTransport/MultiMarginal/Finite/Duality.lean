/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.MultiMarginal.Finite.Basic

/-!
# Finite multi-marginal duality and complementary slackness

For finitely many finite spaces, the multi-marginal dual problem has one real-valued potential
per marginal, constrained so that their pointwise sum never exceeds the cost.

The basic identity in this file is the multi-marginal analogue of the transportation-matrix gap
formula: the difference between the cost of a plan and the value of a family of potentials is the
expectation of the pointwise dual gap. It gives weak duality and complementary slackness without
topology or linear-programming infrastructure. In particular, a feasible plan and feasible
potentials are simultaneously optimal as soon as every configuration carrying mass saturates the
dual constraint.

The finite coupling model and its bridge to the measure-theoretic `TauCeti.MultiCoupling` API live
in `TauCeti.MeasureTheory.OptimalTransport.MultiMarginal.Finite.Basic`.

This is the algebraic and certificate slice of Layer 2, item 6 of the optimal-transport roadmap.
Strong duality and dual attainment are the remaining finite linear-programming step.

## References

* C. Villani, *Optimal Transport: Old and New*, Springer, 2009, Chapter 1, for the
  multi-marginal Kantorovich problem and its marginal-potential dual.
* `TauCeti.MeasureTheory.OptimalTransport.Finite.Duality`, for the two-marginal gap and
  complementary-slackness organization generalized here to a finite family.
-/

public section

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace TauCeti

universe u v

variable {ι : Type u} {X : ι → Type v} {μ : ∀ i, PMF (X i)}

section DualValue

variable [Fintype ι] [∀ i, Fintype (X i)]

/-- The value of a finite family of multi-marginal potentials: the sum of their expectations
against the prescribed marginals. -/
def finiteMultiDualValue (μ : ∀ i, PMF (X i)) (φ : ∀ i, X i → ℝ) : ℝ :=
  ∑ i, ∑ x, ((μ i) x).toReal * φ i x

/-- The defining finite-sum formula for the value of multi-marginal potentials. -/
theorem finiteMultiDualValue_def (μ : ∀ i, PMF (X i)) (φ : ∀ i, X i → ℝ) :
    finiteMultiDualValue μ φ = ∑ i, ∑ x, ((μ i) x).toReal * φ i x := (rfl)

/-- Adding a coordinatewise constant to the potentials adds the sum of those constants to the
dual value. -/
theorem finiteMultiDualValue_add_const (μ : ∀ i, PMF (X i)) (φ : ∀ i, X i → ℝ)
    (a : ι → ℝ) :
    finiteMultiDualValue μ (fun i x ↦ φ i x + a i) =
      finiteMultiDualValue μ φ + ∑ i, a i := by
  simp only [finiteMultiDualValue_def, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul,
    PMF.sum_toReal_eq_one, one_mul, Finset.sum_add_distrib]

/-- The finite multi-marginal dual value is monotone in every potential. -/
theorem finiteMultiDualValue_mono {φ ψ : ∀ i, X i → ℝ} (h : ∀ i x, φ i x ≤ ψ i x) :
    finiteMultiDualValue μ φ ≤ finiteMultiDualValue μ ψ := by
  refine Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun x _ ↦ ?_
  exact mul_le_mul_of_nonneg_left (h i x) ENNReal.toReal_nonneg

end DualValue

section DualFeasible

variable [Fintype ι]

/-- A family of potentials is feasible for the finite multi-marginal dual problem when their
pointwise sum never exceeds the cost. -/
def FiniteMultiDualFeasible (c : (∀ i, X i) → ℝ) (φ : ∀ i, X i → ℝ) : Prop :=
  ∀ x, ∑ i, φ i (x i) ≤ c x

/-- The pointwise inequality defining finite multi-marginal dual feasibility. -/
@[simp]
theorem finiteMultiDualFeasible_iff {c : (∀ i, X i) → ℝ} {φ : ∀ i, X i → ℝ} :
    FiniteMultiDualFeasible c φ ↔ ∀ x, ∑ i, φ i (x i) ≤ c x := Iff.rfl

namespace FiniteMultiDualFeasible

/-- Apply a feasible family of potentials to one configuration. -/
theorem sum_le {c : (∀ i, X i) → ℝ} {φ : ∀ i, X i → ℝ}
    (h : FiniteMultiDualFeasible c φ) (x : ∀ i, X i) : ∑ i, φ i (x i) ≤ c x :=
  h x

/-- Lowering every potential preserves dual feasibility. -/
theorem mono {c : (∀ i, X i) → ℝ} {φ ψ : ∀ i, X i → ℝ}
    (h : FiniteMultiDualFeasible c φ) (hψ : ∀ i x, ψ i x ≤ φ i x) :
    FiniteMultiDualFeasible c ψ := by
  intro x
  exact (Finset.sum_le_sum fun i _ ↦ hψ i (x i)).trans (h x)

/-- Shifting each potential by a constant whose total is zero preserves dual feasibility. -/
theorem add_const {c : (∀ i, X i) → ℝ} {φ : ∀ i, X i → ℝ}
    (h : FiniteMultiDualFeasible c φ) (a : ι → ℝ) (ha : ∑ i, a i = 0) :
    FiniteMultiDualFeasible c (fun i x ↦ φ i x + a i) := by
  intro x
  rw [Finset.sum_add_distrib, ha, add_zero]
  exact h x

end FiniteMultiDualFeasible

end DualFeasible

section Finite

variable [Fintype ι] [∀ i, Fintype (X i)]
attribute [local instance] Classical.decEq

/-- Integrating the sum of the coordinate potentials against a coupling gives their dual value.
This is the finite change-of-variables identity behind multi-marginal weak duality. -/
theorem FiniteMultiCoupling.sum_mul_mass_eq_finiteMultiDualValue
    (π : FiniteMultiCoupling μ) (φ : ∀ i, X i → ℝ) :
    ∑ x, (∑ i, φ i (x i)) * (π.1 x).toReal = finiteMultiDualValue μ φ := by
  rw [finiteMultiDualValue_def]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [← π.map_eval i]
  let _ : MeasurableSpace (∀ i, X i) := ⊤
  let _ : MeasurableSpace (X i) := ⊤
  have hmap := MeasureTheory.integral_map (μ := π.1.toMeasure) (φ := Function.eval i)
    (measurable_of_finite (Function.eval i)).aemeasurable
    (measurable_of_finite (φ i)).aestronglyMeasurable
  rw [PMF.toMeasure_map (Function.eval i) π.1
    (measurable_of_finite (Function.eval i))] at hmap
  simpa only [PMF.integral_eq_sum, smul_eq_mul, mul_comm] using hmap.symm

/-- The cost of a plan minus the value of a family of potentials is the mass-weighted sum of
the pointwise dual gaps. -/
theorem FiniteMultiCoupling.cost_sub_finiteMultiDualValue (π : FiniteMultiCoupling μ)
    (c : (∀ i, X i) → ℝ) (φ : ∀ i, X i → ℝ) :
    π.cost c - finiteMultiDualValue μ φ =
      ∑ x, (c x - ∑ i, φ i (x i)) * (π.1 x).toReal := by
  rw [FiniteMultiCoupling.cost_def, ← π.sum_mul_mass_eq_finiteMultiDualValue φ]
  simp only [sub_mul, Finset.sum_sub_distrib]

/-- **Finite multi-marginal weak duality.** Every feasible family of potentials has value at
most the cost of every feasible plan. -/
theorem FiniteMultiCoupling.finiteMultiDualValue_le_cost (π : FiniteMultiCoupling μ)
    {c : (∀ i, X i) → ℝ} {φ : ∀ i, X i → ℝ} (hφ : FiniteMultiDualFeasible c φ) :
    finiteMultiDualValue μ φ ≤ π.cost c := by
  rw [← sub_nonneg]
  rw [π.cost_sub_finiteMultiDualValue]
  exact Finset.sum_nonneg fun x _ ↦
    mul_nonneg (sub_nonneg.2 (hφ x)) ENNReal.toReal_nonneg

/-- **Finite multi-marginal complementary slackness.** A feasible plan and feasible family of
potentials have the same value exactly when every configuration carrying mass saturates the
dual constraint. -/
theorem FiniteMultiCoupling.cost_eq_finiteMultiDualValue_iff (π : FiniteMultiCoupling μ)
    {c : (∀ i, X i) → ℝ} {φ : ∀ i, X i → ℝ} (hφ : FiniteMultiDualFeasible c φ) :
    π.cost c = finiteMultiDualValue μ φ ↔
      ∀ x, π.1 x ≠ 0 → ∑ i, φ i (x i) = c x := by
  rw [← sub_eq_zero, π.cost_sub_finiteMultiDualValue,
    Finset.sum_eq_zero_iff_of_nonneg fun x _ ↦
      mul_nonneg (sub_nonneg.2 (hφ x)) ENNReal.toReal_nonneg]
  constructor
  · intro h x hx
    rcases mul_eq_zero.1 (h x (Finset.mem_univ x)) with hgap | hmass
    · linarith
    · rcases (ENNReal.toReal_eq_zero_iff (π.1 x)).1 hmass with hzero | htop
      · exact (hx hzero).elim
      · exact (π.1.apply_ne_top x htop).elim
  · intro h x _
    by_cases hx : π.1 x = 0
    · simp [hx]
    · rw [h x hx, sub_self, zero_mul]

/-- A complementary-slackness pair is simultaneously primal- and dual-optimal among all finite
multi-marginal plans and all feasible families of potentials. -/
theorem FiniteMultiCoupling.forall_cost_le_and_forall_finiteMultiDualValue_le_of_eq
    (π : FiniteMultiCoupling μ) {c : (∀ i, X i) → ℝ} {φ : ∀ i, X i → ℝ}
    (hφ : FiniteMultiDualFeasible c φ) (heq : π.cost c = finiteMultiDualValue μ φ) :
    (∀ σ : FiniteMultiCoupling μ, π.cost c ≤ σ.cost c) ∧
      ∀ ψ, FiniteMultiDualFeasible c ψ → finiteMultiDualValue μ ψ ≤ finiteMultiDualValue μ φ := by
  constructor
  · intro σ
    rw [heq]
    exact σ.finiteMultiDualValue_le_cost hφ
  · intro ψ hψ
    rw [← heq]
    exact π.finiteMultiDualValue_le_cost hψ

end Finite

end TauCeti
