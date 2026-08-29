/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.ProbabilityMassFunction.Integrals
public import TauCeti.MeasureTheory.OptimalTransport.MultiMarginal.Basic
public import TauCeti.Probability.ProbabilityMassFunction.Finite

/-!
# Finite multi-marginal transport and complementary slackness

For finitely many finite spaces, a multi-marginal transport plan is a probability mass function
on the dependent product whose coordinate pushforwards are prescribed.  This file packages that
finite model, its real-valued primal cost, and the dual problem with one potential per marginal.

The basic identity is the multi-marginal analogue of the transportation-matrix gap formula: the
difference between the cost of a plan and the value of a family of potentials is the expectation
of the pointwise dual gap.  It gives weak duality and complementary slackness without topology or
linear-programming infrastructure.  In particular, a feasible plan and feasible potentials are
simultaneously optimal as soon as every configuration carrying mass saturates the dual constraint.

`TauCeti.FiniteMultiCoupling.toMultiCoupling` connects the finite model to the measurable
`TauCeti.MultiCoupling` API.  Thus later finite multi-marginal duality can be transferred to the
measure-theoretic definitions without maintaining a second notion of marginal.

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

/-- A finite multi-marginal coupling is a probability mass function on the dependent product
whose pushforward by each coordinate evaluation is the prescribed marginal. -/
abbrev FiniteMultiCoupling (μ : ∀ i, PMF (X i)) :=
  {π : PMF (∀ i, X i) // ∀ i, π.map (Function.eval i) = μ i}

namespace FiniteMultiCoupling

/-- Two finite multi-marginal couplings are equal when their point masses agree. -/
@[ext]
theorem ext {π σ : FiniteMultiCoupling μ} (h : ∀ x, π.1 x = σ.1 x) : π = σ := by
  apply Subtype.ext
  exact PMF.ext h

/-- Every point mass of a finite multi-marginal coupling is finite. -/
theorem apply_ne_top (π : FiniteMultiCoupling μ) (x : ∀ i, X i) : π.1 x ≠ ⊤ :=
  π.1.apply_ne_top x

/-- The marginal condition, in its canonical pushforward form. -/
@[simp]
theorem map_eval (π : FiniteMultiCoupling μ) (i : ι) : π.1.map (Function.eval i) = μ i :=
  π.2 i

/-- The measure of a finite multi-marginal coupling is a measure-theoretic multi-coupling of the
measures associated to its marginals. -/
theorem isMultiCoupling_toMeasure [∀ i, MeasurableSpace (X i)] (π : FiniteMultiCoupling μ) :
    Measure.IsMultiCoupling π.1.toMeasure (fun i ↦ (μ i).toMeasure) := by
  constructor
  intro i
  rw [PMF.toMeasure_map (Function.eval i) π.1 (measurable_pi_apply i), π.map_eval i]

/-- A finite multi-marginal coupling, regarded as the bundled measure-theoretic coupling of the
probability measures associated to its marginals. -/
def toMultiCoupling [∀ i, MeasurableSpace (X i)]
    (π : FiniteMultiCoupling μ) :
    MultiCoupling (fun i ↦ (⟨(μ i).toMeasure, inferInstance⟩ : ProbabilityMeasure (X i))) :=
  ⟨⟨π.1.toMeasure, inferInstance⟩, π.isMultiCoupling_toMeasure⟩

/-- The measure underlying the bundled coupling associated to a finite coupling is the measure
of its probability mass function. -/
@[simp]
theorem coe_toMultiCoupling [∀ i, MeasurableSpace (X i)]
    (π : FiniteMultiCoupling μ) :
    (π.toMultiCoupling : ProbabilityMeasure (∀ i, X i)).toMeasure = π.1.toMeasure := (rfl)

section Independent

variable [Fintype ι] [∀ i, Fintype (X i)] [Fintype (∀ i, X i)]

/-- The independent finite multi-marginal coupling. -/
def independent (μ : ∀ i, PMF (X i)) : FiniteMultiCoupling μ := by
  let _ : ∀ i, MeasurableSpace (X i) := fun _ ↦ ⊤
  let ν : ∀ i, ProbabilityMeasure (X i) := fun i ↦ ⟨(μ i).toMeasure, inferInstance⟩
  let π : PMF (∀ i, X i) := (ProbabilityMeasure.pi ν).toMeasure.toPMF
  refine ⟨π, fun i ↦ ?_⟩
  rw [← PMF.toMeasure_inj]
  rw [← PMF.toMeasure_map (Function.eval i) π (measurable_pi_apply i)]
  dsimp only [π]
  rw [Measure.toPMF_toMeasure]
  exact (measurePreserving_eval (fun i ↦ (ν i).toMeasure) i).map_eq

end Independent

/-- Every finite family of probability mass functions has a finite multi-marginal coupling. -/
instance instNonempty [Finite ι] [∀ i, Finite (X i)] [Finite (∀ i, X i)] :
    Nonempty (FiniteMultiCoupling μ) := by
  let _ := Fintype.ofFinite ι
  let _ : ∀ i, Fintype (X i) := fun _ ↦ Fintype.ofFinite _
  let _ := Fintype.ofFinite (∀ i, X i)
  exact ⟨independent μ⟩

section Cost

variable [Fintype (∀ i, X i)]

/-- The real cost of a finite multi-marginal coupling. -/
def cost (c : (∀ i, X i) → ℝ) (π : FiniteMultiCoupling μ) : ℝ :=
  ∑ x, c x * (π.1 x).toReal

/-- The defining finite-sum formula for the cost of a multi-marginal coupling. -/
theorem cost_def (c : (∀ i, X i) → ℝ) (π : FiniteMultiCoupling μ) :
    π.cost c = ∑ x, c x * (π.1 x).toReal := (rfl)

/-- Adding a constant to the cost adds that constant to every plan's cost. -/
@[simp]
theorem cost_add_const (c : (∀ i, X i) → ℝ) (π : FiniteMultiCoupling μ) (a : ℝ) :
    π.cost (fun x ↦ c x + a) = π.cost c + a := by
  rw [cost_def, cost_def]
  simp only [add_mul, Finset.sum_add_distrib]
  rw [← Finset.mul_sum, PMF.sum_toReal_eq_one, mul_one]

/-- The finite-sum cost is the integral of the cost against the measure associated to the
coupling. -/
theorem cost_eq_integral [∀ i, MeasurableSpace (X i)]
    [MeasurableSingletonClass (∀ i, X i)] (π : FiniteMultiCoupling μ)
    (c : (∀ i, X i) → ℝ) : π.cost c = ∫ x, c x ∂π.1.toMeasure := by
  rw [PMF.integral_eq_sum, cost_def]
  simp only [smul_eq_mul, mul_comm]

end Cost

end FiniteMultiCoupling

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

variable [Fintype ι] [∀ i, Fintype (X i)] [Fintype (∀ i, X i)]

private theorem sum_map_toReal_mul {α β : Type*} [Fintype α] [Fintype β]
    (p : PMF α) (f : α → β) (g : β → ℝ) :
    ∑ y, ((p.map f) y).toReal * g y = ∑ x, (p x).toReal * g (f x) := by
  let _ : MeasurableSpace α := ⊤
  let _ : MeasurableSpace β := ⊤
  have hmap := MeasureTheory.integral_map (μ := p.toMeasure) (φ := f)
    (measurable_of_finite f).aemeasurable (measurable_of_finite g).aestronglyMeasurable
  rw [PMF.toMeasure_map f p (measurable_of_finite f)] at hmap
  simpa only [PMF.integral_eq_sum, smul_eq_mul] using hmap

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
  simpa only [mul_comm] using (sum_map_toReal_mul π.1 (Function.eval i) (φ i)).symm

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
      · exact (π.apply_ne_top x htop).elim
  · intro h x _
    by_cases hx : π.1 x = 0
    · simp [hx]
    · rw [show c x - ∑ i, φ i (x i) = 0 by linarith [h x hx], zero_mul]

/-- A complementary-slackness pair is simultaneously primal- and dual-optimal among all finite
multi-marginal plans and all feasible families of potentials. -/
theorem FiniteMultiCoupling.isMin_and_isMax_of_eq (π : FiniteMultiCoupling μ)
    {c : (∀ i, X i) → ℝ} {φ : ∀ i, X i → ℝ} (hφ : FiniteMultiDualFeasible c φ)
    (heq : π.cost c = finiteMultiDualValue μ φ) :
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
