/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.Probability.ProbabilityMassFunction.Integrals
public import Mathlib.Topology.Sion
public import TauCeti.MeasureTheory.OptimalTransport.CTransform
public import TauCeti.MeasureTheory.OptimalTransport.Duality.Basic
public import TauCeti.MeasureTheory.OptimalTransport.Finite.TransportMatrix

/-!
# Kantorovich duality on finite spaces

On finite source and target spaces the transport problem is a linear program: minimise
`∑ i, ∑ j, c (i, j) * A i j` over the transportation matrices `A` with prescribed marginals
`μ` and `ν`. Its dual maximises `∑ i, μ i * φ i + ∑ j, ν j * ψ j` over the pairs of real
potentials satisfying `φ i + ψ j ≤ c (i, j)`.

This file proves that the two problems have the same value, that both are attained, and that
a feasible pair of a plan and a potential pair is simultaneously optimal exactly when the plan
is concentrated on the contact set of the potentials.

Unlike the rest of the theory the cost here is an honest real number, negative values included,
because a linear program has no reason to be nonnegative. Consequently the primal value is
measured by `TauCeti.TransportMatrix.cost` rather than by `TauCeti.transportCost`, whose
`ℝ≥0∞`-valued `lintegral` cannot see cancellation. The two marginal integrals of the dual are
likewise packaged as `TauCeti.finiteDualValue`, which asks for no measurable structure on the
two finite spaces; `TauCeti.finiteDualValue_eq_kantorovichDualValue` and
`TauCeti.TransportMatrix.cost_eq_integral` identify both with the measure-level definitions as
soon as one is available. The feasibility constraint used here is likewise the real form of the
canonical `TauCeti.DualFeasible`, by `TauCeti.dualFeasible_ofReal_iff` whenever the cost is
nonnegative.

The hard half of the duality is the minimax theorem: the Lagrangian
`∑ q, (c q - φ q.1 - ψ q.2) * f q + (∑ i, μ i * φ i + ∑ j, ν j * ψ j)`
is affine in the plan `f`, which ranges over the compact convex standard simplex, and affine
in the potentials, which range over the whole of `(ι → ℝ) × (κ → ℝ)`. Sion's minimax theorem
exchanges the two extrema. Taking the potentials unbounded is what forces the extended-real
codomain: the inner supremum is `⊤` at a plan whose marginals are wrong.

## Main definitions

* `TauCeti.finiteDualValue` — the value of a pair of potentials against two probability mass
  functions. The primal value is `TauCeti.TransportMatrix.cost`, which belongs to the
  transportation-matrix file.

## Main statements

* `TauCeti.TransportMatrix.finiteDualValue_le_cost` — weak duality;
* `TauCeti.TransportMatrix.exists_forall_cost_le` and
  `TauCeti.exists_forall_finiteDualValue_le` — primal and dual attainment;
* `TauCeti.exists_cost_eq_finiteDualValue` — strong duality, together with both attainments;
* `TauCeti.exists_isLeast_cost_isGreatest_finiteDualValue` — the same statement read as an
  optimal value shared by the two problems;
* `TauCeti.TransportMatrix.cost_eq_finiteDualValue_iff` — complementary slackness;
* `TauCeti.TransportMatrix.forall_cost_le_and_forall_finiteDualValue_le_iff` — the optimality
  certificate: a plan and a feasible pair are optimal for their problems exactly when the plan
  lives on the contact set of the pair, and
  `TauCeti.TransportMatrix.forall_cost_le_and_forall_finiteDualValue_le_iff_mem_contactSet` —
  the same certificate read through `TauCeti.contactSet`;
* `TauCeti.finiteDualValue_eq_kantorovichDualValue`,
  `TauCeti.TransportMatrix.cost_eq_integral` and
  `TauCeti.TransportMatrix.isCoupling_toPMF_toMeasure` — the bridges to the measure-level dual
  value, primal value and couplings.

## References

* C. Villani, *Topics in Optimal Transportation*, Graduate Studies in Mathematics 58, 2003,
  §1.1.2, for the finite duality and complementary slackness.
* M. Sion, *On general minimax theorems*, Pacific J. Math. 8 (1958), 171--176.
* `Mathlib.Topology.Sion`, formalized by Antoine Chambert-Loir and Anatole Dedecker.

This is Layer 2, item 3 of the optimal-transport roadmap.
-/

public section

noncomputable section

open Set
open scoped ENNReal BigOperators

namespace TauCeti

universe u v

variable {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ] {μ : PMF ι} {ν : PMF κ}
  {c : ι × κ → ℝ} {φ : ι → ℝ} {ψ : κ → ℝ} {f : ι × κ → ℝ}

/-- The masses of a probability mass function on a finite type sum to one. -/
private theorem sum_toReal_pmf (μ : PMF ι) : ∑ i, (μ i).toReal = 1 := by
  have h : ∑ i, μ i = 1 := (tsum_fintype fun i ↦ μ i).symm.trans μ.tsum_coe
  rw [← ENNReal.toReal_sum fun i _ ↦ μ.apply_ne_top i, h, ENNReal.toReal_one]

/-- The value of a pair of Kantorovich potentials against two probability mass functions on
finite types: the sum of the two marginal expectations. -/
def finiteDualValue (μ : PMF ι) (ν : PMF κ) (φ : ι → ℝ) (ψ : κ → ℝ) : ℝ :=
  ∑ i, (μ i).toReal * φ i + ∑ j, (ν j).toReal * ψ j

/-- The defining formula for the dual value. The body of the definition is not exposed, so this
is the lemma downstream modules should rewrite with. -/
theorem finiteDualValue_def (μ : PMF ι) (ν : PMF κ) (φ : ι → ℝ) (ψ : κ → ℝ) :
    finiteDualValue μ ν φ ψ = ∑ i, (μ i).toReal * φ i + ∑ j, (ν j).toReal * ψ j := (rfl)

/-- Shifting the two potentials by two constants shifts the dual value by their sum: both
marginals have total mass one. -/
theorem finiteDualValue_add_const_add_const (μ : PMF ι) (ν : PMF κ) (φ : ι → ℝ) (ψ : κ → ℝ)
    (a b : ℝ) :
    finiteDualValue μ ν (fun i ↦ φ i + a) (fun j ↦ ψ j + b)
      = finiteDualValue μ ν φ ψ + a + b := by
  simp only [finiteDualValue_def, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul,
    sum_toReal_pmf, one_mul]
  ring

/-- Adding a constant to the first potential adds it to the dual value: the first marginal has
total mass one. -/
theorem finiteDualValue_add_const (μ : PMF ι) (ν : PMF κ) (φ : ι → ℝ) (ψ : κ → ℝ) (a : ℝ) :
    finiteDualValue μ ν (fun i ↦ φ i + a) ψ = finiteDualValue μ ν φ ψ + a := by
  simpa using finiteDualValue_add_const_add_const μ ν φ ψ a 0

/-- The dual value is unchanged by the opposite additive shifts of the two potentials, which
is the normalisation freedom of the dual problem: both marginals have total mass one. -/
theorem finiteDualValue_add_const_sub_const (μ : PMF ι) (ν : PMF κ) (φ : ι → ℝ) (ψ : κ → ℝ)
    (a : ℝ) :
    finiteDualValue μ ν (fun i ↦ φ i + a) (fun j ↦ ψ j - a) = finiteDualValue μ ν φ ψ := by
  simpa [sub_eq_add_neg] using finiteDualValue_add_const_add_const μ ν φ ψ a (-a)

/-- The dual value is monotone in both potentials. -/
theorem finiteDualValue_mono {φ φ' : ι → ℝ} {ψ ψ' : κ → ℝ} (hφ : ∀ i, φ i ≤ φ' i)
    (hψ : ∀ j, ψ j ≤ ψ' j) : finiteDualValue μ ν φ ψ ≤ finiteDualValue μ ν φ' ψ' := by
  simp only [finiteDualValue_def]
  refine add_le_add (Finset.sum_le_sum fun i _ ↦ ?_) (Finset.sum_le_sum fun j _ ↦ ?_)
  · exact mul_le_mul_of_nonneg_left (hφ i) ENNReal.toReal_nonneg
  · exact mul_le_mul_of_nonneg_left (hψ j) ENNReal.toReal_nonneg

/-! ### The standard-simplex picture

Convexity and compactness arguments are run on real-valued plans, which form a closed subset of
the standard simplex on the product. -/

/-- The real transport plans: nonnegative functions on the product with the prescribed row and
column sums. This is the standard-simplex picture of `TauCeti.TransportMatrix`. -/
private def RealPlans (μ : PMF ι) (ν : PMF κ) : Set (ι × κ → ℝ) :=
  {f | (∀ q, 0 ≤ f q) ∧ (∀ i, ∑ j, f (i, j) = (μ i).toReal) ∧
    ∀ j, ∑ i, f (i, j) = (ν j).toReal}

/-- The cost of a real transport plan. -/
private def costFun (c : ι × κ → ℝ) (f : ι × κ → ℝ) : ℝ := ∑ q, c q * f q

namespace TransportMatrix

private theorem cost_eq_costFun (c : ι × κ → ℝ) (A : TransportMatrix μ ν) :
    A.cost c = costFun c A.toRealFun := A.cost_def c

private theorem toRealFun_mem_realPlans (A : TransportMatrix μ ν) :
    A.toRealFun ∈ RealPlans μ ν :=
  ⟨A.toRealFun_nonneg, A.sum_toRealFun_row, A.sum_toRealFun_col⟩

/-- The transportation matrix attached to a nonnegative function with the prescribed row and
column sums. -/
private def ofRealFun (hf : f ∈ RealPlans μ ν) : TransportMatrix μ ν where
  matrix i j := ENNReal.ofReal (f (i, j))
  row_sum i := by
    rw [← ENNReal.ofReal_sum_of_nonneg fun j _ ↦ hf.1 (i, j), hf.2.1 i,
      ENNReal.ofReal_toReal (μ.apply_ne_top i)]
  col_sum j := by
    rw [← ENNReal.ofReal_sum_of_nonneg fun i _ ↦ hf.1 (i, j), hf.2.2 j,
      ENNReal.ofReal_toReal (ν.apply_ne_top j)]

private theorem toRealFun_ofRealFun (hf : f ∈ RealPlans μ ν) :
    (ofRealFun hf).toRealFun = f := by
  funext q
  rw [toRealFun_apply]
  exact ENNReal.toReal_ofReal (hf.1 q)

private theorem cost_ofRealFun (c : ι × κ → ℝ) (hf : f ∈ RealPlans μ ν) :
    (ofRealFun hf).cost c = costFun c f := by
  rw [cost_eq_costFun, toRealFun_ofRealFun]

end TransportMatrix

/-! ### The algebraic core

The difference between the cost of a plan and the value of a pair of potentials is the total
mass the plan puts on the pointwise gap `c (i, j) - φ i - ψ j`. -/

private theorem sum_fst_mul (φ : ι → ℝ) (f : ι × κ → ℝ) :
    ∑ q, φ q.1 * f q = ∑ i, φ i * ∑ j, f (i, j) := by
  rw [Fintype.sum_prod_type]
  simp [Finset.mul_sum]

private theorem sum_snd_mul (ψ : κ → ℝ) (f : ι × κ → ℝ) :
    ∑ q, ψ q.2 * f q = ∑ j, ψ j * ∑ i, f (i, j) := by
  rw [Fintype.sum_prod_type_right]
  simp [Finset.mul_sum]

private theorem sum_gap_mul (c : ι × κ → ℝ) (φ : ι → ℝ) (ψ : κ → ℝ) (f : ι × κ → ℝ) :
    ∑ q, (c q - φ q.1 - ψ q.2) * f q
      = costFun c f - (∑ i, φ i * ∑ j, f (i, j)) - ∑ j, ψ j * ∑ i, f (i, j) := by
  simp only [sub_mul, Finset.sum_sub_distrib, sum_fst_mul, sum_snd_mul, costFun]

namespace TransportMatrix

/-- The cost of a plan exceeds the value of a pair of potentials by the mass the plan puts on
the pointwise gap. -/
theorem cost_sub_finiteDualValue (A : TransportMatrix μ ν) (c : ι × κ → ℝ) (φ : ι → ℝ)
    (ψ : κ → ℝ) :
    A.cost c - finiteDualValue μ ν φ ψ = ∑ q, (c q - φ q.1 - ψ q.2) * A.toRealFun q := by
  rw [sum_gap_mul, ← cost_eq_costFun, finiteDualValue_def]
  simp only [A.sum_toRealFun_row, A.sum_toRealFun_col, mul_comm]
  ring

/-- **Weak duality** on finite spaces: every dual-feasible pair of potentials is worth at most
the cost of every transport plan. -/
theorem finiteDualValue_le_cost (A : TransportMatrix μ ν) (h : ∀ i j, φ i + ψ j ≤ c (i, j)) :
    finiteDualValue μ ν φ ψ ≤ A.cost c := by
  have hnn : 0 ≤ A.cost c - finiteDualValue μ ν φ ψ := by
    rw [A.cost_sub_finiteDualValue]
    refine Finset.sum_nonneg fun q _ ↦ mul_nonneg ?_ (A.toRealFun_nonneg q)
    have := h q.1 q.2
    linarith
  linarith

/-- **Complementary slackness**: a transport plan and a dual-feasible pair of potentials have
the same value exactly when the plan is concentrated on the contact set of the potentials. -/
theorem cost_eq_finiteDualValue_iff (A : TransportMatrix μ ν)
    (h : ∀ i j, φ i + ψ j ≤ c (i, j)) :
    A.cost c = finiteDualValue μ ν φ ψ ↔ ∀ i j, A i j ≠ 0 → φ i + ψ j = c (i, j) := by
  rw [← sub_eq_zero, A.cost_sub_finiteDualValue,
    Finset.sum_eq_zero_iff_of_nonneg fun q _ ↦
      mul_nonneg (by have := h q.1 q.2; linarith) (A.toRealFun_nonneg q)]
  constructor
  · intro hq i j hij
    rcases mul_eq_zero.1 (hq (i, j) (Finset.mem_univ _)) with hg | hz
    · have : (c (i, j) - φ i - ψ j) = 0 := hg
      linarith
    · rw [toRealFun_apply] at hz
      rcases ENNReal.toReal_eq_zero_iff _ |>.1 hz with h0 | htop
      · exact absurd h0 hij
      · exact absurd htop (A.apply_ne_top i j)
  · intro hq q _
    by_cases hz : A q.1 q.2 = 0
    · simp [toRealFun_apply, hz]
    · have hcontact : φ q.1 + ψ q.2 = c q := by
        simpa only [Prod.eta] using hq q.1 q.2 hz
      have hg : c q - φ q.1 - ψ q.2 = 0 := by
        linarith
      rw [hg, zero_mul]

end TransportMatrix

/-! ### Primal attainment -/

private theorem continuous_costFun (c : ι × κ → ℝ) : Continuous (costFun c) := by
  refine continuous_finsetSum _ fun q _ ↦ ?_
  exact continuous_const.mul (continuous_apply q)

private theorem realPlans_subset_stdSimplex : RealPlans μ ν ⊆ stdSimplex ℝ (ι × κ) := by
  intro f hf
  refine ⟨hf.1, ?_⟩
  rw [Fintype.sum_prod_type]
  simp only [hf.2.1]
  exact sum_toReal_pmf μ

private theorem isClosed_realPlans : IsClosed (RealPlans μ ν) := by
  have h1 : IsClosed {f : ι × κ → ℝ | ∀ q, 0 ≤ f q} := by
    simpa only [Set.ofPred_forall] using
      isClosed_iInter fun q ↦ isClosed_le continuous_const (continuous_apply q)
  have h2 : IsClosed {f : ι × κ → ℝ | ∀ i, ∑ j, f (i, j) = (μ i).toReal} := by
    simpa only [Set.ofPred_forall] using isClosed_iInter fun i ↦
      isClosed_eq (continuous_finsetSum _ fun j _ ↦ continuous_apply (i, j)) continuous_const
  have h3 : IsClosed {f : ι × κ → ℝ | ∀ j, ∑ i, f (i, j) = (ν j).toReal} := by
    simpa only [Set.ofPred_forall] using isClosed_iInter fun j ↦
      isClosed_eq (continuous_finsetSum _ fun i _ ↦ continuous_apply (i, j)) continuous_const
  exact h1.inter (h2.inter h3)

private theorem isCompact_realPlans : IsCompact (RealPlans μ ν) :=
  (isCompact_stdSimplex ℝ (ι × κ)).of_isClosed_subset isClosed_realPlans
    realPlans_subset_stdSimplex

private theorem realPlans_nonempty (μ : PMF ι) (ν : PMF κ) : (RealPlans μ ν).Nonempty :=
  ⟨(TransportMatrix.independent μ ν).toRealFun,
    TransportMatrix.toRealFun_mem_realPlans _⟩

/-- **Primal attainment**: on finite spaces the transport problem has a minimiser. -/
theorem TransportMatrix.exists_forall_cost_le (c : ι × κ → ℝ) (μ : PMF ι) (ν : PMF κ) :
    ∃ A : TransportMatrix μ ν, ∀ B : TransportMatrix μ ν, A.cost c ≤ B.cost c := by
  obtain ⟨f, hf, hmin⟩ := isCompact_realPlans.exists_isMinOn (realPlans_nonempty μ ν)
    (continuous_costFun c).continuousOn
  refine ⟨ofRealFun hf, fun B ↦ ?_⟩
  rw [cost_ofRealFun, cost_eq_costFun]
  exact isMinOn_iff.1 hmin _ B.toRealFun_mem_realPlans

/-! ### Dual attainment

The dual problem is invariant under the opposite shifts of the two potentials, so its
supremum is unchanged by restricting to potentials normalised at a base point.  Two infimal
`c`-transforms turn an arbitrary feasible pair into a normalised one with at least the same
value, and normalised pairs are confined to a box. -/

private theorem nonempty_of_pmf {α : Type*} (μ : PMF α) : Nonempty α := by
  rcases isEmpty_or_nonempty α with h | h
  · exact absurd μ.tsum_coe (by simp)
  · exact h

/-- Two infimal transforms and a shift turn a dual-feasible pair into one that is confined to a
box depending only on a bound for the cost, without decreasing the dual value. -/
private theorem exists_bounded_of_feasible [Nonempty ι] [Nonempty κ] {M : ℝ}
    (hM : ∀ q, |c q| ≤ M) (h : ∀ i j, φ i + ψ j ≤ c (i, j)) :
    ∃ φ' ψ', (∀ i j, φ' i + ψ' j ≤ c (i, j)) ∧ (∀ i, |φ' i| ≤ 2 * M) ∧
      (∀ j, |ψ' j| ≤ 3 * M) ∧ finiteDualValue μ ν φ ψ ≤ finiteDualValue μ ν φ' ψ' := by
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have hub : ∀ q, c q ≤ M := fun q ↦ (le_abs_self _).trans (hM q)
  have hlb : ∀ q, -M ≤ c q := fun q ↦ neg_le_of_abs_le (hM q)
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM (i₀, Classical.arbitrary κ))
  -- Improve the original feasible pair by applying the infimal transform in each variable.
  obtain ⟨ψ₁, hψ₁⟩ : ∃ g : κ → ℝ, ∀ j, g j = ⨅ i, (c (i, j) - φ i) := ⟨_, fun _ ↦ rfl⟩
  obtain ⟨φ₁, hφ₁⟩ : ∃ g : ι → ℝ, ∀ i, g i = ⨅ j, (c (i, j) - ψ₁ j) := ⟨_, fun _ ↦ rfl⟩
  have hψ₁le : ∀ i j, ψ₁ j ≤ c (i, j) - φ i := fun i j ↦
    (hψ₁ j).le.trans (ciInf_le (Finite.bddBelow_range fun i ↦ c (i, j) - φ i) i)
  have hφ₁le : ∀ i j, φ₁ i ≤ c (i, j) - ψ₁ j := fun i j ↦
    (hφ₁ i).le.trans (ciInf_le (Finite.bddBelow_range fun j ↦ c (i, j) - ψ₁ j) j)
  have hmonoψ : ∀ j, ψ j ≤ ψ₁ j := fun j ↦ by
    rw [hψ₁ j]; exact le_ciInf fun i ↦ by linarith [h i j]
  have hmonoφ : ∀ i, φ i ≤ φ₁ i := fun i ↦ by
    rw [hφ₁ i]; exact le_ciInf fun j ↦ by linarith [hψ₁le i j]
  -- Use the additive freedom of the dual problem to normalize the first potential at `i₀`.
  obtain ⟨φ₂, hφ₂⟩ : ∃ g : ι → ℝ, ∀ i, g i = φ₁ i + -φ₁ i₀ := ⟨_, fun _ ↦ rfl⟩
  obtain ⟨ψ₂, hψ₂⟩ : ∃ g : κ → ℝ, ∀ j, g j = ψ₁ j - -φ₁ i₀ := ⟨_, fun _ ↦ rfl⟩
  have hφ₂i₀ : φ₂ i₀ = 0 := by rw [hφ₂]; ring
  have hfeas₂ : ∀ i j, φ₂ i + ψ₂ j ≤ c (i, j) := fun i j ↦ by
    rw [hφ₂, hψ₂]; linarith [hφ₁le i j]
  have hψ₂ub : ∀ j, ψ₂ j ≤ M := fun j ↦ by
    have := hfeas₂ i₀ j
    rw [hφ₂i₀, zero_add] at this
    exact this.trans (hub (i₀, j))
  -- Transform the normalized second potential once more, preserving feasibility and value.
  obtain ⟨ψ₃, hψ₃⟩ : ∃ g : κ → ℝ, ∀ j, g j = ⨅ i, (c (i, j) - φ₂ i) := ⟨_, fun _ ↦ rfl⟩
  have hψ₃le : ∀ i j, ψ₃ j ≤ c (i, j) - φ₂ i := fun i j ↦
    (hψ₃ j).le.trans (ciInf_le (Finite.bddBelow_range fun i ↦ c (i, j) - φ₂ i) i)
  have hmonoψ₃ : ∀ j, ψ₂ j ≤ ψ₃ j := fun j ↦ by
    rw [hψ₃ j]; exact le_ciInf fun i ↦ by linarith [hfeas₂ i j]
  -- Bound the normalized first potential using points where the finite infima are attained.
  have hφ₂lb : ∀ i, -(2 * M) ≤ φ₂ i := fun i ↦ by
    obtain ⟨j₁, hj₁⟩ := exists_eq_ciInf_of_finite (f := fun j ↦ c (i, j) - ψ₁ j)
    have hval : φ₂ i = c (i, j₁) - ψ₂ j₁ := by rw [hφ₂, hφ₁, ← hj₁, hψ₂]; ring
    have := hlb (i, j₁)
    have := hψ₂ub j₁
    rw [hval]; linarith
  have hφ₂ub : ∀ i, φ₂ i ≤ 2 * M := fun i ↦ by
    obtain ⟨j₂, hj₂⟩ := exists_eq_ciInf_of_finite (f := fun j ↦ c (i₀, j) - ψ₁ j)
    have h1 := hub (i, j₂)
    have h2 := hlb (i₀, j₂)
    have h3 := hφ₁le i j₂
    rw [hφ₂, hφ₁ i₀, ← hj₂]
    linarith
  -- Package feasibility and the two uniform bounds, then compare the dual values.
  refine ⟨φ₂, ψ₃, fun i j ↦ by linarith [hψ₃le i j], fun i ↦ ?_, fun j ↦ ?_, ?_⟩
  · exact abs_le.2 ⟨hφ₂lb i, hφ₂ub i⟩
  · refine abs_le.2 ⟨?_, ?_⟩
    · obtain ⟨i₁, hi₁⟩ := exists_eq_ciInf_of_finite (f := fun i ↦ c (i, j) - φ₂ i)
      have := hlb (i₁, j)
      have := hφ₂ub i₁
      rw [hψ₃ j, ← hi₁]; linarith
    · have := hψ₃le i₀ j
      rw [hφ₂i₀, sub_zero] at this
      linarith [hub (i₀, j), this]
  · refine (finiteDualValue_mono hmonoφ hmonoψ).trans ?_
    have hshift : finiteDualValue μ ν φ₂ ψ₂ = finiteDualValue μ ν φ₁ ψ₁ := by
      have : (fun i ↦ φ₁ i + -φ₁ i₀) = φ₂ := funext fun i ↦ (hφ₂ i).symm
      have h' : (fun j ↦ ψ₁ j - -φ₁ i₀) = ψ₂ := funext fun j ↦ (hψ₂ j).symm
      rw [← this, ← h', finiteDualValue_add_const_sub_const]
    rw [← hshift]
    exact finiteDualValue_mono (fun i ↦ le_rfl) hmonoψ₃

/-- **Dual attainment**: on finite spaces the dual problem has a maximiser. -/
theorem exists_forall_finiteDualValue_le (c : ι × κ → ℝ) (μ : PMF ι) (ν : PMF κ) :
    ∃ φ ψ, (∀ i j, φ i + ψ j ≤ c (i, j)) ∧
      ∀ φ' ψ', (∀ i j, φ' i + ψ' j ≤ c (i, j)) →
        finiteDualValue μ ν φ' ψ' ≤ finiteDualValue μ ν φ ψ := by
  have := nonempty_of_pmf μ
  have := nonempty_of_pmf ν
  obtain ⟨q₀, hq₀⟩ := Finite.exists_max fun q : ι × κ ↦ |c q|
  set M : ℝ := |c q₀| with hMdef
  have hM : ∀ q, |c q| ≤ M := hq₀
  have hM0 : 0 ≤ M := abs_nonneg _
  set K : Set ((ι → ℝ) × (κ → ℝ)) :=
    {p | (∀ i j, p.1 i + p.2 j ≤ c (i, j)) ∧ (∀ i, |p.1 i| ≤ 2 * M) ∧ ∀ j, |p.2 j| ≤ 3 * M}
    with hKdef
  have hKclosed : IsClosed K := by
    have h1 : IsClosed {p : (ι → ℝ) × (κ → ℝ) | ∀ i j, p.1 i + p.2 j ≤ c (i, j)} := by
      simp only [Set.ofPred_forall]
      exact isClosed_iInter fun i ↦ isClosed_iInter fun j ↦
        isClosed_le (((continuous_apply i).comp continuous_fst).add
          ((continuous_apply j).comp continuous_snd)) continuous_const
    have h2 : IsClosed {p : (ι → ℝ) × (κ → ℝ) | ∀ i, |p.1 i| ≤ 2 * M} := by
      simp only [Set.ofPred_forall]
      exact isClosed_iInter fun i ↦
        isClosed_le (((continuous_apply i).comp continuous_fst).abs) continuous_const
    have h3 : IsClosed {p : (ι → ℝ) × (κ → ℝ) | ∀ j, |p.2 j| ≤ 3 * M} := by
      simp only [Set.ofPred_forall]
      exact isClosed_iInter fun j ↦
        isClosed_le (((continuous_apply j).comp continuous_snd).abs) continuous_const
    exact h1.inter (h2.inter h3)
  have hKsub : K ⊆ (Set.univ.pi fun _ : ι ↦ Set.Icc (-(2 * M)) (2 * M)) ×ˢ
      (Set.univ.pi fun _ : κ ↦ Set.Icc (-(3 * M)) (3 * M)) := by
    rintro p ⟨-, h2, h3⟩
    exact ⟨fun i _ ↦ abs_le.1 (h2 i), fun j _ ↦ abs_le.1 (h3 j)⟩
  have hKcompact : IsCompact K :=
    IsCompact.of_isClosed_subset
      ((isCompact_univ_pi fun _ ↦ isCompact_Icc).prod (isCompact_univ_pi fun _ ↦ isCompact_Icc))
      hKclosed hKsub
  have hKne : K.Nonempty := by
    refine ⟨(fun _ ↦ -M, fun _ ↦ -M), fun i j ↦ ?_, fun i ↦ ?_, fun j ↦ ?_⟩
    · have := neg_le_of_abs_le (hM (i, j)); linarith
    · rw [abs_neg, abs_of_nonneg hM0]; linarith
    · rw [abs_neg, abs_of_nonneg hM0]; linarith
  have hcont : Continuous fun p : (ι → ℝ) × (κ → ℝ) ↦ finiteDualValue μ ν p.1 p.2 := by
    simp only [finiteDualValue_def]
    exact (continuous_finsetSum _ fun i _ ↦
        continuous_const.mul ((continuous_apply i).comp continuous_fst)).add
      (continuous_finsetSum _ fun j _ ↦
        continuous_const.mul ((continuous_apply j).comp continuous_snd))
  obtain ⟨p, hp, hmax⟩ := hKcompact.exists_isMaxOn hKne hcont.continuousOn
  refine ⟨p.1, p.2, hp.1, fun φ' ψ' hfeas ↦ ?_⟩
  obtain ⟨φ'', ψ'', hfeas'', hb1, hb2, hle⟩ := exists_bounded_of_feasible (μ := μ) (ν := ν) hM hfeas
  exact hle.trans (isMaxOn_iff.1 hmax (φ'', ψ'') ⟨hfeas'', hb1, hb2⟩)

/-! ### Strong duality

The Lagrangian of the transport problem is affine and continuous in the plan, which ranges over
the compact convex standard simplex, and affine and continuous in the potentials, which range
over the whole of `(ι → ℝ) × (κ → ℝ)`.  Sion's minimax theorem exchanges the two extrema.  The
inner supremum is `⊤` at a plan with the wrong marginals, whence the extended-real codomain. -/

/-- The Lagrangian of the finite transport problem: the cost of the plan corrected by the two
marginal constraints, written so that the plan enters linearly through the pointwise gap. -/
private def lagrangian (c : ι × κ → ℝ) (μ : PMF ι) (ν : PMF κ) (f : ι × κ → ℝ)
    (p : (ι → ℝ) × (κ → ℝ)) : ℝ :=
  ∑ q, (c q - p.1 q.1 - p.2 q.2) * f q + finiteDualValue μ ν p.1 p.2

private theorem lagrangian_eq (c : ι × κ → ℝ) (μ : PMF ι) (ν : PMF κ) (f : ι × κ → ℝ)
    (p : (ι → ℝ) × (κ → ℝ)) :
    lagrangian c μ ν f p = costFun c f + (∑ i, p.1 i * ((μ i).toReal - ∑ j, f (i, j)))
      + ∑ j, p.2 j * ((ν j).toReal - ∑ i, f (i, j)) := by
  rw [lagrangian, sum_gap_mul, finiteDualValue_def]
  simp only [mul_sub, Finset.sum_sub_distrib, mul_comm]
  ring

private theorem lagrangian_affine_left (c : ι × κ → ℝ) (μ : PMF ι) (ν : PMF κ)
    (f f' : ι × κ → ℝ) (p : (ι → ℝ) × (κ → ℝ)) (a b : ℝ) (hab : a + b = 1) :
    lagrangian c μ ν (a • f + b • f') p
      = a * lagrangian c μ ν f p + b * lagrangian c μ ν f' p := by
  simp only [lagrangian]
  have hterm : ∀ q,
      (c q - p.1 q.1 - p.2 q.2) * ((a • f + b • f') q)
        = a * ((c q - p.1 q.1 - p.2 q.2) * f q)
          + b * ((c q - p.1 q.1 - p.2 q.2) * f' q) := by
    intro q
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [Finset.sum_congr rfl fun q _ ↦ hterm q,
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  obtain rfl : a = 1 - b := by linarith
  ring

private theorem lagrangian_affine_right (c : ι × κ → ℝ) (μ : PMF ι) (ν : PMF κ) (f : ι × κ → ℝ)
    (p p' : (ι → ℝ) × (κ → ℝ)) (a b : ℝ) (hab : a + b = 1) :
    lagrangian c μ ν f (a • p + b • p')
      = a * lagrangian c μ ν f p + b * lagrangian c μ ν f p' := by
  rw [lagrangian_eq, lagrangian_eq, lagrangian_eq]
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  have hfst : ∀ i,
      (a * p.1 i + b * p'.1 i) * ((μ i).toReal - ∑ j, f (i, j))
        = a * (p.1 i * ((μ i).toReal - ∑ j, f (i, j)))
          + b * (p'.1 i * ((μ i).toReal - ∑ j, f (i, j))) := by
    intro i
    ring
  have hsnd : ∀ j,
      (a * p.2 j + b * p'.2 j) * ((ν j).toReal - ∑ i, f (i, j))
        = a * (p.2 j * ((ν j).toReal - ∑ i, f (i, j)))
          + b * (p'.2 j * ((ν j).toReal - ∑ i, f (i, j))) := by
    intro j
    ring
  rw [Finset.sum_congr rfl fun i _ ↦ hfst i,
    Finset.sum_congr rfl fun j _ ↦ hsnd j,
    Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum, ← Finset.mul_sum]
  obtain rfl : a = 1 - b := by linarith
  ring

private theorem continuous_lagrangian_left (c : ι × κ → ℝ) (μ : PMF ι) (ν : PMF κ)
    (p : (ι → ℝ) × (κ → ℝ)) : Continuous fun f ↦ lagrangian c μ ν f p := by
  simp only [lagrangian]
  exact (continuous_finsetSum _ fun q _ ↦ continuous_const.mul (continuous_apply q)).add
    continuous_const

private theorem continuous_lagrangian_right (c : ι × κ → ℝ) (μ : PMF ι) (ν : PMF κ)
    (f : ι × κ → ℝ) : Continuous fun p : (ι → ℝ) × (κ → ℝ) ↦ lagrangian c μ ν f p := by
  simp only [lagrangian, finiteDualValue_def]
  refine (continuous_finsetSum _ fun q _ ↦ ?_).add ((continuous_finsetSum _ fun i _ ↦
    continuous_const.mul ((continuous_apply i).comp continuous_fst)).add
    (continuous_finsetSum _ fun j _ ↦
      continuous_const.mul ((continuous_apply j).comp continuous_snd)))
  exact ((continuous_const.sub ((continuous_apply q.1).comp continuous_fst)).sub
    ((continuous_apply q.2).comp continuous_snd)).mul continuous_const

private theorem quasiconvexOn_coe {E : Type*} [AddCommMonoid E] [SMul ℝ E] {s : Set E}
    {g : E → ℝ} (hg : ConvexOn ℝ s g) : QuasiconvexOn ℝ s fun x ↦ ((g x : ℝ) : EReal) := by
  intro r
  induction r with
  | bot =>
    have hs : {x ∈ s | ((g x : ℝ) : EReal) ≤ ⊥} = ∅ := by ext x; simp [le_bot_iff]
    rw [hs]; exact convex_empty
  | coe a =>
    have hs : {x ∈ s | ((g x : ℝ) : EReal) ≤ (a : EReal)} = {x ∈ s | g x ≤ a} := by
      ext x; simp
    rw [hs]; exact hg.convex_le a
  | top =>
    have hs : {x ∈ s | ((g x : ℝ) : EReal) ≤ ⊤} = s := by ext x; simp
    rw [hs]; exact hg.1

private theorem quasiconcaveOn_coe {E : Type*} [AddCommMonoid E] [SMul ℝ E] {s : Set E}
    {g : E → ℝ} (hg : ConcaveOn ℝ s g) : QuasiconcaveOn ℝ s fun x ↦ ((g x : ℝ) : EReal) := by
  intro r
  induction r with
  | bot =>
    have hs : {x ∈ s | (⊥ : EReal) ≤ ((g x : ℝ) : EReal)} = s := by ext x; simp
    rw [hs]; exact hg.1
  | coe a =>
    have hs : {x ∈ s | (a : EReal) ≤ ((g x : ℝ) : EReal)} = {x ∈ s | a ≤ g x} := by
      ext x; simp
    rw [hs]; exact hg.convex_ge a
  | top =>
    have hs : {x ∈ s | (⊤ : EReal) ≤ ((g x : ℝ) : EReal)} = ∅ := by ext x; simp [top_le_iff]
    rw [hs]; exact convex_empty

private theorem affine_convexOn_concaveOn {E : Type*} [AddCommGroup E] [Module ℝ E] {s : Set E}
    (hs : Convex ℝ s) {g : E → ℝ}
    (h : ∀ (x y : E) (a b : ℝ), a + b = 1 → g (a • x + b • y) = a * g x + b * g y) :
    ConvexOn ℝ s g ∧ ConcaveOn ℝ s g :=
  ⟨⟨hs, fun x _ y _ a b _ _ hab ↦ by rw [h x y a b hab]; simp⟩,
    ⟨hs, fun x _ y _ a b _ _ hab ↦ by rw [h x y a b hab]; simp⟩⟩

private theorem iSup_lagrangian_of_mem (c : ι × κ → ℝ) (hf : f ∈ RealPlans μ ν) :
    ⨆ p : (ι → ℝ) × (κ → ℝ), ((lagrangian c μ ν f p : ℝ) : EReal)
      = ((costFun c f : ℝ) : EReal) := by
  have hconst : ∀ p : (ι → ℝ) × (κ → ℝ), lagrangian c μ ν f p = costFun c f := fun p ↦ by
    rw [lagrangian_eq]
    simp [hf.2.1, hf.2.2]
  simp only [hconst]
  exact iSup_const

private theorem iSup_lagrangian_of_notMem (c : ι × κ → ℝ) (hf : f ∈ stdSimplex ℝ (ι × κ))
    (hnot : f ∉ RealPlans μ ν) :
    ⨆ p : (ι → ℝ) × (κ → ℝ), ((lagrangian c μ ν f p : ℝ) : EReal) = ⊤ := by
  classical
  refine (EReal.eq_top_iff_forall_lt _).2 fun y ↦ ?_
  suffices h : ∃ p : (ι → ℝ) × (κ → ℝ), y < lagrangian c μ ν f p by
    obtain ⟨p, hp⟩ := h
    exact lt_of_lt_of_le (EReal.coe_lt_coe_iff.2 hp)
      (le_iSup (fun p ↦ ((lagrangian c μ ν f p : ℝ) : EReal)) p)
  rw [RealPlans, Set.mem_ofPred_eq] at hnot
  by_cases hrow : ∀ i, ∑ j, f (i, j) = (μ i).toReal
  · obtain ⟨j₀, hj₀⟩ := not_forall.1 fun hcol ↦ hnot ⟨hf.1, hrow, hcol⟩
    have hd : (ν j₀).toReal - ∑ i, f (i, j₀) ≠ 0 := sub_ne_zero.2 (Ne.symm hj₀)
    refine ⟨(fun _ ↦ 0, fun j ↦ if j = j₀ then
      (y + 1 - costFun c f) / ((ν j₀).toReal - ∑ i, f (i, j₀)) else 0), ?_⟩
    rw [lagrangian_eq]
    have hz : ∑ i, (0 : ℝ) * ((μ i).toReal - ∑ j, f (i, j)) = 0 := by simp
    have hs : ∀ t : ℝ, ∑ j, (if j = j₀ then t else 0) * ((ν j).toReal - ∑ i, f (i, j))
        = t * ((ν j₀).toReal - ∑ i, f (i, j₀)) := fun t ↦ by
      simp [ite_mul, Finset.sum_ite_eq']
    rw [hz, hs, add_zero, div_mul_eq_mul_div, mul_div_assoc, div_self hd, mul_one]
    linarith
  · obtain ⟨i₀, hi₀⟩ := not_forall.1 hrow
    have hd : (μ i₀).toReal - ∑ j, f (i₀, j) ≠ 0 := sub_ne_zero.2 (Ne.symm hi₀)
    refine ⟨(fun i ↦ if i = i₀ then
      (y + 1 - costFun c f) / ((μ i₀).toReal - ∑ j, f (i₀, j)) else 0, fun _ ↦ 0), ?_⟩
    rw [lagrangian_eq]
    have hz : ∑ j, (0 : ℝ) * ((ν j).toReal - ∑ i, f (i, j)) = 0 := by simp
    have hs : ∀ t : ℝ, ∑ i, (if i = i₀ then t else 0) * ((μ i).toReal - ∑ j, f (i, j))
        = t * ((μ i₀).toReal - ∑ j, f (i₀, j)) := fun t ↦ by
      simp [ite_mul, Finset.sum_ite_eq']
    rw [hz, hs, add_zero, div_mul_eq_mul_div, mul_div_assoc, div_self hd, mul_one]
    linarith

private theorem iInf_lagrangian (c : ι × κ → ℝ) (μ : PMF ι) (ν : PMF κ)
    (p : (ι → ℝ) × (κ → ℝ)) (q₀ : ι × κ)
    (hq₀ : ∀ q, c q₀ - p.1 q₀.1 - p.2 q₀.2 ≤ c q - p.1 q.1 - p.2 q.2) :
    ⨅ f ∈ stdSimplex ℝ (ι × κ), ((lagrangian c μ ν f p : ℝ) : EReal)
      = ((finiteDualValue μ ν p.1 p.2 + (c q₀ - p.1 q₀.1 - p.2 q₀.2) : ℝ) : EReal) := by
  classical
  refine le_antisymm ?_ (le_iInf₂ fun f hf ↦ ?_)
  · have hmem : (fun q ↦ if q = q₀ then (1 : ℝ) else 0) ∈ stdSimplex ℝ (ι × κ) := by
      refine ⟨fun q ↦ by positivity, ?_⟩
      simp
    refine (biInf_le _ hmem).trans (le_of_eq ?_)
    rw [EReal.coe_eq_coe_iff, lagrangian, Finset.sum_eq_single q₀ (fun b _ hb ↦ by simp [hb])
      (by simp)]
    simp [add_comm]
  · rw [EReal.coe_le_coe_iff, lagrangian]
    have hcalc : c q₀ - p.1 q₀.1 - p.2 q₀.2 ≤ ∑ q, (c q - p.1 q.1 - p.2 q.2) * f q :=
      calc c q₀ - p.1 q₀.1 - p.2 q₀.2
          = ∑ q, (c q₀ - p.1 q₀.1 - p.2 q₀.2) * f q := by
            rw [← Finset.mul_sum, hf.2, mul_one]
        _ ≤ ∑ q, (c q - p.1 q.1 - p.2 q.2) * f q :=
            Finset.sum_le_sum fun q _ ↦ mul_le_mul_of_nonneg_right (hq₀ q) (hf.1 q)
    linarith

/-- **Kantorovich duality on finite spaces**: the transport problem and its dual have the same
value, and both are attained. -/
theorem exists_cost_eq_finiteDualValue (c : ι × κ → ℝ) (μ : PMF ι) (ν : PMF κ) :
    ∃ (A : TransportMatrix μ ν) (φ : ι → ℝ) (ψ : κ → ℝ),
      (∀ B : TransportMatrix μ ν, A.cost c ≤ B.cost c) ∧
      (∀ i j, φ i + ψ j ≤ c (i, j)) ∧ A.cost c = finiteDualValue μ ν φ ψ := by
  have := nonempty_of_pmf μ
  have := nonempty_of_pmf ν
  obtain ⟨A, hA⟩ := TransportMatrix.exists_forall_cost_le c μ ν
  obtain ⟨φ, ψ, hfeas, hmax⟩ := exists_forall_finiteDualValue_le c μ ν
  refine ⟨A, φ, ψ, hA, hfeas, le_antisymm ?_ (A.finiteDualValue_le_cost hfeas)⟩
  have key : (⨅ f ∈ stdSimplex ℝ (ι × κ), ⨆ p ∈ (Set.univ : Set ((ι → ℝ) × (κ → ℝ))),
        ((lagrangian c μ ν f p : ℝ) : EReal))
      = ⨆ p ∈ (Set.univ : Set ((ι → ℝ) × (κ → ℝ))), ⨅ f ∈ stdSimplex ℝ (ι × κ),
        ((lagrangian c μ ν f p : ℝ) : EReal) := by
    refine Sion.minimax'
      (ne_X := (realPlans_nonempty μ ν).mono realPlans_subset_stdSimplex)
      (cX := convex_stdSimplex ℝ (ι × κ)) (kX := isCompact_stdSimplex ℝ (ι × κ))
      (cY := convex_univ) (hfy := fun p _ ↦ ?_) (hfy' := fun p _ ↦ ?_)
      (hfx := fun f _ ↦ ?_) (hfx' := fun f _ ↦ ?_)
    · exact (continuous_coe_real_ereal.comp
        (continuous_lagrangian_left c μ ν p)).lowerSemicontinuous.lowerSemicontinuousOn _
    · exact quasiconvexOn_coe (affine_convexOn_concaveOn (convex_stdSimplex ℝ (ι × κ))
        (fun x y a b hab ↦ lagrangian_affine_left c μ ν x y p a b hab)).1
    · exact (continuous_coe_real_ereal.comp
        (continuous_lagrangian_right c μ ν f)).upperSemicontinuous.upperSemicontinuousOn _
    · exact quasiconcaveOn_coe (affine_convexOn_concaveOn convex_univ
        (fun x y a b hab ↦ lagrangian_affine_right c μ ν f x y a b hab)).2
  simp only [iSup_univ] at key
  have h1 : ((A.cost c : ℝ) : EReal) ≤ ⨅ f ∈ stdSimplex ℝ (ι × κ),
      ⨆ p : (ι → ℝ) × (κ → ℝ), ((lagrangian c μ ν f p : ℝ) : EReal) := by
    refine le_iInf₂ fun f hf ↦ ?_
    by_cases hmem : f ∈ RealPlans μ ν
    · rw [iSup_lagrangian_of_mem c hmem, EReal.coe_le_coe_iff,
        ← TransportMatrix.cost_ofRealFun c hmem]
      exact hA _
    · rw [iSup_lagrangian_of_notMem c hf hmem]
      exact le_top
  have h2 : (⨆ p : (ι → ℝ) × (κ → ℝ), ⨅ f ∈ stdSimplex ℝ (ι × κ),
      ((lagrangian c μ ν f p : ℝ) : EReal)) ≤ ((finiteDualValue μ ν φ ψ : ℝ) : EReal) := by
    refine iSup_le fun p ↦ ?_
    obtain ⟨q₀, hq₀⟩ := Finite.exists_min fun q ↦ c q - p.1 q.1 - p.2 q.2
    rw [iInf_lagrangian c μ ν p q₀ hq₀, EReal.coe_le_coe_iff]
    have hshift : ∀ i j, (p.1 i + (c q₀ - p.1 q₀.1 - p.2 q₀.2)) + p.2 j ≤ c (i, j) := by
      intro i j
      have := hq₀ (i, j)
      simp only at this
      linarith
    have := hmax (fun i ↦ p.1 i + (c q₀ - p.1 q₀.1 - p.2 q₀.2)) p.2 hshift
    rwa [finiteDualValue_add_const] at this
  rw [key] at h1
  exact EReal.coe_le_coe_iff.1 (h1.trans h2)

/-- The common optimal value of the two problems: the transport problem attains its infimum and
the dual problem attains its supremum, at the same real number. -/
theorem exists_isLeast_cost_isGreatest_finiteDualValue (c : ι × κ → ℝ) (μ : PMF ι) (ν : PMF κ) :
    ∃ V : ℝ, IsLeast {r | ∃ A : TransportMatrix μ ν, A.cost c = r} V ∧
      IsGreatest {r | ∃ φ ψ, (∀ i j, φ i + ψ j ≤ c (i, j)) ∧ finiteDualValue μ ν φ ψ = r} V := by
  obtain ⟨A, φ, ψ, hA, hfeas, heq⟩ := exists_cost_eq_finiteDualValue c μ ν
  refine ⟨A.cost c, ⟨⟨A, rfl⟩, ?_⟩, ⟨⟨φ, ψ, hfeas, heq.symm⟩, ?_⟩⟩
  · rintro r ⟨B, rfl⟩
    exact hA B
  · rintro r ⟨φ', ψ', hfeas', rfl⟩
    exact A.finiteDualValue_le_cost hfeas'

/-- **The optimality certificate.** A transport plan and a dual-feasible pair of potentials are
optimal for their respective problems exactly when the plan is concentrated on the contact set
of the pair. -/
theorem TransportMatrix.forall_cost_le_and_forall_finiteDualValue_le_iff (A : TransportMatrix μ ν)
    (hfeas : ∀ i j, φ i + ψ j ≤ c (i, j)) :
    ((∀ B : TransportMatrix μ ν, A.cost c ≤ B.cost c) ∧
        ∀ φ' ψ', (∀ i j, φ' i + ψ' j ≤ c (i, j)) →
          finiteDualValue μ ν φ' ψ' ≤ finiteDualValue μ ν φ ψ)
      ↔ ∀ i j, A i j ≠ 0 → φ i + ψ j = c (i, j) := by
  rw [← A.cost_eq_finiteDualValue_iff hfeas]
  constructor
  · rintro ⟨hmin, hmax⟩
    obtain ⟨B, φ', ψ', -, hfeas', heq⟩ := exists_cost_eq_finiteDualValue c μ ν
    have h1 := hmin B
    have h2 := hmax φ' ψ' hfeas'
    have h3 := A.finiteDualValue_le_cost hfeas
    linarith
  · intro heq
    refine ⟨fun B ↦ ?_, fun φ' ψ' hfeas' ↦ ?_⟩
    · rw [heq]
      exact B.finiteDualValue_le_cost hfeas
    · rw [← heq]
      exact A.finiteDualValue_le_cost hfeas'

/-- **The optimality certificate, through the contact set.** The pointwise equality of
`TauCeti.TransportMatrix.forall_cost_le_and_forall_finiteDualValue_le_iff` says exactly that
every pair carrying mass lies in `TauCeti.contactSet` of the coerced potentials. -/
theorem TransportMatrix.forall_cost_le_and_forall_finiteDualValue_le_iff_mem_contactSet
    (A : TransportMatrix μ ν) (hfeas : ∀ i j, φ i + ψ j ≤ c (i, j)) :
    ((∀ B : TransportMatrix μ ν, A.cost c ≤ B.cost c) ∧
        ∀ φ' ψ', (∀ i j, φ' i + ψ' j ≤ c (i, j)) →
          finiteDualValue μ ν φ' ψ' ≤ finiteDualValue μ ν φ ψ)
      ↔ ∀ i j, A i j ≠ 0 →
          (i, j) ∈ contactSet c (fun i ↦ (φ i : EReal)) (fun j ↦ (ψ j : EReal)) := by
  rw [A.forall_cost_le_and_forall_finiteDualValue_le_iff hfeas]
  refine forall_congr' fun i ↦ forall_congr' fun j ↦ imp_congr_right fun _ ↦ ?_
  rw [mk_mem_contactSet_iff, ← EReal.coe_add, EReal.coe_eq_coe_iff]

/-! ### The measure-level reading

Neither the primal nor the dual value needs a measurable structure on the two finite spaces.
When one is available, both agree with the measure-level definitions of the rest of the
theory. -/

section Measure

variable [MeasurableSpace ι] [MeasurableSingletonClass ι] [MeasurableSpace κ]
  [MeasurableSingletonClass κ]

/-- The dual value of a pair of potentials against two probability mass functions is the
Kantorovich dual value against the measures they define. -/
theorem finiteDualValue_eq_kantorovichDualValue (μ : PMF ι) (ν : PMF κ) (φ : ι → ℝ)
    (ψ : κ → ℝ) :
    finiteDualValue μ ν φ ψ = kantorovichDualValue μ.toMeasure ν.toMeasure φ ψ := by
  rw [finiteDualValue_def, kantorovichDualValue_def, PMF.integral_eq_sum, PMF.integral_eq_sum]
  simp [smul_eq_mul]

/-- The cost of a finite transportation matrix is the integral of the cost function against the
probability measure the matrix defines. -/
theorem TransportMatrix.cost_eq_integral (c : ι × κ → ℝ) (A : TransportMatrix μ ν) :
    A.cost c = ∫ q, c q ∂A.toPMF.toMeasure := by
  rw [PMF.integral_eq_sum, cost_def]
  simp [smul_eq_mul, mul_comm]

omit [MeasurableSingletonClass ι] [MeasurableSingletonClass κ] in
/-- The measure a finite transportation matrix defines is a coupling of the two marginals. -/
theorem TransportMatrix.isCoupling_toPMF_toMeasure (A : TransportMatrix μ ν) :
    IsCoupling A.toPMF.toMeasure μ.toMeasure ν.toMeasure where
  fst_eq := by
    rw [MeasureTheory.Measure.fst,
      PMF.toMeasure_map Prod.fst A.toPMF measurable_fst, A.map_fst_toPMF]
  snd_eq := by
    rw [MeasureTheory.Measure.snd,
      PMF.toMeasure_map Prod.snd A.toPMF measurable_snd, A.map_snd_toPMF]

end Measure

end TauCeti
