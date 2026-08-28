/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.ConditionalProbability
public import Mathlib.Topology.UniformSpace.HeineCantor
public import TauCeti.MeasureTheory.MeasurableSpace.Metric
public import TauCeti.MeasureTheory.OptimalTransport.CTransform.Basic
public import TauCeti.MeasureTheory.OptimalTransport.Cost.Compact
public import TauCeti.MeasureTheory.OptimalTransport.Finite.Duality

/-!
# Strong Kantorovich duality for continuous costs on compact spaces

For probability measures `μ` and `ν` on two compact pseudometric spaces whose open sets are
measurable, and a continuous nonnegative cost `c` on their product, the transport problem and its
dual have the same value:

`(transportCost (ENNReal.ofReal ∘ c) μ ν).toReal =
  sSup {kantorovichDualValue μ ν φ ψ}`,

the supremum running over the pairs of *continuous* potentials with `φ x + ψ y ≤ c (x, y)`. Weak
duality, proved for the general interface in `TauCeti.MeasureTheory.OptimalTransport.Duality.Basic`,
gives one inequality; this file supplies the other one and hence closes the gap.

The proof is the finite approximation argument. Uniform continuity of `c` turns a `δ`-net of each
factor into a pair of measurable maps `qX : X → Fin n` and `qY : Y → Fin m` moving no point by
more than `δ`; pushing the two marginals forward along them produces a finite transport problem
whose cost matrix is the cost read at the marked points. Kantorovich duality on finite spaces,
already available as `TauCeti.exists_cost_eq_finiteDualValue`, solves that problem exactly. Its
optimal transportation matrix is lifted back to a genuine coupling by gluing the conditional
measures on the fibres, which bounds the continuous primal value from above; its optimal
potentials are read back as step functions on the fibres, which bounds the continuous dual value
from below. Both estimates lose only a multiple of the modulus of continuity, so letting the net
refine closes the duality gap.

The smoothing result `TauCeti.exists_continuous_feasible_pair_dominating` replaces any feasible pair
by a *continuous* one that dominates it pointwise: applying the infimal
`c`-transform twice inherits the modulus of continuity of the cost. This is what upgrades the
step-function potentials produced by the finite problem to the continuous potentials the theorem
advertises, and it is also why the bounded-continuous and the integrable dual classes have the same
supremum. The discretisation lemma `TauCeti.exists_measurable_dist_lt` is imported from
`TauCeti.MeasureTheory.MeasurableSpace.Metric`; it applies to totally bounded pseudometric spaces,
and is used here through `isCompact_univ.totallyBounded`.

## Implementation notes

The transform is spelled here as the real infimum `⨅ x, (c (x, y) - φ x)` rather than through the
`EReal`-valued `TauCeti.cTransform`, because the relevant infima are bounded below and the whole
computation stays inside `ℝ`. The bridge lemmas `TauCeti.cTransform_coe` and
`TauCeti.cTransformSymm_coe` identify these real infima with the extended-real transforms, so the
proof reuses the order-theoretic transform API from
`TauCeti.MeasureTheory.OptimalTransport.CTransform.Basic`.

The cost is taken nonnegative because `TauCeti.transportCost` measures an `ℝ≥0∞`-valued cost. A
continuous cost on a compact space is bounded below, so this costs no generality beyond an
additive normalisation of the cost and of the potentials.

## Main statements

* `TauCeti.exists_continuous_feasible_pair_dominating` — a feasible pair is dominated by a
  continuous feasible pair;
* `TauCeti.exists_continuous_forall_add_le_transportCost_le` — the approximate duality: for every
  `ε > 0` there is a continuous feasible pair whose value is within `ε` of the primal value;
* `TauCeti.isLUB_kantorovichDualValue_continuous` — **strong Kantorovich duality**: the primal
  value is the least upper bound of the values of the continuous feasible pairs;
* `TauCeti.isLUB_kantorovichDualValue_integrable` — the same value is also the least upper bound
  over the larger integrable dual class, so the two classes agree;
* `TauCeti.toReal_transportCost_eq_sSup` and `TauCeti.transportCost_eq_ofReal_sSup` — the same
  statement read as an equality of a supremum, in `ℝ` and in `ℝ≥0∞`;
* `TauCeti.transportCost_ne_top_of_continuous` — the primal value is finite. Real-form weak
  duality is provided by `TauCeti.DualFeasible.kantorovichDualValue_le_toReal_transportCost`.

## References

* C. Villani, *Topics in Optimal Transportation*, Graduate Studies in Mathematics 58, 2003,
  Theorem 1.3 and §1.1.
* C. Villani, *Optimal Transport: Old and New*, Grundlehren 338, 2009, Theorem 5.10.

Joseph K. Miller's Apache-2.0 `Hydrodynamical/Vlasov_Meanfield_Formalization` development at commit
`31186ee11b1c478a35b1775db48384252eb06e22` and Daniel Lyng's Apache-2.0 `danlyng/Econlib`
development at commit `003655ccf010cdf44c4f67d6675167b54ce0e9df` contain related finite
approximation proofs. The proof here was written independently against Tau Ceti's existing
raw-measure, `ℝ≥0∞`-valued transport-cost and finite-duality APIs; no code was taken from either
development.

This is Layer 2, item 4 of the optimal-transport roadmap, in its compact continuous case.
-/

public section

noncomputable section

open MeasureTheory Metric Set
open scoped BigOperators ENNReal ProbabilityTheory

namespace TauCeti

universe u v

variable {X : Type u} {Y : Type v}

section Transform

variable [PseudoMetricSpace X] [PseudoMetricSpace Y] {c : X × Y → ℝ} {φ : X → ℝ}
  {ψ : Y → ℝ}

variable [CompactSpace X] [CompactSpace Y] [Nonempty X] [Nonempty Y]

/-- **Smoothing a dual pair.** On compact pseudometric spaces, a feasible pair is dominated
pointwise by *continuous* potentials
satisfying the same Kantorovich constraint. The improved pair is obtained by applying the infimal
`c`-transform twice, so it inherits the modulus of continuity of the cost. -/
theorem exists_continuous_feasible_pair_dominating (hc : Continuous c)
    (hfeas : ∀ x y, φ x + ψ y ≤ c (x, y)) :
    ∃ φ' ψ', Continuous φ' ∧ Continuous ψ' ∧ (∀ x y, φ' x + ψ' y ≤ c (x, y)) ∧
      (∀ x, φ x ≤ φ' x) ∧ ∀ y, ψ y ≤ ψ' y := by
  obtain ⟨K, hK⟩ := (isCompact_univ (X := X × Y)).exists_bound_of_continuousOn hc.continuousOn
  have hK' : ∀ z, |c z| ≤ K := fun z ↦ by simpa using hK z (Set.mem_univ z)
  have hφub : ∀ x, φ x ≤ K - ψ (Classical.arbitrary Y) := fun x ↦ by
    have hcK := (le_abs_self (c (x, Classical.arbitrary Y))).trans (hK' _)
    linarith [hfeas x (Classical.arbitrary Y)]
  set ψ' : Y → ℝ := fun y ↦ ⨅ x, (c (x, y) - φ x) with hψ'
  have hbddψ : ∀ y, BddBelow (Set.range fun x ↦ c (x, y) - φ x) := by
    refine fun y ↦ ⟨-K - (K - ψ (Classical.arbitrary Y)), ?_⟩
    rintro _ ⟨x, rfl⟩
    linarith [neg_abs_le (c (x, y)), hK' (x, y), hφub x]
  have hψ'ub : ∀ y, ψ' y ≤ K - φ (Classical.arbitrary X) := fun y ↦ by
    have hle := ciInf_le (hbddψ y)
      (f := fun x ↦ c (x, y) - φ x) (Classical.arbitrary X)
    have hcK := (le_abs_self (c (Classical.arbitrary X, y))).trans (hK' _)
    simpa only [hψ'] using hle.trans (sub_le_sub_right hcK _)
  set φ' : X → ℝ := fun x ↦ ⨅ y, (c (x, y) - ψ' y) with hφ'
  have hbddφ : ∀ x, BddBelow (Set.range fun y ↦ c (x, y) - ψ' y) := by
    refine fun x ↦ ⟨-K - (K - φ (Classical.arbitrary X)), ?_⟩
    rintro _ ⟨y, rfl⟩
    linarith [neg_abs_le (c (x, y)), hK' (x, y), hψ'ub y]
  have hψcoe : cTransform c (fun x ↦ (φ x : EReal)) = fun y ↦ (ψ' y : EReal) := by
    funext y
    simpa only [hψ'] using cTransform_coe c φ y (hbddψ y)
  have hφcoe : cTransformSymm c (fun y ↦ (ψ' y : EReal)) = fun x ↦ (φ' x : EReal) := by
    funext x
    simpa only [hφ'] using cTransformSymm_coe c ψ' x (hbddφ x)
  have hψle : ∀ y, ψ y ≤ ψ' y := fun y ↦ EReal.coe_le_coe_iff.1 <| by
    have h := (le_cTransform_iff (c := c) (φ := fun x ↦ (φ x : EReal))
      (ψ := fun y ↦ (ψ y : EReal))).2 (fun x y ↦ by
        rw [← EReal.coe_add]
        exact EReal.coe_le_coe_iff.2 (hfeas x y)) y
    rw [hψcoe] at h
    exact h
  have hφle : ∀ x, φ x ≤ φ' x := fun x ↦ EReal.coe_le_coe_iff.1 <| by
    have h := le_cTransformSymm_cTransform c (fun x ↦ (φ x : EReal)) x
    rw [hψcoe, hφcoe] at h
    exact h
  have hcu : UniformContinuous c := CompactSpace.uniformContinuous_of_continuous hc
  have hcuY : ∀ ε > 0, ∃ δ > 0, ∀ x y y', dist y y' < δ →
      dist (c (x, y)) (c (x, y')) < ε := fun ε hε ↦ by
    obtain ⟨δ, hδ, hcδ⟩ := Metric.uniformContinuous_iff.1 hcu ε hε
    exact ⟨δ, hδ, fun x y y' hyy' ↦
      hcδ (by simpa [Prod.dist_eq, max_eq_right dist_nonneg] using hyy')⟩
  refine ⟨φ', ψ', ?_, (uniformContinuous_iInf_sub hcuY hbddψ).continuous, ?_, hφle, hψle⟩
  · have hcuX : ∀ ε > 0, ∃ δ > 0, ∀ y x x', dist x x' < δ →
        dist (c (x, y)) (c (x', y)) < ε := fun ε hε ↦ by
      obtain ⟨δ, hδ, hcδ⟩ := Metric.uniformContinuous_iff.1 hcu ε hε
      refine ⟨δ, hδ, fun y x x' hxx' ↦ ?_⟩
      have hprod : dist ((x, y) : X × Y) (x', y) < δ := by
        simpa [Prod.dist_eq] using hxx'
      exact hcδ hprod
    exact (uniformContinuous_iInf_sub (c := fun q : Y × X ↦ c (q.2, q.1))
      (φ := ψ') hcuX hbddφ).continuous
  · intro x y
    have h := cTransformSymm_add_le c (fun y ↦ (ψ' y : EReal)) x y
    rw [hφcoe] at h
    rw [← EReal.coe_add] at h
    exact EReal.coe_le_coe_iff.1 h

end Transform

/-! ### Lifting a finite transport plan to a coupling -/

section Lift

variable [MeasurableSpace X] [MeasurableSpace Y]

/-- The expectation of a function of a finitely valued measurable map is the finite sum of its
values weighted by the masses of the fibres. -/
private theorem integral_comp_eq_sum (μ : Measure X) [IsProbabilityMeasure μ] {n : ℕ}
    {q : X → Fin n} (hq : Measurable q) (a : Fin n → ℝ) :
    ∫ x, a (q x) ∂μ = ∑ i, (μ (q ⁻¹' {i})).toReal * a i := by
  have : IsProbabilityMeasure (μ.map q) := Measure.isProbabilityMeasure_map hq.aemeasurable
  rw [← integral_map hq.aemeasurable (Measurable.of_discrete (f := a)).aestronglyMeasurable,
    integral_fintype Integrable.of_finite]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [measureReal_def, Measure.map_apply hq (MeasurableSet.singleton i), smul_eq_mul]

/-- A nonzero matrix entry has a nonzero source fibre. -/
private theorem row_fiber_ne_zero {n m : ℕ} {q : X → Fin n} {μ : Measure X}
    {pμ : PMF (Fin n)} {pν : PMF (Fin m)} (hpμ : ∀ i, pμ i = μ (q ⁻¹' {i}))
    (T : TransportMatrix pμ pν) {i : Fin n} {j : Fin m} (h : T i j ≠ 0) :
    μ (q ⁻¹' {i}) ≠ 0 := by
  intro hzero
  exact h <| le_antisymm ((T.apply_le_row i j).trans_eq (by rw [hpμ i, hzero])) zero_le

/-- A nonzero matrix entry has a nonzero target fibre. -/
private theorem col_fiber_ne_zero {n m : ℕ} {q : Y → Fin m} {ν : Measure Y}
    {pμ : PMF (Fin n)} {pν : PMF (Fin m)} (hpν : ∀ j, pν j = ν (q ⁻¹' {j}))
    (T : TransportMatrix pμ pν) {i : Fin n} {j : Fin m} (h : T i j ≠ 0) :
    ν (q ⁻¹' {j}) ≠ 0 := by
  intro hzero
  exact h <| le_antisymm ((T.apply_le_col i j).trans_eq (by rw [hpν j, hzero])) zero_le

/-- Gluing conditional laws along a finite transportation matrix gives a coupling of the original
marginals. -/
private theorem isCoupling_glue {n m : ℕ} {qX : X → Fin n} {qY : Y → Fin m}
    (hqX : Measurable qX) (hqY : Measurable qY) {μ : Measure X} [IsProbabilityMeasure μ]
    {ν : Measure Y} [IsProbabilityMeasure ν]
    {pμ : PMF (Fin n)} {pν : PMF (Fin m)} (hpμ : ∀ i, pμ i = μ (qX ⁻¹' {i}))
    (hpν : ∀ j, pν j = ν (qY ⁻¹' {j})) (T : TransportMatrix pμ pν) :
    IsCoupling (∑ i, ∑ j, T i j • (μ[|qX ⁻¹' {i}]).prod (ν[|qY ⁻¹' {j}])) μ ν := by
  have hmapfst : ∀ i j, Measure.map Prod.fst
      (T i j • (μ[|qX ⁻¹' {i}]).prod (ν[|qY ⁻¹' {j}])) = T i j • μ[|qX ⁻¹' {i}] := by
    intro i j
    rcases eq_or_ne (T i j) 0 with h | h
    · simp [h]
    · have := ProbabilityTheory.cond_isProbabilityMeasure (col_fiber_ne_zero hpν T h)
      rw [Measure.map_smul, Measure.map_fst_prod, measure_univ, one_smul]
  have hmapsnd : ∀ i j, Measure.map Prod.snd
      (T i j • (μ[|qX ⁻¹' {i}]).prod (ν[|qY ⁻¹' {j}])) = T i j • ν[|qY ⁻¹' {j}] := by
    intro i j
    rcases eq_or_ne (T i j) 0 with h | h
    · simp [h]
    · have := ProbabilityTheory.cond_isProbabilityMeasure (row_fiber_ne_zero hpμ T h)
      rw [Measure.map_smul, Measure.map_snd_prod, measure_univ, one_smul]
  refine { fst_eq := ?_, snd_eq := ?_ }
  · rw [Measure.fst]
    have hstep : Measure.map Prod.fst
        (∑ i, ∑ j, T i j • (μ[|qX ⁻¹' {i}]).prod (ν[|qY ⁻¹' {j}])) =
        ∑ i, μ (qX ⁻¹' {i}) • μ[|qX ⁻¹' {i}] := by
      rw [Measure.map_finset_sum' measurable_fst.aemeasurable]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [Measure.map_finset_sum' measurable_fst.aemeasurable,
        Finset.sum_congr rfl fun j _ ↦ hmapfst i j, ← Finset.sum_smul, T.row_sum i, hpμ i]
    rw [hstep]
    exact ProbabilityTheory.sum_meas_smul_cond_fiber hqX μ
  · rw [Measure.snd]
    have hstep : Measure.map Prod.snd
        (∑ i, ∑ j, T i j • (μ[|qX ⁻¹' {i}]).prod (ν[|qY ⁻¹' {j}])) =
        ∑ j, ν (qY ⁻¹' {j}) • ν[|qY ⁻¹' {j}] := by
      rw [Measure.map_finset_sum' measurable_snd.aemeasurable]
      rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) ↦
        (Measure.map_finset_sum' (m := fun j ↦ T i j • (μ[|qX ⁻¹' {i}]).prod
          (ν[|qY ⁻¹' {j}])) measurable_snd.aemeasurable).trans
            (Finset.sum_congr rfl fun j _ ↦ hmapsnd i j), Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ ↦ by rw [← Finset.sum_smul, T.col_sum j, hpν j]
    rw [hstep]
    exact ProbabilityTheory.sum_meas_smul_cond_fiber hqY ν

/-- **Lifting a finite transportation matrix to a coupling.** Let two measurable maps `qX` and
`qY` with finite ranges discretise the two marginals, and let `T` be a transportation matrix for
the discretised masses. Gluing the conditional measures on the fibres of `qX` and `qY` along `T`
produces a genuine coupling of `μ` and `ν`, so if the cost is dominated fibrewise by the entries
of `C` then the primal transport cost is at most the finite cost of `T`. -/
private theorem transportCost_le_ofReal_cost {n m : ℕ} {qX : X → Fin n} {qY : Y → Fin m}
    (hqX : Measurable qX) (hqY : Measurable qY) {μ : Measure X} [IsProbabilityMeasure μ]
    {ν : Measure Y} [IsProbabilityMeasure ν] {pμ : PMF (Fin n)} {pν : PMF (Fin m)}
    (hpμ : ∀ i, pμ i = μ (qX ⁻¹' {i})) (hpν : ∀ j, pν j = ν (qY ⁻¹' {j}))
    (T : TransportMatrix pμ pν) {c : X × Y → ℝ} {C : Fin n × Fin m → ℝ} (hC0 : ∀ p, 0 ≤ C p)
    (hC : ∀ x y, c (x, y) ≤ C (qX x, qY y)) :
    transportCost (fun z ↦ ENNReal.ofReal (c z)) μ ν ≤ ENNReal.ofReal (T.cost C) := by
  set π : Measure (X × Y) :=
    ∑ i, ∑ j, T i j • (μ[|qX ⁻¹' {i}]).prod (ν[|qY ⁻¹' {j}]) with hπ
  have hcoup : IsCoupling π μ ν := by
    rw [hπ]
    exact isCoupling_glue hqX hqY hpμ hpν T
  -- the cost of the glued measure
  have hblock : ∀ i j, T i j * ∫⁻ z, ENNReal.ofReal (c z) ∂((μ[|qX ⁻¹' {i}]).prod
      (ν[|qY ⁻¹' {j}])) ≤ T i j * ENNReal.ofReal (C (i, j)) := by
    intro i j
    rcases eq_or_ne (T i j) 0 with h | h
    · simp [h]
    · have := ProbabilityTheory.cond_isProbabilityMeasure (row_fiber_ne_zero hpμ T h)
      have := ProbabilityTheory.cond_isProbabilityMeasure (col_fiber_ne_zero hpν T h)
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      have hfib1 : ∀ᵐ z ∂((μ[|qX ⁻¹' {i}]).prod (ν[|qY ⁻¹' {j}])), qX z.1 = i := by
        refine (Measure.ae_prod_iff_ae_ae ?_).2 ?_
        · exact (hqX.comp measurable_fst) (MeasurableSet.singleton i)
        · filter_upwards [ProbabilityTheory.ae_cond_mem (μ := μ)
            (hqX (MeasurableSet.singleton i))] with x hx
          exact ae_of_all _ fun _ ↦ hx
      have hfib2 : ∀ᵐ z ∂((μ[|qX ⁻¹' {i}]).prod (ν[|qY ⁻¹' {j}])), qY z.2 = j := by
        refine (Measure.ae_prod_iff_ae_ae ?_).2 ?_
        · exact (hqY.comp measurable_snd) (MeasurableSet.singleton j)
        · exact ae_of_all _ fun _ ↦ ProbabilityTheory.ae_cond_mem (μ := ν)
            (hqY (MeasurableSet.singleton j))
      refine le_trans (lintegral_mono_ae ?_) (by rw [lintegral_const, measure_univ, mul_one])
      filter_upwards [hfib1, hfib2] with z h1 h2
      refine ENNReal.ofReal_le_ofReal ?_
      have hz := hC z.1 z.2
      rw [h1, h2] at hz
      simpa using hz
  have hentry : ∀ i j, T i j * ENNReal.ofReal (C (i, j))
      = ENNReal.ofReal (C (i, j) * T.toRealFun (i, j)) := by
    intro i j
    rw [mul_comm (C (i, j)), ENNReal.ofReal_mul (T.toRealFun_nonneg _),
      TransportMatrix.toRealFun_apply, ENNReal.ofReal_toReal (T.apply_ne_top i j)]
  refine (transportCost_le_lintegral hcoup _).trans ?_
  calc ∫⁻ z, ENNReal.ofReal (c z) ∂π
      = ∑ i, ∑ j, T i j * ∫⁻ z, ENNReal.ofReal (c z) ∂((μ[|qX ⁻¹' {i}]).prod
          (ν[|qY ⁻¹' {j}])) := by
        simp only [hπ, lintegral_finsetSum_measure, lintegral_smul_measure, smul_eq_mul]
    _ ≤ ∑ i, ∑ j, T i j * ENNReal.ofReal (C (i, j)) :=
        Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ hblock i j
    _ = ENNReal.ofReal (T.cost C) := by
        rw [TransportMatrix.cost_def, Fintype.sum_prod_type,
          ENNReal.ofReal_sum_of_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦
            mul_nonneg (hC0 _) (T.toRealFun_nonneg _)]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [ENNReal.ofReal_sum_of_nonneg fun j _ ↦ mul_nonneg (hC0 _) (T.toRealFun_nonneg _)]
        exact Finset.sum_congr rfl fun j _ ↦ hentry i j

end Lift

/-! ### Strong duality -/

section Duality

variable [PseudoMetricSpace X] [CompactSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  [PseudoMetricSpace Y] [CompactSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]
  {μ : Measure X} {ν : Measure Y} {c : X × Y → ℝ}

/-- A continuous real function on a compact space is integrable against every finite measure for
which open sets are measurable. -/
private theorem integrable_of_continuous [IsFiniteMeasure μ] {f : X → ℝ} (hf : Continuous f) :
    Integrable f μ := by
  simpa only [integrableOn_univ] using
    hf.continuousOn.integrableOn_compact' (μ := μ) isCompact_univ MeasurableSet.univ

omit [CompactSpace X] [OpensMeasurableSpace X] [CompactSpace Y] [OpensMeasurableSpace Y] in
/-- The zero pair belongs to the continuous dual class for a nonnegative cost. -/
private theorem zero_mem_continuousDualValues (hc0 : ∀ z, 0 ≤ c z) :
    (0 : ℝ) ∈ {r : ℝ | ∃ φ ψ, Continuous φ ∧ Continuous ψ ∧
      (∀ x y, φ x + ψ y ≤ c (x, y)) ∧ kantorovichDualValue μ ν φ ψ = r} :=
  ⟨fun _ ↦ 0, fun _ ↦ 0, continuous_const, continuous_const,
    fun x y ↦ by simpa using hc0 (x, y), by simp⟩

/-- **Approximate Kantorovich duality on compact spaces.** For probability measures on compact
pseudometric spaces, a continuous nonnegative cost, and every `ε > 0`, there is a pair of
*continuous* potentials satisfying the Kantorovich constraint whose value is within `ε` of the
primal transport cost. Together with weak duality this closes the duality gap. -/
theorem exists_continuous_forall_add_le_transportCost_le [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hc : Continuous c) (hc0 : ∀ z, 0 ≤ c z) {ε : ℝ} (hε : 0 < ε) :
    ∃ φ ψ, Continuous φ ∧ Continuous ψ ∧ (∀ x y, φ x + ψ y ≤ c (x, y)) ∧
      transportCost (fun z ↦ ENNReal.ofReal (c z)) μ ν
        ≤ ENNReal.ofReal (kantorovichDualValue μ ν φ ψ + ε) := by
  have hXne : Nonempty X := ⟨(μ.nonempty_of_neZero).some⟩
  have hYne : Nonempty Y := ⟨(ν.nonempty_of_neZero).some⟩
  -- discretise both factors finely enough that the cost varies by less than `ε / 2`
  have hcu : UniformContinuous c := CompactSpace.uniformContinuous_of_continuous hc
  obtain ⟨δ, hδ, hcδ⟩ := Metric.uniformContinuous_iff.1 hcu (ε / 2) (by positivity)
  obtain ⟨n, v, qX, hqX, hvX⟩ :=
    exists_measurable_dist_lt X isCompact_univ.totallyBounded hδ
  obtain ⟨m, w, qY, hqY, hwY⟩ :=
    exists_measurable_dist_lt Y isCompact_univ.totallyBounded hδ
  have hosc : ∀ x y, |c (x, y) - c (v (qX x), w (qY y))| < ε / 2 := fun x y ↦ by
    have hd : dist ((x, y) : X × Y) (v (qX x), w (qY y)) < δ := by
      rw [Prod.dist_eq]
      exact max_lt (hvX x) (hwY y)
    simpa [Real.dist_eq] using hcδ hd
  -- the two discretised marginals
  have hsumX : ∑ i, μ (qX ⁻¹' {i}) = 1 := by
    rw [MeasureTheory.sum_measure_preimage_singleton _
      fun i _ ↦ hqX (MeasurableSet.singleton i)]
    simp
  have hsumY : ∑ j, ν (qY ⁻¹' {j}) = 1 := by
    rw [MeasureTheory.sum_measure_preimage_singleton _
      fun j _ ↦ hqY (MeasurableSet.singleton j)]
    simp
  set pμ : PMF (Fin n) := PMF.ofFintype _ hsumX
  set pν : PMF (Fin m) := PMF.ofFintype _ hsumY
  have hpμ : ∀ i, pμ i = μ (qX ⁻¹' {i}) := fun i ↦ rfl
  have hpν : ∀ j, pν j = ν (qY ⁻¹' {j}) := fun j ↦ rfl
  -- solve the finite problem for the cost read at the marked points
  set C : Fin n × Fin m → ℝ := fun p ↦ max 0 (c (v p.1, w p.2) - ε / 2)
  have hC0 : ∀ p, 0 ≤ C p := fun p ↦ le_max_left _ _
  obtain ⟨T, a, b, -, hfeas, hTcost⟩ := exists_cost_eq_finiteDualValue C pμ pν
  -- the step potentials are feasible for the continuous cost
  have hstepfeas : ∀ x y, a (qX x) + b (qY y) ≤ c (x, y) := by
    intro x y
    refine (hfeas (qX x) (qY y)).trans (max_le (hc0 _) ?_)
    have := abs_lt.1 (hosc x y)
    linarith [this.1, this.2]
  -- and the primal cost is at most the finite cost, up to `ε`
  have hlift : transportCost (fun z ↦ ENNReal.ofReal (c z)) μ ν
      ≤ ENNReal.ofReal (T.cost C + ε) := by
    rw [← T.cost_add_const C ε]
    refine transportCost_le_ofReal_cost hqX hqY hpμ hpν T
      (fun p ↦ by have := hC0 p; linarith) fun x y ↦ ?_
    have h1 : c (v (qX x), w (qY y)) - ε / 2 ≤ C (qX x, qY y) := le_max_right _ _
    have := abs_lt.1 (hosc x y)
    linarith [this.1, this.2]
  -- upgrade the step potentials to continuous ones
  obtain ⟨φ, ψ, hφc, hψc, hfeas', hφle, hψle⟩ :=
    exists_continuous_feasible_pair_dominating (c := c) (φ := fun x ↦ a (qX x))
      (ψ := fun y ↦ b (qY y)) hc hstepfeas
  refine ⟨φ, ψ, hφc, hψc, hfeas', hlift.trans (ENNReal.ofReal_le_ofReal ?_)⟩
  have hint : kantorovichDualValue μ ν (fun x ↦ a (qX x)) (fun y ↦ b (qY y))
      = finiteDualValue pμ pν a b := by
    rw [kantorovichDualValue_def, finiteDualValue_def, integral_comp_eq_sum μ hqX a,
      integral_comp_eq_sum ν hqY b]
    simp only [hpμ, hpν]
  have hmono : kantorovichDualValue μ ν (fun x ↦ a (qX x)) (fun y ↦ b (qY y))
      ≤ kantorovichDualValue μ ν φ ψ := by
    rw [kantorovichDualValue_def, kantorovichDualValue_def]
    refine add_le_add
      (integral_mono ?_ (integrable_of_continuous hφc) hφle)
      (integral_mono ?_ (integrable_of_continuous hψc) hψle)
    · exact (Integrable.of_finite (μ := μ.map qX)).comp_measurable hqX
    · exact (Integrable.of_finite (μ := ν.map qY)).comp_measurable hqY
  rw [hTcost, ← hint]
  linarith

/-- **Strong Kantorovich duality on compact pseudometrizable spaces.** For probability measures
on compact pseudometric spaces and a continuous nonnegative cost, the primal transport cost is
the least upper bound of the values of the pairs of continuous potentials satisfying the
Kantorovich constraint. -/
theorem isLUB_kantorovichDualValue_continuous [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hc : Continuous c) (hc0 : ∀ z, 0 ≤ c z) :
    IsLUB {r : ℝ | ∃ φ ψ, Continuous φ ∧ Continuous ψ ∧ (∀ x y, φ x + ψ y ≤ c (x, y)) ∧
        kantorovichDualValue μ ν φ ψ = r}
      (transportCost (fun z ↦ ENNReal.ofReal (c z)) μ ν).toReal := by
  have hne := transportCost_ne_top_of_continuous (μ := μ) (ν := ν)
    ⟨_, isCoupling_prod μ ν⟩ hc
  constructor
  · rintro r ⟨φ, ψ, hφc, hψc, hfeas, rfl⟩
    have hdual := (dualFeasible_ofReal_iff hc0 φ ψ).2 hfeas
    exact hdual.kantorovichDualValue_le_toReal_transportCost hne
      (integrable_of_continuous hφc) (integrable_of_continuous hψc)
  · intro b hb
    have hb0 : (0 : ℝ) ≤ b := hb (zero_mem_continuousDualValues hc0)
    refine _root_.le_of_forall_pos_le_add fun ε hε ↦ ?_
    obtain ⟨φ, ψ, hφc, hψc, hfeas, hle⟩ :=
      exists_continuous_forall_add_le_transportCost_le (μ := μ) (ν := ν) hc hc0 hε
    have hvb : kantorovichDualValue μ ν φ ψ ≤ b := hb ⟨φ, ψ, hφc, hψc, hfeas, rfl⟩
    exact ENNReal.toReal_le_of_le_ofReal (by linarith)
      (hle.trans (ENNReal.ofReal_le_ofReal (by linarith)))

/-- **Strong Kantorovich duality against the integrable dual class.** For probability measures,
enlarging the dual class from the continuous to the merely integrable potentials does not change
the value of the dual problem: it is still the primal transport cost. -/
theorem isLUB_kantorovichDualValue_integrable [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hc : Continuous c) (hc0 : ∀ z, 0 ≤ c z) :
    IsLUB {r : ℝ | ∃ φ ψ, Integrable φ μ ∧ Integrable ψ ν ∧ (∀ x y, φ x + ψ y ≤ c (x, y)) ∧
        kantorovichDualValue μ ν φ ψ = r}
      (transportCost (fun z ↦ ENNReal.ofReal (c z)) μ ν).toReal := by
  have hne := transportCost_ne_top_of_continuous (μ := μ) (ν := ν)
    ⟨_, isCoupling_prod μ ν⟩ hc
  refine ⟨?_, fun b hb ↦ (isLUB_kantorovichDualValue_continuous hc hc0).2 fun r hr ↦ ?_⟩
  · rintro r ⟨φ, ψ, hφ, hψ, hfeas, rfl⟩
    exact ((dualFeasible_ofReal_iff hc0 φ ψ).2 hfeas).kantorovichDualValue_le_toReal_transportCost
      hne hφ hψ
  · obtain ⟨φ, ψ, hφc, hψc, hfeas, rfl⟩ := hr
    exact hb ⟨φ, ψ, integrable_of_continuous hφc, integrable_of_continuous hψc, hfeas, rfl⟩

/-- **Strong Kantorovich duality for probability measures**, read as an equality between the
primal value and the supremum of the dual values over the continuous potentials. -/
theorem toReal_transportCost_eq_sSup [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hc : Continuous c) (hc0 : ∀ z, 0 ≤ c z) :
    (transportCost (fun z ↦ ENNReal.ofReal (c z)) μ ν).toReal
      = sSup {r : ℝ | ∃ φ ψ, Continuous φ ∧ Continuous ψ ∧ (∀ x y, φ x + ψ y ≤ c (x, y)) ∧
        kantorovichDualValue μ ν φ ψ = r} :=
  ((isLUB_kantorovichDualValue_continuous hc hc0).csSup_eq
    ⟨0, zero_mem_continuousDualValues hc0⟩).symm

/-- **Strong Kantorovich duality for probability measures**, read in `ℝ≥0∞`: the primal transport
cost is the supremum of the dual values of the continuous feasible pairs. -/
theorem transportCost_eq_ofReal_sSup [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hc : Continuous c) (hc0 : ∀ z, 0 ≤ c z) :
    transportCost (fun z ↦ ENNReal.ofReal (c z)) μ ν
      = ENNReal.ofReal (sSup {r : ℝ | ∃ φ ψ, Continuous φ ∧ Continuous ψ ∧
        (∀ x y, φ x + ψ y ≤ c (x, y)) ∧ kantorovichDualValue μ ν φ ψ = r}) := by
  rw [← toReal_transportCost_eq_sSup hc hc0,
    ENNReal.ofReal_toReal
      (transportCost_ne_top_of_continuous ⟨_, isCoupling_prod μ ν⟩ hc)]

end Duality

end TauCeti
