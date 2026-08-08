/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Probability.DeFinetti.ViaL2.EmpiricalToDirecting
public import TauCeti.MeasureTheory.Function.ProductL1Convergence

/-!
# Convergence of a product of fixed-start window averages

For a contractable process on a standard Borel state space, finitely many Cesàro window averages of
indicators converge in `L¹`, *simultaneously*, to the product of the corresponding directing-measure
evaluations:

```text
∫ |∏ i, blockAverage 𝟙_{B i} (window i) - ∏ i, (directingMeasure ω).real (B i)| dμ → 0.
```

Each factor converges by
`Contractable.tendsto_integral_abs_blockAverage_indicator_sub_directingMeasure`, and
`tendsto_integral_norm_prod_sub_prod` upgrades finitely many `L¹` convergences to convergence of the
product. The unit-ball hypotheses that lemma needs are exactly what indicators supply: a window
average of an indicator lies in `[0, 1]`, and so does a probability-measure evaluation.

⚠ The start points `r : Fin m → ℕ` are **fixed**, while the window length grows with `n`. For
`m ≥ 2` the windows therefore overlap once `n` is large: this is *not* a disjoint-window statement.
What it does give is the step from "each factor converges in `L¹`" to "the product converges in
`L¹`", jointly in the sense that a single limit governs all `m` factors at once.

The block factorization additionally needs the windows to be pairwise disjoint, which requires
starts that grow with the window length — the scheme `window N i` of
`Probability/Process/DisjointWindow.lean`. That is a *moving*-window statement: both the start
`(i + 1) * N` and the length `N` grow together, so it does not follow from the fixed-start
convergence used here and has to be established separately.

## References

* Roadmap: `TauCetiRoadmap/Exchangeability/README.md`, **Layer 3** — the `L²` averaging library and
  the standard-Borel de Finetti route. This is the product step of the "simultaneous disjoint-window
  product convergence" prerequisite; the disjointness half is separate, as noted above.
-/

public section

open Filter MeasureTheory

open scoped Topology

namespace TauCeti

namespace Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- **Simultaneous window-product convergence.** For a contractable process on a standard Borel
state space and finitely many measurable sets `B i` with window start points `r i`, the product of
the Cesàro window averages of the indicators converges in `L¹` to the product of the
directing-measure evaluations. -/
theorem Contractable.tendsto_integral_abs_prod_blockAverage_indicator_sub_prod_directingMeasure
    [StandardBorelSpace α] [Nonempty α] {μ : Measure Ω} [IsFiniteMeasure μ] {X : ℕ → Ω → α}
    (hX : Contractable μ X) (hX_meas : ∀ i, Measurable (X i))
    {m : ℕ} (B : Fin m → Set α) (hB : ∀ i, MeasurableSet (B i)) (r : Fin m → ℕ) :
    Tendsto (fun n => ∫ ω,
        |(∏ i, blockAverage (fun k ω => (B i).indicator (fun _ => (1 : ℝ)) (X k ω))
            (fun j : Fin (n + 1) => r i + (j : ℕ)) ω)
          - ∏ i, (directingMeasure μ X ω).real (B i)| ∂μ) atTop (𝓝 0) := by
  classical
  set F : Fin m → ℕ → Ω → ℝ := fun i n =>
    blockAverage (fun k ω => (B i).indicator (fun _ => (1 : ℝ)) (X k ω))
      fun j : Fin (n + 1) => r i + (j : ℕ) with hF
  set g : Fin m → Ω → ℝ := fun i ω => (directingMeasure μ X ω).real (B i) with hg
  have hind : ∀ i k, Measurable fun ω => (B i).indicator (fun _ => (1 : ℝ)) (X k ω) := fun i k =>
    (measurable_const.indicator (hB i)).comp (hX_meas k)
  have hind_mem : ∀ i k ω, 0 ≤ (B i).indicator (fun _ => (1 : ℝ)) (X k ω) ∧
      (B i).indicator (fun _ => (1 : ℝ)) (X k ω) ≤ 1 := by
    intro i k ω
    by_cases h : X k ω ∈ B i <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, h]
  have hFapp : ∀ i n ω, F i n ω
      = (((n + 1 : ℕ) : ℝ))⁻¹ * ∑ j : Fin (n + 1),
          (B i).indicator (fun _ => (1 : ℝ)) (X (r i + (j : ℕ)) ω) := by
    intro i n ω; simp only [hF, blockAverage_apply]
  -- Each window average is measurable and lies in `[0, 1]`.
  have hF_meas : ∀ i n, Measurable (F i n) := by
    intro i n
    have : F i n = fun ω => (((n + 1 : ℕ) : ℝ))⁻¹ * ∑ j : Fin (n + 1),
        (B i).indicator (fun _ => (1 : ℝ)) (X (r i + (j : ℕ)) ω) := funext (hFapp i n)
    rw [this]
    exact measurable_const.mul (Finset.measurable_sum _ fun j _ => hind i _)
  have hF_le : ∀ i n ω, ‖F i n ω‖ ≤ 1 := by
    intro i n ω
    have hpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    have hnonneg : 0 ≤ F i n ω := by
      rw [hFapp]
      exact mul_nonneg (inv_nonneg.2 hpos.le)
        (Finset.sum_nonneg fun j _ => (hind_mem i _ ω).1)
    have hsum : ∑ j : Fin (n + 1),
        (B i).indicator (fun _ => (1 : ℝ)) (X (r i + (j : ℕ)) ω) ≤ ((n + 1 : ℕ) : ℝ) := by
      calc ∑ j : Fin (n + 1), (B i).indicator (fun _ => (1 : ℝ)) (X (r i + (j : ℕ)) ω)
          ≤ ∑ _j : Fin (n + 1), (1 : ℝ) := Finset.sum_le_sum fun j _ => (hind_mem i _ ω).2
        _ = ((n + 1 : ℕ) : ℝ) := by simp
    rw [Real.norm_of_nonneg hnonneg, hFapp]
    calc (((n + 1 : ℕ) : ℝ))⁻¹ * ∑ j : Fin (n + 1),
          (B i).indicator (fun _ => (1 : ℝ)) (X (r i + (j : ℕ)) ω)
        ≤ (((n + 1 : ℕ) : ℝ))⁻¹ * ((n + 1 : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_left hsum (inv_nonneg.2 hpos.le)
      _ = 1 := inv_mul_cancel₀ hpos.ne'
  -- The limits are probability-measure evaluations, hence also in `[0, 1]`.
  have hg_meas : ∀ i, Measurable (g i) := fun i =>
    (measurable_directingMeasure_coe (tailProcess_le_ambient 0 fun k _ => hX_meas k)
      (hB i)).ennreal_toReal
  have hg_le : ∀ i ω, ‖g i ω‖ ≤ 1 := by
    intro i ω
    have hnn : 0 ≤ g i ω := measureReal_nonneg
    rw [Real.norm_of_nonneg hnn]
    exact measureReal_le_one
  have hconv : ∀ i ∈ Finset.univ,
      Tendsto (fun n => ∫ ω, ‖F i n ω - g i ω‖ ∂μ) atTop (𝓝 0) := by
    intro i _
    simpa only [Real.norm_eq_abs, hF, hg] using
      hX.tendsto_integral_abs_blockAverage_indicator_sub_directingMeasure hX_meas (hB i) (r i)
  simpa only [Real.norm_eq_abs] using
    TauCeti.MeasureTheory.tendsto_integral_norm_prod_sub_prod
      (s := (Finset.univ : Finset (Fin m))) (F := F) (g := g)
      (fun i _ n => (hF_meas i n).aestronglyMeasurable)
      (fun i _ => (hg_meas i).aestronglyMeasurable)
      (fun i _ n => ae_of_all _ fun ω => hF_le i n ω)
      (fun i _ => ae_of_all _ fun ω => hg_le i ω) hconv

end Probability

end TauCeti

end
