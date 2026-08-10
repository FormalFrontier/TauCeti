/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Probability.DeFinetti.ViaL2.EmpiricalToDirecting
public import TauCeti.Probability.Process.DisjointWindow
public import TauCeti.MeasureTheory.Function.ProductL1Convergence

/-!
# Simultaneous convergence over disjoint windows

For a contractable process on a standard Borel state space, the block averages of finitely many
indicators over **pairwise disjoint** windows converge in `L¹`, simultaneously, to the product of
the corresponding directing-measure evaluations:

```text
∫ |∏ i, blockAverage 𝟙_{B i} (window (n+1) i) - ∏ i, (directingMeasure ω).real (B i)| dμ → 0.
```

The selections are `disjointWindow i`, so factor `i` occupies `[(i+1)(n+1), (i+2)(n+1))`. Distinct
factors never collide (`disjointWindow_ne`), and the windows move outward as the length grows —
which is exactly what fixed starts cannot do, since windows from distinct fixed starts overlap once
the common length exceeds the gap between the starts.

Two ingredients meet here.

*Each factor converges.* The indicator-to-directing-measure convergence in
`ViaL2/EmpiricalToDirecting.lean` accepts any eventually-injective moving selection, and
`disjointWindow i` is injective at every length. The limit does not depend on the selection,
so all `m` factors converge to their directing-measure evaluations against the *same* directing
measure.

*The product follows.* `tendsto_integral_norm_prod_sub_prod` turns finitely many `L¹`
convergences into convergence of the product, and indicators supply the unit-ball bounds it needs
on both sides.

## References

* Roadmap: `TauCetiRoadmap/Exchangeability/README.md`, **Layer 3** — the simultaneous
  disjoint-window product convergence that the finite-block conditional factorization consumes.
-/

public section

open Filter MeasureTheory

open scoped Topology

namespace TauCeti

namespace Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- **Simultaneous disjoint-window convergence.** For a contractable process on a standard Borel
state space and finitely many measurable sets `B i`, the product of the block averages of the
indicators over the pairwise disjoint selections `disjointWindow i` converges in `L¹` to the
product
of the directing-measure evaluations. -/
theorem Contractable.tendsto_integral_abs_prod_blockAverage_window_sub_prod_directingMeasure
    [StandardBorelSpace α] [Nonempty α] {μ : Measure Ω} [IsFiniteMeasure μ] {X : ℕ → Ω → α}
    (hX : Contractable μ X) (hX_meas : ∀ i, Measurable (X i))
    {m : ℕ} (B : Fin m → Set α) (hB : ∀ i, MeasurableSet (B i)) :
    Tendsto (fun n => ∫ ω,
        |(∏ i : Fin m, blockAverage (fun c ω => (B i).indicator (fun _ => (1 : ℝ)) (X c ω))
            (disjointWindow (i : ℕ) n) ω)
          - ∏ i : Fin m, (directingMeasure μ X ω).real (B i)| ∂μ) atTop (𝓝 0) := by
  classical
  set F : Fin m → ℕ → Ω → ℝ := fun i n =>
    blockAverage (fun c ω => (B i).indicator (fun _ => (1 : ℝ)) (X c ω))
      (disjointWindow (i : ℕ) n) with hF
  set g : Fin m → Ω → ℝ := fun i ω => (directingMeasure μ X ω).real (B i) with hg
  have hind : ∀ i c, Measurable fun ω => (B i).indicator (fun _ => (1 : ℝ)) (X c ω) := fun i c =>
    (measurable_const.indicator (hB i)).comp (hX_meas c)
  have hind_mem : ∀ i c ω, 0 ≤ (B i).indicator (fun _ => (1 : ℝ)) (X c ω) ∧
      (B i).indicator (fun _ => (1 : ℝ)) (X c ω) ≤ 1 := by
    intro i c ω
    by_cases h : X c ω ∈ B i <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, h]
  have hFapp : ∀ i n ω, F i n ω
      = (((n + 1 : ℕ) : ℝ))⁻¹ * ∑ j : Fin (n + 1),
          (B i).indicator (fun _ => (1 : ℝ)) (X (disjointWindow (i : ℕ) n j) ω) := by
    intro i n ω; simp only [hF, blockAverage_apply]
  have hF_meas : ∀ i n, Measurable (F i n) := by
    intro i n
    have : F i n = fun ω => (((n + 1 : ℕ) : ℝ))⁻¹ * ∑ j : Fin (n + 1),
        (B i).indicator (fun _ => (1 : ℝ)) (X (disjointWindow (i : ℕ) n j) ω) :=
      funext (hFapp i n)
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
        (B i).indicator (fun _ => (1 : ℝ)) (X (disjointWindow (i : ℕ) n j) ω)
          ≤ ((n + 1 : ℕ) : ℝ) := by
      calc ∑ j : Fin (n + 1),
            (B i).indicator (fun _ => (1 : ℝ)) (X (disjointWindow (i : ℕ) n j) ω)
          ≤ ∑ _j : Fin (n + 1), (1 : ℝ) := Finset.sum_le_sum fun j _ => (hind_mem i _ ω).2
        _ = ((n + 1 : ℕ) : ℝ) := by simp
    rw [Real.norm_of_nonneg hnonneg, hFapp]
    calc (((n + 1 : ℕ) : ℝ))⁻¹ * ∑ j : Fin (n + 1),
          (B i).indicator (fun _ => (1 : ℝ)) (X (disjointWindow (i : ℕ) n j) ω)
        ≤ (((n + 1 : ℕ) : ℝ))⁻¹ * ((n + 1 : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_left hsum (inv_nonneg.2 hpos.le)
      _ = 1 := inv_mul_cancel₀ hpos.ne'
  have hg_meas : ∀ i, Measurable (g i) := fun i =>
    (measurable_directingMeasure_coe (tailProcess_le_ambient 0 fun c _ => hX_meas c)
      (hB i)).ennreal_toReal
  have hg_le : ∀ i ω, ‖g i ω‖ ≤ 1 := by
    intro i ω
    rw [Real.norm_of_nonneg measureReal_nonneg]
    exact measureReal_le_one
  -- Each window converges: the selection is injective at every length.
  have hconv : ∀ i ∈ Finset.univ,
      Tendsto (fun n => ∫ ω, ‖F i n ω - g i ω‖ ∂μ) atTop (𝓝 0) := by
    intro i _
    simpa only [Real.norm_eq_abs, hF, hg] using
      hX.tendsto_integral_abs_blockAverage_indicator_sub_directingMeasure hX_meas (hB i)
        (disjointWindow (i : ℕ)) (disjointWindow_eventually_injective (i : ℕ))
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
