/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Probability.DeFinetti.ViaL2.EmpiricalToDirecting
public import TauCeti.Probability.Process.DisjointWindow
public import TauCeti.MeasureTheory.Function.ProductL1Convergence

/-!
# Simultaneous convergence of a product of indicator block averages

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
`ViaL2/EmpiricalToDirecting.lean` accepts any eventually-injective moving selection. The general
theorem below therefore takes an arbitrary family of such selections; cross-factor disjointness is
not needed for the convergence, only for what the terms mean downstream. The limit does not
depend on the selection,
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

namespace Contractable

/-- **Simultaneous convergence of a product of indicator block averages.** For a contractable
process on a standard Borel state space and finitely many measurable sets `B i`, each read along
its own selection `k i`, the product of the block averages converges in `L¹` to the product of the
directing-measure evaluations.

Only each selection's own eventual injectivity is used; nothing here needs the selections to be
disjoint from one another. Disjointness matters for what the *terms* mean downstream, not for the
convergence. -/
theorem tendsto_integral_abs_prod_blockAverage_indicator_sub_prod_directingMeasure
    [StandardBorelSpace α] [Nonempty α] {μ : Measure Ω} [IsFiniteMeasure μ] {X : ℕ → Ω → α}
    (hX : Contractable μ X) (hX_meas : ∀ i, Measurable (X i))
    {m : ℕ} (B : Fin m → Set α) (hB : ∀ i, MeasurableSet (B i))
    (k : Fin m → ∀ n : ℕ, Fin (n + 1) → ℕ)
    (hk : ∀ i, ∀ᶠ n in atTop, Function.Injective (k i n)) :
    Tendsto (fun n => ∫ ω,
        |(∏ i : Fin m, blockAverage (fun c ω => (B i).indicator (fun _ => (1 : ℝ)) (X c ω))
            (k i n) ω)
          - ∏ i : Fin m, (directingMeasure μ X ω).real (B i)| ∂μ) atTop (𝓝 0) := by
  classical
  set F : Fin m → ℕ → Ω → ℝ := fun i n =>
    blockAverage (fun c ω => (B i).indicator (fun _ => (1 : ℝ)) (X c ω)) (k i n) with hF
  set g : Fin m → Ω → ℝ := fun i ω => (directingMeasure μ X ω).real (B i) with hg
  have hind : ∀ i c, Measurable fun ω => (B i).indicator (fun _ => (1 : ℝ)) (X c ω) := fun i c =>
    (measurable_const.indicator (hB i)).comp (hX_meas c)
  have hind0 : ∀ i c ω, 0 ≤ (B i).indicator (fun _ => (1 : ℝ)) (X c ω) :=
    fun _ _ _ => Set.indicator_apply_nonneg fun _ => zero_le_one
  have hind1 : ∀ i c ω, (B i).indicator (fun _ => (1 : ℝ)) (X c ω) ≤ 1 :=
    fun _ _ _ => Set.indicator_apply_le' (fun _ => le_rfl) fun _ => zero_le_one
  have hF_meas : ∀ i n, Measurable (F i n) := by
    intro i n
    have hrw : F i n = fun ω => ((n + 1 : ℕ) : ℝ)⁻¹ * ∑ j : Fin (n + 1),
        (B i).indicator (fun _ => (1 : ℝ)) (X (k i n j) ω) :=
      funext fun ω => blockAverage_apply _ ω
    rw [hrw]
    exact measurable_const.mul (Finset.measurable_sum _ fun j _ => hind i _)
  have hF_le : ∀ i n ω, ‖F i n ω‖ ≤ 1 := fun i n ω => by
    rw [hF, Real.norm_of_nonneg (blockAverage_nonneg fun j => hind0 i (k i n j) ω)]
    exact blockAverage_le_one fun j => hind1 i (k i n j) ω
  have hg_meas : ∀ i, Measurable (g i) := fun i =>
    (measurable_directingMeasure_coe (tailProcess_le_ambient 0 fun c _ => hX_meas c)
      (hB i)).ennreal_toReal
  have hg_le : ∀ i ω, ‖g i ω‖ ≤ 1 := fun i ω => by
    rw [hg, Real.norm_of_nonneg measureReal_nonneg]; exact measureReal_le_one
  have hconv : ∀ i ∈ Finset.univ,
      Tendsto (fun n => ∫ ω, ‖F i n ω - g i ω‖ ∂μ) atTop (𝓝 0) := by
    intro i _
    simpa only [Real.norm_eq_abs, hF, hg] using
      hX.tendsto_integral_abs_blockAverage_indicator_sub_directingMeasure hX_meas (hB i)
        (k i) (hk i)
  simpa only [Real.norm_eq_abs, hF, hg] using
    TauCeti.MeasureTheory.tendsto_integral_norm_prod_sub_prod
      (s := (Finset.univ : Finset (Fin m))) (F := F) (g := g)
      (fun i _ n => (hF_meas i n).aestronglyMeasurable)
      (fun i _ => (hg_meas i).aestronglyMeasurable)
      (fun i _ n => ae_of_all _ fun ω => hF_le i n ω)
      (fun i _ => ae_of_all _ fun ω => hg_le i ω) hconv

/-- **The disjoint-window instance.** The block averages are of indicators, as in the general
theorem above; reading factor `i` along `disjointWindow i` keeps distinct factors in disjoint
blocks at every length, which is the configuration a finite-block factorization consumes. -/
theorem tendsto_integral_abs_prod_blockAverage_indicator_disjointWindow_sub_prod_directingMeasure
    [StandardBorelSpace α] [Nonempty α] {μ : Measure Ω} [IsFiniteMeasure μ] {X : ℕ → Ω → α}
    (hX : Contractable μ X) (hX_meas : ∀ i, Measurable (X i))
    {m : ℕ} (B : Fin m → Set α) (hB : ∀ i, MeasurableSet (B i)) :
    Tendsto (fun n => ∫ ω,
        |(∏ i : Fin m, blockAverage (fun c ω => (B i).indicator (fun _ => (1 : ℝ)) (X c ω))
            (disjointWindow (i : ℕ) n) ω)
          - ∏ i : Fin m, (directingMeasure μ X ω).real (B i)| ∂μ) atTop (𝓝 0) :=
  hX.tendsto_integral_abs_prod_blockAverage_indicator_sub_prod_directingMeasure hX_meas B hB
    (fun i => disjointWindow (i : ℕ)) fun i => disjointWindow_eventually_injective (i : ℕ)

end Contractable

end Probability


end TauCeti

end
