/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Exchangeability.CondExp
public import TauCeti.Probability.Exchangeability.L2.TailMeasurability
import TauCeti.MeasureTheory.Function.BoundedMemLp
import TauCeti.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# The Cesàro limit of an observable is its conditional expectation given the process tail

Layer 3 of the Exchangeability roadmap produces the Cesàro limit of an observable of a contractable
process twice over: `weighted_sums_converge_L1_of_memLp` gives it as an abstract `L¹` limit, and
`Contractable.exists_tailProcess_measurable_cesaro_limit_of_memLp` places it on the process tail
`tailProcess X`. Neither says *what* the limit is.

This file identifies it:

* `Contractable.condExp_blockAverage_tailProcess_ae_eq` — every block average of `f ∘ X` has the
  same conditional expectation given `tailProcess X` as the single coordinate `f ∘ X 0`;
* `Contractable.tendsto_integral_abs_blockAverage_sub_condExp_of_memLp` — the block averages
  converge in `L¹` to `μ[f ∘ X 0 | tailProcess X]` along *every* eventually injective moving
  selection, fixed starts (`fixedStart`) and disjoint windows (`disjointWindow`) alike, with
  `Contractable.tendsto_integral_abs_blockAverage_sub_condExp` the bounded-observable form;
* `Contractable.ae_eq_condExp_tailProcess_of_tendsto_integral_abs` — consequently *any* `L¹` limit
  of those block averages, along any eventually injective selection, is a.e. that conditional
  expectation.

Both ingredients are already in place, and the argument is short. Contractability makes all
coordinates share a conditional law given the tail (`Contractable.condExp_comp_tailProcess_ae_eq`),
so the conditional expectation of every window is `μ[f ∘ X 0 | tailProcess X]`; the limit is
tail-measurable, hence its own conditional expectation; and conditional expectation is
`L¹`-continuous (`TauCeti.MeasureTheory.condExp_ae_eq_of_forall_condExp_ae_eq_of_tendsto_eLpNorm`).
No reverse-martingale convergence theorem is used, which is what keeps this on the `L²` route
rather than the martingale one.

The roadmap maps `Exchangeability/Bridge/CesaroToCondExp.lean` in `cameronfreer/exchangeability`
(pin `e0532e59ceff23edab44dda9ab0655debbc9cc22`) as the Layer 3 source for this bridge. No material
is ported from it: the identification here is assembled from Tau Ceti's own tail-measurability
result and its `L¹`-continuity lemma, and it conditions on the *process* tail `tailProcess X`
throughout.
-/

public section

noncomputable section

open Filter MeasureTheory
open scoped ENNReal Topology

namespace TauCeti

namespace Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- **Block averages do not move the conditional expectation given the tail.** For a contractable
process all coordinates share a conditional law given `tailProcess X`, so the conditional
expectation of the average of any nonempty finite block of `f ∘ X` is the conditional expectation of
a single coordinate. -/
theorem Contractable.condExp_blockAverage_tailProcess_ae_eq {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → α} (hX : Contractable μ X) (hX_meas : ∀ i, Measurable (X i)) {f : α → ℝ}
    (hf : Measurable f) (hf_int : Integrable (fun ω => f (X 0 ω)) μ) {n : ℕ} (k : Fin (n + 1) → ℕ) :
    μ[blockAverage (fun i ω => f (X i ω)) k | tailProcess X]
      =ᵐ[μ] μ[fun ω => f (X 0 ω) | tailProcess X] := by
  have hint : ∀ i, Integrable (fun ω => f (X i ω)) μ :=
    hX.integrable_comp (fun i => (hX_meas i).aemeasurable) hf hf_int
  have hterm : ∀ᵐ ω ∂μ, ∀ j : Fin (n + 1),
      (μ[fun ω => f (X (k j) ω) | tailProcess X]) ω
        = (μ[fun ω => f (X 0 ω) | tailProcess X]) ω :=
    ae_all_iff.2 fun j => hX.condExp_comp_tailProcess_ae_eq hX_meas hf
  -- Conditional expectation passes inside the block average, and the block has `n + 1` terms all
  -- with the same conditional expectation, so the average is that common value.
  refine (condExp_blockAverage k fun j => hint (k j)).trans ?_
  filter_upwards [hterm] with ω hω
  exact blockAverage_apply_of_forall_eq n.succ_pos hω

/-- **The block averages converge to a conditional expectation.** For a measurable observable `f`
whose composite with a single coordinate is square-integrable, the block averages of `f ∘ X` along
a contractable process converge in `L¹` to `μ[f ∘ X 0 | tailProcess X]`, for every selection `k`
that is injective for all sufficiently large lengths — the selection may move with the length.

This is the identification the Layer 3 route needs: the limit supplied by
`weighted_sums_converge_L1_of_memLp` is not merely tail-measurable, it is the conditional
expectation of a single coordinate given the tail. -/
theorem Contractable.tendsto_integral_abs_blockAverage_sub_condExp_of_memLp {μ : Measure Ω}
    [IsFiniteMeasure μ] {X : ℕ → Ω → α} (hX : Contractable μ X) (hX_meas : ∀ i, Measurable (X i))
    {f : α → ℝ} (hf : Measurable f) (hf_L2 : MemLp (fun ω => f (X 0 ω)) 2 μ)
    (k : ∀ n : ℕ, Fin (n + 1) → ℕ) (hk : ∀ᶠ n in atTop, Function.Injective (k n)) :
    Tendsto
      (fun m => ∫ ω, |blockAverage (fun i ω => f (X i ω)) (k m) ω
        - (μ[fun ω => f (X 0 ω) | tailProcess X]) ω| ∂μ)
      atTop (𝓝 0) := by
  have hX_ae : ∀ i, AEMeasurable (X i) μ := fun i => (hX_meas i).aemeasurable
  have hY_L2 : ∀ i : ℕ, MemLp (fun ω => f (X i ω)) 2 μ := hX.memLp_comp hX_ae hf hf_L2
  obtain ⟨a, ha_meas, ha_L1, ha_lim'⟩ :=
    hX.exists_tailProcess_measurable_cesaro_limit_of_memLp hX_ae hf hf_L2
  -- This route only needs the fixed-start instance of the moving-selection convergence.
  have ha_lim : ∀ r : ℕ, Tendsto
      (fun m => ∫ ω, |blockAverage (fun i ω => f (X i ω))
        (fun j : Fin (m + 1) => r + (j : ℕ)) ω - a ω| ∂μ) atTop (𝓝 0) := fun r =>
    by simpa only [funext (fixedStart_apply r _)] using
      ha_lim' (fixedStart r) (fixedStart_eventually_injective r)
  have ha_int : Integrable a μ := ha_L1.integrable le_rfl
  have hA_int : ∀ m : ℕ,
      Integrable (blockAverage (fun i ω => f (X i ω)) fun j : Fin (m + 1) => 0 + (j : ℕ)) μ :=
    fun m => (memLp_blockAverage _ fun j => hY_L2 (0 + (j : ℕ))).integrable one_le_two
  have ha_eq : a =ᵐ[μ] μ[fun ω => f (X 0 ω) | tailProcess X] := by
    -- `L¹` convergence of the prefix windows, in the `eLpNorm` form the continuity lemma expects.
    have hL1 : Tendsto (fun m => eLpNorm
        (a - blockAverage (fun i ω => f (X i ω)) fun j : Fin (m + 1) => 0 + (j : ℕ)) 1 μ)
        atTop (𝓝 0) := by
      simp_rw [eLpNorm_sub_comm a]
      exact TauCeti.MeasureTheory.tendsto_eLpNorm_one_of_tendsto_integral_norm_sub hA_int ha_int
        (by simpa [Real.norm_eq_abs] using ha_lim 0)
    -- The limit is tail-measurable, so it is its own conditional expectation.
    have htail_le : tailProcess X ≤ (inferInstance : MeasurableSpace Ω) :=
      tailProcess_le_ambient 0 fun k _ => hX_meas k
    have : IsFiniteMeasure (μ.trim htail_le) := isFiniteMeasure_trim htail_le
    have ha_condExp : μ[a | tailProcess X] = a :=
      condExp_of_stronglyMeasurable htail_le ha_meas.stronglyMeasurable ha_int
    exact ha_condExp ▸
      TauCeti.MeasureTheory.condExp_ae_eq_of_forall_condExp_ae_eq_of_tendsto_eLpNorm ha_int hA_int
        (fun m => hX.condExp_blockAverage_tailProcess_ae_eq hX_meas hf
          (MemLp.integrable one_le_two (hY_L2 0)) _) hL1
  refine (ha_lim' k hk).congr fun m => integral_congr_ae ?_
  filter_upwards [ha_eq] with ω hω
  rw [hω]

/-- **Bounded-observable form.** A uniform bound gives square-integrability of the composite on a
finite measure space, matching the entry point of `weighted_sums_converge_L1`. -/
theorem Contractable.tendsto_integral_abs_blockAverage_sub_condExp {μ : Measure Ω}
    [IsFiniteMeasure μ] {X : ℕ → Ω → α} (hX : Contractable μ X) (hX_meas : ∀ i, Measurable (X i))
    {f : α → ℝ} (hf : Measurable f) (hf_bdd : ∃ C, ∀ x, ‖f x‖ ≤ C)
    (k : ∀ n : ℕ, Fin (n + 1) → ℕ) (hk : ∀ᶠ n in atTop, Function.Injective (k n)) :
    Tendsto
      (fun m => ∫ ω, |blockAverage (fun i ω => f (X i ω)) (k m) ω
        - (μ[fun ω => f (X 0 ω) | tailProcess X]) ω| ∂μ)
      atTop (𝓝 0) :=
  let ⟨C, hC⟩ := hf_bdd
  hX.tendsto_integral_abs_blockAverage_sub_condExp_of_memLp hX_meas hf
    (memLp_comp_of_bound hf (hX_meas 0).aemeasurable C
      (Eventually.of_forall fun ω => hC (X 0 ω)) 2) k hk

/-- **Any `L¹` limit of the block averages is the conditional expectation.** The identification
form: along any eventually injective selection, an `L¹` limit is a.e. unique, so it must be the
conditional expectation the windows already converge to. -/
theorem Contractable.ae_eq_condExp_tailProcess_of_tendsto_integral_abs {μ : Measure Ω}
    [IsFiniteMeasure μ] {X : ℕ → Ω → α} (hX : Contractable μ X) (hX_meas : ∀ i, Measurable (X i))
    {f : α → ℝ} (hf : Measurable f) (hf_L2 : MemLp (fun ω => f (X 0 ω)) 2 μ)
    {k : ∀ n : ℕ, Fin (n + 1) → ℕ} (hk : ∀ᶠ n in atTop, Function.Injective (k n)) {a : Ω → ℝ}
    (ha_int : Integrable a μ)
    (ha_lim : Tendsto
      (fun m => ∫ ω, |blockAverage (fun i ω => f (X i ω)) (k m) ω - a ω| ∂μ)
      atTop (𝓝 0)) :
    a =ᵐ[μ] μ[fun ω => f (X 0 ω) | tailProcess X] := by
  have hX_ae : ∀ i, AEMeasurable (X i) μ := fun i => (hX_meas i).aemeasurable
  have hY_L2 : ∀ i : ℕ, MemLp (fun ω => f (X i ω)) 2 μ := hX.memLp_comp hX_ae hf hf_L2
  have hA_int : ∀ m : ℕ,
      Integrable (blockAverage (fun i ω => f (X i ω)) (k m)) μ :=
    fun m => (memLp_blockAverage _ fun j => hY_L2 (k m j)).integrable one_le_two
  -- Both `a` and the conditional expectation are `L¹` limits of the same windows, hence limits in
  -- measure, and a limit in measure is a.e. unique.
  exact tendstoInMeasure_ae_unique (f := fun m =>
      blockAverage (fun i ω => f (X i ω)) (k m))
    (tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero
      (fun m => (hA_int m).aestronglyMeasurable) ha_int.aestronglyMeasurable
      (TauCeti.MeasureTheory.tendsto_eLpNorm_one_of_tendsto_integral_norm_sub hA_int ha_int
        (by simpa [Real.norm_eq_abs] using ha_lim)))
    (tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero
      (fun m => (hA_int m).aestronglyMeasurable) integrable_condExp.aestronglyMeasurable
      (TauCeti.MeasureTheory.tendsto_eLpNorm_one_of_tendsto_integral_norm_sub hA_int
        integrable_condExp (by
          simpa [Real.norm_eq_abs] using
            hX.tendsto_integral_abs_blockAverage_sub_condExp_of_memLp hX_meas hf hf_L2 k hk)))

end Probability

end TauCeti
