/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Probability.DeFinetti.CondExpConvergence
public import TauCeti.Probability.Exchangeability.L2.TailMeasurability
import TauCeti.Probability.Exchangeability.Map
import TauCeti.MeasureTheory.Function.BoundedMemLp

/-!
# The Cesàro limit of an observable is its conditional expectation given the process tail

Layer 3 of the Exchangeability roadmap produces the Cesàro limit of an observable of a contractable
process twice over: `weighted_sums_converge_L1_of_memLp` gives it as an abstract `L¹` limit, and
`Contractable.exists_tailProcess_measurable_cesaro_limit_of_memLp` places it on the process tail
`tailProcess X`. Neither says *what* the limit is.

This file identifies it:

* `Contractable.condExp_blockAverage_tailProcess_eq` — every block average of `f ∘ X` has the same
  conditional expectation given `tailProcess X` as the single coordinate `f ∘ X 0`;
* `Contractable.tendsto_integral_abs_blockAverage_sub_condExp_of_memLp` — the fixed-start Cesàro
  windows converge in `L¹` to `μ[f ∘ X 0 | tailProcess X]`, with
  `Contractable.tendsto_integral_abs_blockAverage_sub_condExp` the bounded-observable form;
* `Contractable.ae_eq_condExp_tailProcess_of_tendsto_integral_abs` — consequently *any* `L¹` limit
  of those windows is a.e. that conditional expectation.

Both ingredients are already in place, and the argument is short. Contractability makes all
coordinates share a conditional law given the tail (`Contractable.condExp_comp_tailProcess_eq`), so
the conditional expectation of every window is `μ[f ∘ X 0 | tailProcess X]`; the limit is
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

/-- Two `L¹` limits of one sequence agree almost everywhere. Stated in the `∫ |·|` form in which
the Cesàro convergence results phrase their conclusions. -/
private theorem ae_eq_of_tendsto_integral_abs_sub {μ : Measure Ω} {A : ℕ → Ω → ℝ} {a b : Ω → ℝ}
    (hA : ∀ m, Integrable (A m) μ) (ha : Integrable a μ) (hb : Integrable b μ)
    (hA_a : Tendsto (fun m => ∫ ω, |A m ω - a ω| ∂μ) atTop (𝓝 0))
    (hA_b : Tendsto (fun m => ∫ ω, |A m ω - b ω| ∂μ) atTop (𝓝 0)) :
    a =ᵐ[μ] b := by
  have hle : ∀ m, ∫ ω, |a ω - b ω| ∂μ ≤ ∫ ω, |A m ω - a ω| ∂μ + ∫ ω, |A m ω - b ω| ∂μ := by
    intro m
    have hAa : Integrable (fun ω => |A m ω - a ω|) μ := ((hA m).sub ha).abs
    have hAb : Integrable (fun ω => |A m ω - b ω|) μ := ((hA m).sub hb).abs
    have hab : Integrable (fun ω => |a ω - b ω|) μ := (ha.sub hb).abs
    rw [← integral_add hAa hAb]
    refine integral_mono hab (hAa.add hAb) fun ω => ?_
    calc |a ω - b ω| ≤ |a ω - A m ω| + |A m ω - b ω| := abs_sub_le _ _ _
      _ = |A m ω - a ω| + |A m ω - b ω| := by rw [abs_sub_comm]
  have hzero : ∫ ω, |a ω - b ω| ∂μ = 0 := by
    refine le_antisymm ?_ (integral_nonneg fun ω => abs_nonneg _)
    refine le_of_tendsto_of_tendsto' (b := (atTop : Filter ℕ))
      (f := fun _ => ∫ ω, |a ω - b ω| ∂μ) tendsto_const_nhds ?_ hle
    simpa using hA_a.add hA_b
  have hae := (integral_eq_zero_iff_of_nonneg (fun ω => abs_nonneg _) (ha.sub hb).abs).1 hzero
  filter_upwards [hae] with ω hω
  exact sub_eq_zero.1 (abs_eq_zero.1 hω)

/-- **Block averages do not move the conditional expectation given the tail.** For a contractable
process all coordinates share a conditional law given `tailProcess X`, so the conditional
expectation of the average of any nonempty finite block of `f ∘ X` is the conditional expectation of
a single coordinate. -/
theorem Contractable.condExp_blockAverage_tailProcess_eq {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → α} (hX : Contractable μ X) (hX_meas : ∀ i, Measurable (X i)) {f : α → ℝ}
    (hf : Measurable f) (hf_int : Integrable (fun ω => f (X 0 ω)) μ) {n : ℕ} (k : Fin (n + 1) → ℕ) :
    μ[blockAverage (fun i ω => f (X i ω)) k | tailProcess X]
      =ᵐ[μ] μ[fun ω => f (X 0 ω) | tailProcess X] := by
  have hint : ∀ i, Integrable (fun ω => f (X i ω)) μ :=
    hX.integrable_comp (fun i => (hX_meas i).aemeasurable) hf hf_int
  rw [blockAverage_eq_sum]
  have hsmul := condExp_smul (μ := μ) (m := tailProcess X) (((n + 1 : ℕ) : ℝ)⁻¹)
    (∑ j : Fin (n + 1), fun ω => f (X (k j) ω))
  have hsum := condExp_finsetSum (μ := μ) (m := tailProcess X) (s := Finset.univ)
    (f := fun j : Fin (n + 1) => fun ω => f (X (k j) ω)) fun j _ => hint (k j)
  have hterm : ∀ᵐ ω ∂μ, ∀ j : Fin (n + 1),
      (μ[fun ω => f (X (k j) ω) | tailProcess X]) ω
        = (μ[fun ω => f (X 0 ω) | tailProcess X]) ω :=
    ae_all_iff.2 fun j => hX.condExp_comp_tailProcess_eq hX_meas hf hf_int
  filter_upwards [hsmul, hsum, hterm] with ω h1 h2 h3
  rw [h1, Pi.smul_apply, smul_eq_mul, h2, Finset.sum_apply,
    Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => h3 j, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul,
    inv_mul_cancel_left₀ (by positivity : ((n + 1 : ℕ) : ℝ) ≠ 0)]

/-- **The Cesàro windows converge to a conditional expectation.** For a measurable observable `f`
whose composite with a single coordinate is square-integrable, the fixed-start Cesàro windows of
`f ∘ X` along a contractable process converge in `L¹` to `μ[f ∘ X 0 | tailProcess X]`.

This is the identification the Layer 3 route needs: the limit supplied by
`weighted_sums_converge_L1_of_memLp` is not merely tail-measurable, it is the conditional
expectation of a single coordinate given the tail. -/
theorem Contractable.tendsto_integral_abs_blockAverage_sub_condExp_of_memLp {μ : Measure Ω}
    [IsFiniteMeasure μ] {X : ℕ → Ω → α} (hX : Contractable μ X) (hX_meas : ∀ i, Measurable (X i))
    {f : α → ℝ} (hf : Measurable f) (hf_L2 : MemLp (fun ω => f (X 0 ω)) 2 μ) (r : ℕ) :
    Tendsto
      (fun m => ∫ ω, |blockAverage (fun i ω => f (X i ω)) (fun j : Fin (m + 1) => r + j) ω
        - (μ[fun ω => f (X 0 ω) | tailProcess X]) ω| ∂μ)
      atTop (𝓝 0) := by
  have hX_ae : ∀ i, AEMeasurable (X i) μ := fun i => (hX_meas i).aemeasurable
  have hY_L2 : ∀ i : ℕ, MemLp (fun ω => f (X i ω)) 2 μ := fun i =>
    ((hX.map_values hf hX_ae).identDistrib_coord (hf.comp_aemeasurable (hX_ae 0))
      (hf.comp_aemeasurable (hX_ae i))).memLp_snd hf_L2
  obtain ⟨a, ha_meas, ha_L1, ha_lim⟩ :=
    hX.exists_tailProcess_measurable_cesaro_limit_of_memLp hX_ae hf hf_L2
  have ha_int : Integrable a μ := ha_L1.integrable le_rfl
  have hA_int : ∀ m : ℕ,
      Integrable (blockAverage (fun i ω => f (X i ω)) fun j : Fin (m + 1) => 0 + (j : ℕ)) μ :=
    fun m => (memLp_blockAverage _ fun j => hY_L2 (0 + (j : ℕ))).integrable one_le_two
  have ha_eq : a =ᵐ[μ] μ[fun ω => f (X 0 ω) | tailProcess X] := by
    -- `L¹` convergence of the prefix windows, in the `eLpNorm` form the continuity lemma expects.
    have hL1 : Tendsto (fun m => eLpNorm
        (a - blockAverage (fun i ω => f (X i ω)) fun j : Fin (m + 1) => 0 + (j : ℕ)) 1 μ)
        atTop (𝓝 0) := by
      have heq : ∀ m : ℕ, eLpNorm
          (a - blockAverage (fun i ω => f (X i ω)) fun j : Fin (m + 1) => 0 + (j : ℕ)) 1 μ
          = ENNReal.ofReal (∫ ω, |blockAverage (fun i ω => f (X i ω))
              (fun j : Fin (m + 1) => 0 + (j : ℕ)) ω - a ω| ∂μ) := by
        intro m
        rw [eLpNorm_one_eq_lintegral_enorm,
          ← ofReal_integral_norm_eq_lintegral_enorm (ha_int.sub (hA_int m))]
        refine congrArg ENNReal.ofReal (integral_congr_ae (Eventually.of_forall fun ω => ?_))
        change ‖a ω - _‖ = |_ - a ω|
        rw [Real.norm_eq_abs, abs_sub_comm]
      simp_rw [heq]
      have hcomp := (ENNReal.continuous_ofReal.tendsto 0).comp (ha_lim 0)
      rw [ENNReal.ofReal_zero] at hcomp
      exact hcomp
    -- The limit is tail-measurable, so it is its own conditional expectation.
    have htail_le : tailProcess X ≤ (inferInstance : MeasurableSpace Ω) :=
      tailProcess_le_ambient 0 fun k _ => hX_meas k
    have : IsFiniteMeasure (μ.trim htail_le) := isFiniteMeasure_trim htail_le
    have ha_condExp : μ[a | tailProcess X] = a :=
      condExp_of_stronglyMeasurable htail_le ha_meas.stronglyMeasurable ha_int
    exact ha_condExp ▸
      TauCeti.MeasureTheory.condExp_ae_eq_of_forall_condExp_ae_eq_of_tendsto_eLpNorm ha_int hA_int
        (fun m => hX.condExp_blockAverage_tailProcess_eq hX_meas hf
          (MemLp.integrable one_le_two (hY_L2 0)) _) hL1
  refine (ha_lim r).congr fun m => integral_congr_ae ?_
  filter_upwards [ha_eq] with ω hω
  rw [hω]

/-- **Bounded-observable form.** A uniform bound gives square-integrability of the composite on a
finite measure space, matching the entry point of `weighted_sums_converge_L1`. -/
theorem Contractable.tendsto_integral_abs_blockAverage_sub_condExp {μ : Measure Ω}
    [IsFiniteMeasure μ] {X : ℕ → Ω → α} (hX : Contractable μ X) (hX_meas : ∀ i, Measurable (X i))
    {f : α → ℝ} (hf : Measurable f) (hf_bdd : ∃ C, ∀ x, ‖f x‖ ≤ C) (r : ℕ) :
    Tendsto
      (fun m => ∫ ω, |blockAverage (fun i ω => f (X i ω)) (fun j : Fin (m + 1) => r + j) ω
        - (μ[fun ω => f (X 0 ω) | tailProcess X]) ω| ∂μ)
      atTop (𝓝 0) :=
  let ⟨C, hC⟩ := hf_bdd
  hX.tendsto_integral_abs_blockAverage_sub_condExp_of_memLp hX_meas hf
    (memLp_comp_of_bound hf (hX_meas 0).aemeasurable C
      (Eventually.of_forall fun ω => hC (X 0 ω)) 2) r

/-- **Any `L¹` limit of the Cesàro windows is the conditional expectation.** The identification
form: one fixed start `r` suffices, since an `L¹` limit is a.e. unique. -/
theorem Contractable.ae_eq_condExp_tailProcess_of_tendsto_integral_abs {μ : Measure Ω}
    [IsFiniteMeasure μ] {X : ℕ → Ω → α} (hX : Contractable μ X) (hX_meas : ∀ i, Measurable (X i))
    {f : α → ℝ} (hf : Measurable f) (hf_L2 : MemLp (fun ω => f (X 0 ω)) 2 μ) {r : ℕ} {a : Ω → ℝ}
    (ha_int : Integrable a μ)
    (ha_lim : Tendsto
      (fun m => ∫ ω, |blockAverage (fun i ω => f (X i ω)) (fun j : Fin (m + 1) => r + j) ω
        - a ω| ∂μ)
      atTop (𝓝 0)) :
    a =ᵐ[μ] μ[fun ω => f (X 0 ω) | tailProcess X] := by
  have hX_ae : ∀ i, AEMeasurable (X i) μ := fun i => (hX_meas i).aemeasurable
  have hY_L2 : ∀ i : ℕ, MemLp (fun ω => f (X i ω)) 2 μ := fun i =>
    ((hX.map_values hf hX_ae).identDistrib_coord (hf.comp_aemeasurable (hX_ae 0))
      (hf.comp_aemeasurable (hX_ae i))).memLp_snd hf_L2
  exact ae_eq_of_tendsto_integral_abs_sub
    (A := fun m => blockAverage (fun i ω => f (X i ω)) fun j : Fin (m + 1) => r + (j : ℕ))
    (fun m => (memLp_blockAverage _ fun j => hY_L2 (r + (j : ℕ))).integrable one_le_two)
    ha_int integrable_condExp ha_lim
    (hX.tendsto_integral_abs_blockAverage_sub_condExp_of_memLp hX_meas hf hf_L2 r)

end Probability

end TauCeti
