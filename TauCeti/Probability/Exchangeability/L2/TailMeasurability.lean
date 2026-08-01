/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Probability.Exchangeability.L2.CesaroConvergence
public import TauCeti.Probability.Process.Tail.Basic
import TauCeti.Probability.Exchangeability.Map
import TauCeti.MeasureTheory.Function.AEStronglyMeasurable
import TauCeti.MeasureTheory.Function.BoundedMemLp
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# The Cesàro limit of an observable of a contractable process is tail-measurable

Layer 3 of the Exchangeability roadmap reaches `weighted_sums_converge_L1_of_memLp`: every
fixed-start Cesàro window of a square-integrable observable of a contractable process converges in
`L¹` to a common limit. That limit is produced as an abstract `L¹` limit, so nothing about
*where it lives* comes for free.

`Contractable.exists_tailProcess_measurable_cesaroLimit_of_memLp` shows the limit has a
`tailProcess X`-measurable representative, with `…_cesaroLimit` the bounded-observable
corollary. It does **not** identify that limit with a conditional
expectation; that identification, and with it the Layer 3 milestones
`realObservables_determine_directing_measure` and `directing_measure_satisfies_requirements`, is
left to a complementary result. This file supplies the prerequisite those milestones need.

The argument does not use the reverse-martingale convergence theorem `tendsto_ae_condExp_iInf` of
Layer 4, which is what distinguishes this route from the martingale one. The window starting at `r`
is `tailFamily X r`-measurable; `L¹` convergence gives an a.e.-convergent subsequence, so the limit
is `AEStronglyMeasurable[tailFamily X r]` for **every** `r`, and `tailProcess X` is exactly the
infimum of that antitone family.

The roadmap maps `Exchangeability/Bridge/CesaroToCondExp.lean` in `cameronfreer/exchangeability`
(pin `e0532e59ceff23edab44dda9ab0655debbc9cc22`) as a Layer 3 source. This file is **not**
adapted from it: the
tail-measurability step is assembled from Tau Ceti's existing general helpers
`aestronglyMeasurable_of_tendsto_ae'` and `aestronglyMeasurable_iInf_of_antitone` (themselves
adapted from that repository's `Probability/SigmaAlgebraHelpers.lean`, and carrying attribution
there), rather than by porting a bridge file. The divergence is deliberate: separating tail
measurability from the conditional-expectation identification keeps this prerequisite independent
of the directing measure.
-/

public section

noncomputable section

open Filter MeasureTheory
open scoped ENNReal Topology

namespace TauCeti

namespace Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- **The Cesàro limit lives on the tail.** For a measurable observable `f` whose composite with a
single coordinate is square-integrable, the common `L¹` limit of the fixed-start Cesàro windows
supplied by `weighted_sums_converge_L1_of_memLp` has a **`tailProcess X`-measurable**
representative.

Each fixed-start window is `tailFamily X r`-measurable, so an a.e.-convergent subsequence exhibits
the limit as `AEStronglyMeasurable[tailFamily X r]` for every `r`; `tailProcess X` is the infimum
of that antitone family. -/
theorem Contractable.exists_tailProcess_measurable_cesaroLimit_of_memLp {μ : Measure Ω}
    [IsFiniteMeasure μ] {X : ℕ → Ω → α} (hX : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i)) {f : α → ℝ} (hf : Measurable f)
    (hf_L2 : MemLp (fun ω => f (X 0 ω)) 2 μ) :
    ∃ a : Ω → ℝ, Measurable[tailProcess X] a ∧ MemLp a 1 μ ∧
      ∀ r : ℕ,
        Tendsto
          (fun m => ∫ ω, |blockAverage (fun i ω => f (X i ω))
            (fun j : Fin (m + 1) => r + j) ω - a ω| ∂μ)
          atTop (𝓝 0) := by
  obtain ⟨a₀, -, ha₀_L1, ha₀_lim⟩ :=
    weighted_sums_converge_L1_of_memLp hX (fun i => (hX_meas i).aemeasurable) hf hf_L2
  have ha₀_int : Integrable a₀ μ := MemLp.integrable le_rfl ha₀_L1
  -- Contractability carries square-integrability from coordinate `0` to every coordinate.
  have hY : Contractable μ fun i ω => f (X i ω) :=
    Contractable.map_values hX hf fun i => (hX_meas i).aemeasurable
  have hint : ∀ i : ℕ, Integrable (fun ω => f (X i ω)) μ := fun i =>
    MemLp.integrable one_le_two
      ((hY.identDistrib_coord (hf.comp_aemeasurable (hX_meas 0).aemeasurable)
        (hf.comp_aemeasurable (hX_meas i).aemeasurable)).memLp_snd hf_L2)
  -- A window starting at `r` is a fixed multiple of a sum of coordinates from `r` onward.
  have hwin : ∀ (r m : ℕ), blockAverage (fun i ω => f (X i ω)) (fun j : Fin (m + 1) => r + j)
      = fun ω => ((m + 1 : ℕ) : ℝ)⁻¹ * ∑ j : Fin (m + 1), f (X (r + j) ω) := by
    intro r m
    funext ω
    simp [blockAverage_apply]
  have hg_meas : ∀ r m : ℕ, Measurable[tailFamily X r]
      (blockAverage (fun i ω => f (X i ω)) (fun j : Fin (m + 1) => r + j)) := by
    intro r m
    rw [hwin r m]
    have hterm : ∀ j : Fin (m + 1),
        Measurable[tailFamily X r] fun ω => f (X (r + (j : ℕ)) ω) := fun j =>
      hf.comp (measurable_tailFamily_of_le (Nat.le_add_right r (j : ℕ)))
    exact Measurable.const_mul (Finset.measurable_sum Finset.univ fun j _ => hterm j) _
  have hg_int : ∀ r m : ℕ, Integrable
      (blockAverage (fun i ω => f (X i ω)) (fun j : Fin (m + 1) => r + j)) μ := by
    intro r m
    rw [hwin r m]
    exact Integrable.const_mul
      (integrable_finsetSum (Finset.univ : Finset (Fin (m + 1)))
        fun (j : Fin (m + 1)) _ => hint (r + (j : ℕ))) _
  -- For each start index, an a.e.-convergent subsequence puts the limit on `tailFamily X r`.
  have haes : ∀ r : ℕ, AEStronglyMeasurable[tailFamily X r] a₀ μ := by
    intro r
    have hL1 : Tendsto (fun m => eLpNorm
        (blockAverage (fun i ω => f (X i ω)) (fun j : Fin (m + 1) => r + j) - a₀) 1 μ)
        atTop (𝓝 0) := by
      have heq : ∀ m : ℕ, eLpNorm
          (blockAverage (fun i ω => f (X i ω)) (fun j : Fin (m + 1) => r + j) - a₀) 1 μ
          = ENNReal.ofReal (∫ ω, |blockAverage (fun i ω => f (X i ω))
              (fun j : Fin (m + 1) => r + j) ω - a₀ ω| ∂μ) := by
        intro m
        rw [eLpNorm_one_eq_lintegral_enorm,
          ← ofReal_integral_norm_eq_lintegral_enorm ((hg_int r m).sub ha₀_int)]
        simp [Real.norm_eq_abs]
      simp_rw [heq]
      simpa [Function.comp_def] using (ENNReal.continuous_ofReal.tendsto 0).comp (ha₀_lim r)
    have hmeasure : TendstoInMeasure μ
        (fun m => blockAverage (fun i ω => f (X i ω)) (fun j : Fin (m + 1) => r + j)) atTop a₀ :=
      tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero
        (fun m => (hg_int r m).aestronglyMeasurable) ha₀_int.aestronglyMeasurable hL1
    obtain ⟨ns, -, hae⟩ := hmeasure.exists_seq_tendsto_ae
    exact TauCeti.MeasureTheory.aestronglyMeasurable_of_tendsto_ae' (m := tailFamily X r)
      (fun k => ((hg_meas r (ns k)).stronglyMeasurable).aestronglyMeasurable) hae
  have hiInf := TauCeti.MeasureTheory.aestronglyMeasurable_iInf_of_antitone
    (tailFamily_antitone X) a₀ haes
  rw [← tailProcess_eq_iInf_tailFamily] at hiInf
  refine ⟨hiInf.mk a₀, hiInf.stronglyMeasurable_mk.measurable, ?_, ?_⟩
  · exact ha₀_L1.ae_eq hiInf.ae_eq_mk
  · intro r
    refine (ha₀_lim r).congr fun m => integral_congr_ae ?_
    filter_upwards [hiInf.ae_eq_mk] with ω hω
    rw [hω]

/-- **Bounded-observable form.** A uniform bound gives square-integrability of the composite on a
finite measure space, so this is the direct entry point for bounded observables — matching the
shape in which `weighted_sums_converge_L1` states the underlying convergence. -/
theorem Contractable.exists_tailProcess_measurable_cesaroLimit {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → α} (hX : Contractable μ X) (hX_meas : ∀ i, Measurable (X i))
    {f : α → ℝ} (hf : Measurable f) (hf_bdd : ∃ C, ∀ x, ‖f x‖ ≤ C) :
    ∃ a : Ω → ℝ, Measurable[tailProcess X] a ∧ MemLp a 1 μ ∧
      ∀ r : ℕ,
        Tendsto
          (fun m => ∫ ω, |blockAverage (fun i ω => f (X i ω))
            (fun j : Fin (m + 1) => r + j) ω - a ω| ∂μ)
          atTop (𝓝 0) :=
  let ⟨C, hC⟩ := hf_bdd
  hX.exists_tailProcess_measurable_cesaroLimit_of_memLp hX_meas hf
    (memLp_comp_of_bound hf (hX_meas 0).aemeasurable C
      (Filter.Eventually.of_forall fun ω => hC (X 0 ω)) 2)

end Probability

end TauCeti
