/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Probability.Exchangeability.L2.Cesaro.Convergence
public import TauCeti.Probability.Process.Tail.Basic
import TauCeti.MeasureTheory.Function.AEStronglyMeasurable
import TauCeti.MeasureTheory.Function.BoundedMemLp
import TauCeti.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# The Cesàro limit of an observable of a contractable process is tail-measurable

Layer 3 of the Exchangeability roadmap reaches `weighted_sums_converge_L1_of_memLp`: the block
averages of a square-integrable observable of a contractable process converge in `L¹` to a common
limit, along every eventually-injective selection — fixed-start windows and disjoint windows
alike. That limit is produced as an abstract `L¹` limit, so nothing about
*where it lives* comes for free.

`Contractable.exists_tailProcess_measurable_cesaro_limit_of_memLp` shows the limit has a
`tailProcess X`-measurable representative, with `…_cesaro_limit` the bounded-observable corollary.

This file's responsibility is **measurability of the limit**, deliberately separate from
identifying *what* the limit is: `Exchangeability.L2.Cesaro.ToCondExp` identifies it with
`μ[f ∘ X 0 | tailProcess X]`. Keeping the two apart is what lets the measurability argument avoid
the reverse-martingale theorem entirely.

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

omit [MeasurableSpace Ω] in
/-- **A block average over tail indices is tail-measurable.** If every index of the family `k` is at
least `r`, each coordinate `f ∘ X (k j)` is `tailFamily X r`-measurable, hence so is their average.
Only measurability of `f` is needed: no measure, and no contractability of `X`.

The indices need not be consecutive — `blockAverage` averages over an arbitrary `k : Fin n → ℕ`,
and only `r ≤ k j` is used. -/
private theorem measurable_tailFamily_blockAverage {X : ℕ → Ω → α} {f : α → ℝ}
    (hf : Measurable f) {r n : ℕ} {k : Fin n → ℕ} (hk : ∀ j, r ≤ k j) :
    Measurable[tailFamily X r] (blockAverage (fun i ω => f (X i ω)) k) := by
  have hterm : ∀ j : Fin n,
      Measurable[tailFamily X r] fun ω => f (X (k j) ω) := fun j =>
    hf.comp (measurable_tailFamily_of_le (hk j))
  have happly : (blockAverage (fun i ω => f (X i ω)) k)
      = fun ω => (n : ℝ)⁻¹ * ∑ j : Fin n, f (X (k j) ω) :=
    funext fun ω => blockAverage_apply _ _
  rw [happly]
  exact (Finset.measurable_fun_sum Finset.univ fun j _ => hterm j).const_mul _

/-- **The Cesàro limit lives on the tail.** For a measurable observable `f` whose composite with a
single coordinate is square-integrable, the common `L¹` limit of the moving injective block
averages supplied by `weighted_sums_converge_L1_of_memLp` has a **`tailProcess X`-measurable**
representative.

The limit is the same function for every selection, so the conclusion carries the general form
through; fixed starts are only used *inside* the proof, where placing the limit on `tailFamily X r`
needs a window that begins at `r`. -/
theorem Contractable.exists_tailProcess_measurable_cesaro_limit_of_memLp {μ : Measure Ω}
    [IsFiniteMeasure μ] {X : ℕ → Ω → α} (hX : Contractable μ X)
    (hX_ae : ∀ i, AEMeasurable (X i) μ) {f : α → ℝ} (hf : Measurable f)
    (hf_L2 : MemLp (fun ω => f (X 0 ω)) 2 μ) :
    ∃ a : Ω → ℝ, Measurable[tailProcess X] a ∧ MemLp a 1 μ ∧
      ∀ k : ∀ n : ℕ, Fin (n + 1) → ℕ, (∀ᶠ n in atTop, Function.Injective (k n)) →
        Tendsto
          (fun m => ∫ ω, |blockAverage (fun i ω => f (X i ω)) (k m) ω - a ω| ∂μ)
          atTop (𝓝 0) := by
  obtain ⟨a₀, -, ha₀_L1, ha₀_lim'⟩ :=
    weighted_sums_converge_L1_of_memLp hX hX_ae hf hf_L2
  have ha₀_lim : ∀ r : ℕ, Tendsto
      (fun m => ∫ ω, |blockAverage (fun i ω => f (X i ω))
        (fun j : Fin (m + 1) => r + (j : ℕ)) ω - a₀ ω| ∂μ) atTop (𝓝 0) := fun r =>
    ha₀_lim' (fun n j => r + (j : ℕ))
      (Eventually.of_forall fun _ => (add_right_injective r).comp Fin.val_injective)
  have ha₀_int : Integrable a₀ μ := MemLp.integrable le_rfl ha₀_L1
  -- Contractability carries square-integrability from coordinate `0` to every coordinate.
  have hY_L2 : ∀ i : ℕ, MemLp (fun ω => f (X i ω)) 2 μ := hX.memLp_comp hX_ae hf hf_L2
  have hg_int : ∀ r m : ℕ, Integrable
      (blockAverage (fun i ω => f (X i ω)) (fun j : Fin (m + 1) => r + j)) μ := fun r m =>
    MemLp.integrable one_le_two
      (memLp_blockAverage _ fun j => hY_L2 (r + (j : ℕ)))
  -- For each start index, an a.e.-convergent subsequence puts the limit on `tailFamily X r`.
  have haes : ∀ r : ℕ, AEStronglyMeasurable[tailFamily X r] a₀ μ := by
    intro r
    have hL1 : Tendsto (fun m => eLpNorm
        (blockAverage (fun i ω => f (X i ω)) (fun j : Fin (m + 1) => r + j) - a₀) 1 μ)
        atTop (𝓝 0) :=
      TauCeti.MeasureTheory.tendsto_eLpNorm_one_of_tendsto_integral_norm_sub (hg_int r) ha₀_int
        (by simpa [Real.norm_eq_abs] using ha₀_lim r)
    have hmeasure : TendstoInMeasure μ
        (fun m => blockAverage (fun i ω => f (X i ω)) (fun j : Fin (m + 1) => r + j)) atTop a₀ :=
      tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero
        (fun m => (hg_int r m).aestronglyMeasurable) ha₀_int.aestronglyMeasurable hL1
    obtain ⟨ns, -, hae⟩ := hmeasure.exists_seq_tendsto_ae
    exact TauCeti.MeasureTheory.aestronglyMeasurable_of_tendsto_ae' (m := tailFamily X r)
      (fun k => (measurable_tailFamily_blockAverage hf
        fun j => Nat.le_add_right r (j : ℕ)).stronglyMeasurable.aestronglyMeasurable) hae
  have hiInf := TauCeti.MeasureTheory.aestronglyMeasurable_iInf_of_antitone
    (tailFamily_antitone X) a₀ haes
  rw [← tailProcess_eq_iInf_tailFamily] at hiInf
  refine ⟨hiInf.mk a₀, hiInf.stronglyMeasurable_mk.measurable, ?_, ?_⟩
  · exact ha₀_L1.ae_eq hiInf.ae_eq_mk
  · intro k hk
    refine (ha₀_lim' k hk).congr fun m => integral_congr_ae ?_
    filter_upwards [hiInf.ae_eq_mk] with ω hω
    rw [hω]

/-- **Bounded-observable form.** A uniform bound gives square-integrability of the composite on a
finite measure space, so this is the direct entry point for bounded observables — matching the
shape in which `weighted_sums_converge_L1` states the underlying convergence. -/
theorem Contractable.exists_tailProcess_measurable_cesaro_limit {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → α} (hX : Contractable μ X) (hX_ae : ∀ i, AEMeasurable (X i) μ)
    {f : α → ℝ} (hf : Measurable f) (hf_bdd : ∃ C, ∀ x, ‖f x‖ ≤ C) :
    ∃ a : Ω → ℝ, Measurable[tailProcess X] a ∧ MemLp a 1 μ ∧
      ∀ k : ∀ n : ℕ, Fin (n + 1) → ℕ, (∀ᶠ n in atTop, Function.Injective (k n)) →
        Tendsto
          (fun m => ∫ ω, |blockAverage (fun i ω => f (X i ω)) (k m) ω - a ω| ∂μ)
          atTop (𝓝 0) :=
  let ⟨C, hC⟩ := hf_bdd
  hX.exists_tailProcess_measurable_cesaro_limit_of_memLp hX_ae hf
    (memLp_comp_of_bound hf (hX_ae 0) C
      (Filter.Eventually.of_forall fun ω => hC (X 0 ω)) 2)

end Probability

end TauCeti
