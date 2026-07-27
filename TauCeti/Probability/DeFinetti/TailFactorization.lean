/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

-- Public: the modules whose symbols appear in the exported statement.
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import TauCeti.Probability.Process.Tail.Basic
public import TauCeti.Probability.Exchangeability.Cylinder
public import TauCeti.Probability.Exchangeability.Contractability
-- Non-public: used only inside the proof, absent from the exported statement —
-- `condExp_blockIndicatorProd_future_ae_eq_prod` (finite-level factorization) and
-- `tendsto_ae_condExp_iInf` (Lévy's downward theorem).
import TauCeti.Probability.DeFinetti.FutureFactorization
import TauCeti.Probability.Martingale.Convergence

/-!
# Tail-level factorization for the de Finetti martingale route

For a contractable process `X`, this file factors the conditional expectation of a prefix indicator
product given the **tail** σ-algebra `tailProcess X` into a product of single-coordinate tail
conditional expectations — the tail-level input to the de Finetti martingale route.

## Main result

* `condExp_blockIndicatorProd_tailProcess_ae_eq_prod` — for a contractable process, the conditional
  expectation of the length-`r` prefix indicator product given the tail σ-algebra factors as the
  product of the single-coordinate (all replaced by `X 0`) tail conditional expectations.

Adapted from `cameronfreer/exchangeability`
(`DeFinetti/ViaMartingale/Factorization.lean`: `tail_factorization_from_future`).
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped MeasureTheory Topology

namespace TauCeti

namespace Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- **Tail-level factorization.**

For a contractable process, the conditional expectation of the length-`r` prefix indicator product
given the tail σ-algebra `tailProcess X` factors:
```
μ[∏ i<r 𝟙_{X i ∈ C i} | 𝒯_X] = ∏ i<r μ[𝟙_{X 0 ∈ C i} | 𝒯_X]   a.e.
``` -/
lemma condExp_blockIndicatorProd_tailProcess_ae_eq_prod
    [StandardBorelSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    (X : ℕ → Ω → α) (hX : Contractable μ X) (hX_meas : ∀ n, Measurable (X n))
    (r : ℕ) (C : Fin r → Set α) (hC : ∀ i, MeasurableSet (C i)) :
    μ[blockIndicatorProd X (fun i : Fin r => (i : ℕ)) C | tailProcess X]
      =ᵐ[μ]
    (fun ω => ∏ i : Fin r,
      μ[Set.indicator (C i) (fun _ => (1 : ℝ)) ∘ X 0 | tailProcess X] ω) := by
  classical
  -- Reverse-martingale convergence: `μ[f | tailFamily X (m+1)] → μ[f | tailProcess X]` a.e.
  have hconv : ∀ f : Ω → ℝ, ∀ᵐ ω ∂μ,
      Tendsto (fun m => μ[f | tailFamily X (m + 1)] ω) atTop
        (𝓝 (μ[f | tailProcess X] ω)) := by
    intro f
    -- `tendsto_ae_condExp_iInf` takes the index-0 bound `𝔽 0 ≤ m₀`; antitonicity supplies the rest.
    have h := tendsto_ae_condExp_iInf (μ := μ) (tailFamily_antitone X)
      (tailFamily_le_ambient 0 fun k _ => hX_meas k) f
    rw [← tailProcess_eq_iInf_tailFamily X] at h
    filter_upwards [h] with ω hω using hω.comp (tendsto_add_atTop_nat 1)
  -- LHS converges to the tail conditional expectation of the block.
  have h_lhs := hconv (blockIndicatorProd X (fun i : Fin r => (i : ℕ)) C)
  -- RHS: the finite product of the convergent single-coordinate factors converges.
  have h_rhs : ∀ᵐ ω ∂μ,
      Tendsto (fun m => ∏ i : Fin r,
          μ[Set.indicator (C i) (fun _ => (1 : ℝ)) ∘ X 0 | tailFamily X (m + 1)] ω) atTop
        (𝓝 (∏ i : Fin r,
          μ[Set.indicator (C i) (fun _ => (1 : ℝ)) ∘ X 0 | tailProcess X] ω)) := by
    have hfac : ∀ᵐ ω ∂μ, ∀ i : Fin r,
        Tendsto (fun m => μ[Set.indicator (C i) (fun _ => (1 : ℝ)) ∘ X 0
            | tailFamily X (m + 1)] ω) atTop
          (𝓝 (μ[Set.indicator (C i) (fun _ => (1 : ℝ)) ∘ X 0 | tailProcess X] ω)) :=
      ae_all_iff.mpr fun i => hconv _
    filter_upwards [hfac] with ω hω using tendsto_finsetProd _ fun i _ => hω i
  -- Equality of the two sequences at each finite level `m ≥ r`.
  have h_fact : ∀ᵐ ω ∂μ, ∀ m, r ≤ m →
      μ[blockIndicatorProd X (fun i : Fin r => (i : ℕ)) C | tailFamily X (m + 1)] ω
        = ∏ i : Fin r,
            μ[Set.indicator (C i) (fun _ => (1 : ℝ)) ∘ X 0 | tailFamily X (m + 1)] ω := by
    rw [ae_all_iff]
    intro m
    by_cases hm : r ≤ m
    · filter_upwards [condExp_blockIndicatorProd_future_ae_eq_prod X hX hX_meas m r C hC (by omega)]
        with ω hω _ using hω
    · exact ae_of_all _ fun ω h => absurd h hm
  filter_upwards [h_lhs, h_rhs, h_fact] with ω hl hr hf
  refine tendsto_nhds_unique hl (hr.congr' ?_)
  filter_upwards [eventually_ge_atTop r] with m hm using (hf m hm).symm

end Probability

end TauCeti
