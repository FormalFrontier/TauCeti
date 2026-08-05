/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Probability.Martingale.Convergence

/-!
# Lévy's downward theorem on an eventually constant filtration

This file is the Exchangeability-roadmap worked example
(`TauCetiRoadmap/Exchangeability/README.md`, "Worked examples"): *the Lévy downward theorem
specializes correctly to an eventually constant decreasing filtration*. It is a consistency
test of the flagship Layer-4 result `MeasureTheory.tendsto_ae_condExp_iInf`, not a de Finetti
example.

Fix an antitone filtration `𝔽 : ℕ → MeasurableSpace Ω` that is constant from some index `N`
on, `𝔽 n = 𝔽 N` for `n ≥ N`. Two independent computations must agree:

* **Elementary.** The sequence `n ↦ μ[f | 𝔽 n]` is literally constant past `N`
  (`condExp_eq_of_eventually_const`), so it converges — everywhere, no integrability or
  finiteness needed — to the value `μ[f | 𝔽 N]` it already sits at
  (`tendsto_condExp_of_eventually_const`).
* **General.** The intersection `⨅ n, 𝔽 n` collapses to `𝔽 N`
  (`iInf_measurableSpace_eq_of_antitone_of_eventually_const`), so the Lévy downward limit
  `μ[f | ⨅ n, 𝔽 n]` is `μ[f | 𝔽 N]` (`condExp_iInf_eq_of_eventually_const`).

The capstone `tendsto_ae_condExp_of_eventually_const` runs the general theorem and
rewrites its limit through the intersection collapse, recovering exactly the elementary limit:
the two routes agree, which is what "specializes correctly" means.

No material from `cameronfreer/exchangeability` is used; this is a Tau-Ceti-local check of the
flagship theorem stated in `TauCeti.Probability.Martingale.Convergence`.
-/

public section

noncomputable section

open MeasureTheory Filter

open scoped Topology

namespace TauCeti

namespace Probability

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {𝔽 : ℕ → MeasurableSpace Ω}

/-- The intersection of an antitone filtration that is constant from index `N` on collapses to
the stabilized σ-algebra `𝔽 N`. This is the order fact behind the Lévy-downward specialization. -/
theorem iInf_measurableSpace_eq_of_antitone_of_eventually_const {Ω : Type*}
    {𝔽 : ℕ → MeasurableSpace Ω} (h_anti : Antitone 𝔽) {N : ℕ} (h_const : ∀ n, N ≤ n → 𝔽 n = 𝔽 N) :
    ⨅ n, 𝔽 n = 𝔽 N := by
  refine le_antisymm (iInf_le 𝔽 N) (le_iInf fun n => ?_)
  rcases le_total N n with h | h
  · exact (h_const n h).ge
  · exact h_anti h

/-- Past the stabilization index the conditional expectations are literally equal: for `N ≤ n`
the σ-algebras `𝔽 n` and `𝔽 N` coincide, so `μ[f | 𝔽 n]` and `μ[f | 𝔽 N]` are the same term. -/
theorem condExp_eq_of_eventually_const {N : ℕ}
    (h_const : ∀ n, N ≤ n → 𝔽 n = 𝔽 N) (f : Ω → ℝ) {n : ℕ} (hn : N ≤ n) :
    μ[f | 𝔽 n] = μ[f | 𝔽 N] := by
  rw [h_const n hn]

/-- **Elementary convergence.** Along a filtration constant from index `N` on, the conditional
expectations `μ[f | 𝔽 n]` reach `μ[f | 𝔽 N]` exactly and stay there, so they converge to it at
every point. No integrability of `f` or finiteness of `μ` is needed: the sequence is eventually
constant. -/
theorem tendsto_condExp_of_eventually_const {N : ℕ}
    (h_const : ∀ n, N ≤ n → 𝔽 n = 𝔽 N) (f : Ω → ℝ) (ω : Ω) :
    Tendsto (fun n => μ[f | 𝔽 n] ω) atTop (𝓝 (μ[f | 𝔽 N] ω)) :=
  tendsto_atTop_of_eventually_const (i₀ := N)
    fun _ hn => congrFun (condExp_eq_of_eventually_const h_const f hn) ω

/-- **The Lévy downward limit collapses.** For an antitone filtration constant from index `N`
on, the reverse-martingale limit `μ[f | ⨅ n, 𝔽 n]` produced by `tendsto_ae_condExp_iInf` is the
conditional expectation onto the stabilized σ-algebra `𝔽 N`. -/
theorem condExp_iInf_eq_of_eventually_const
    (h_anti : Antitone 𝔽) {N : ℕ} (h_const : ∀ n, N ≤ n → 𝔽 n = 𝔽 N) (f : Ω → ℝ) :
    μ[f | ⨅ n, 𝔽 n] = μ[f | 𝔽 N] := by
  rw [iInf_measurableSpace_eq_of_antitone_of_eventually_const h_anti h_const]

/-- **Lévy's downward theorem specializes correctly to an eventually constant filtration.**

Run the flagship `MeasureTheory.tendsto_ae_condExp_iInf` on an antitone filtration that is
constant from index `N` on, then collapse its limit through
`condExp_iInf_eq_of_eventually_const`. The a.e. limit it delivers is `μ[f | 𝔽 N]` — exactly the
value the sequence already reaches by the elementary
`tendsto_condExp_of_eventually_const`. The general and elementary computations agree. -/
theorem tendsto_ae_condExp_of_eventually_const [IsFiniteMeasure μ]
    (h_anti : Antitone 𝔽) (h_le0 : 𝔽 0 ≤ (inferInstance : MeasurableSpace Ω))
    {N : ℕ} (h_const : ∀ n, N ≤ n → 𝔽 n = 𝔽 N) (f : Ω → ℝ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => μ[f | 𝔽 n] ω) atTop (𝓝 (μ[f | 𝔽 N] ω)) := by
  have h := tendsto_ae_condExp_iInf (μ := μ) h_anti h_le0 f
  rwa [condExp_iInf_eq_of_eventually_const h_anti h_const f] at h

end Probability

end TauCeti
