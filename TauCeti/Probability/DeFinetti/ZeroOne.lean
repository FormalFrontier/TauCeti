/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

-- Public: the law-level zero-one criterion for a product law, which this file reads for a process.
public import TauCeti.Probability.Exchangeability.PathSpace.Law.ZeroOne
-- Public: the constant-witness dictionary, in which the conclusion "i.i.d." is stated.
public import TauCeti.Probability.Exchangeability.MixedIID.Const
-- Non-public: the process-to-path-law bridges, used only inside proofs.
import TauCeti.Probability.Exchangeability.PathSpace.Law.Bridge

/-!
# An exchangeable process with a trivial tail is i.i.d.

De Finetti's theorem makes an exchangeable process conditionally i.i.d. given its directing
measure, and that directing measure is measurable for the tail σ-algebra `tailProcess X`. So a
process whose tail σ-algebra is `μ`-trivial has an almost surely determined directing measure, and
the mixture collapses: the process is plainly i.i.d.

This is the process-level companion of the law-level `infinitePi_of_pathTail_trivial`, and the
zero-one criterion a proof of independence can aim at when independence itself is hard to see but
the tail is visibly trivial. That is the situation for the diagonal of a dissociated exchangeable
array, whose entries dissociation makes only *pairwise* independent, and which
`JointlyDissociated.iIndepFun_arrayDiag` upgrades to i.i.d. through this criterion.

The hypothesis is triviality of the **tail**, not of the larger exchangeable σ-algebra: the tail is
what pulls back from a path event to a process event (`comap_pathTail_le_tailProcess`), whereas an
exchangeable event of the path law has no such description in terms of the process.

## Main results

* `TauCeti.Probability.exists_mixedIIDWith_const_of_exchangeable_of_tailProcess_trivial` — the
  criterion, in the form naming the common law;
* `TauCeti.Probability.iIndepFun_of_exchangeable_of_tailProcess_trivial` — its independence form.

## References

* O. Kallenberg, *Probabilistic Symmetries and Invariance Principles*, Springer, 2005, Chapter 1.
* Roadmap: `TauCetiRoadmap/Exchangeability/README.md`, Layer 6, the zero-one interface for
  exchangeable laws.

No material is adapted from `cameronfreer/exchangeability`, which carries no zero-one criterion.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace TauCeti

namespace Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- **An exchangeable process with a trivial tail σ-algebra is i.i.d.**, and its common law is
named: there is a probability measure `P` on the state space with `fun _ => P` a mixing
representative, so the coordinates are independent with common law `P`
(`mixedIIDWith_const_iff_iIndepFun_and_map_eq`).

Triviality of the tail is exactly what makes the de Finetti mixture degenerate: the canonical
directing measure is tail-measurable, so a trivial tail leaves it no room to vary. -/
theorem exists_mixedIIDWith_const_of_exchangeable_of_tailProcess_trivial [StandardBorelSpace α]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : ℕ → Ω → α}
    (hX_meas : ∀ n, AEMeasurable (X n) μ)
    (hX : Exchangeable μ X)
    (htriv : ∀ s, MeasurableSet[tailProcess X] s → μ s = 0 ∨ μ s = 1) :
    ∃ P : ProbabilityMeasure α, MixedIIDWith μ X fun _ => P := by
  have hφ : AEMeasurable (fun ω => fun i => X i ω : Ω → ℕ → α) μ :=
    aemeasurable_pi_lambda _ hX_meas
  have hprob : IsProbabilityMeasure (pathLaw μ X) := by
    rw [pathLaw_def]
    exact Measure.isProbabilityMeasure_map hφ
  have hlaw : ExchangeableLaw (pathLaw μ X) :=
    (exchangeable_iff_exchangeableLaw_pathLaw hX_meas).mp hX
  have hpathTail : ∀ s, MeasurableSet[pathTail α] s → pathLaw μ X s = 0 ∨ pathLaw μ X s = 1 := by
    intro s hs
    have hs' : MeasurableSet s :=
      tailProcess_le_ambient 0 (fun k _ => measurable_pi_apply k) s hs
    have hpull : MeasurableSet[tailProcess X] ((fun ω i => X i ω) ⁻¹' s) :=
      comap_pathTail_le_tailProcess X _ ⟨s, hs, rfl⟩
    rw [pathLaw_def, Measure.map_apply_of_aemeasurable hφ hs']
    exact htriv _ hpull
  obtain ⟨P, hP⟩ := infinitePi_of_pathTail_trivial hlaw hpathTail
  exact ⟨P, mixedIIDWith_const_of_pathLaw_eq_infinitePi hX_meas hP⟩

/-- **An exchangeable process with a trivial tail σ-algebra has independent coordinates.** The
identical-distribution half of "i.i.d." is available alongside it, through
`exists_mixedIIDWith_const_of_exchangeable_of_tailProcess_trivial` and
`MixedIIDWith.map_eq_of_const`. -/
theorem iIndepFun_of_exchangeable_of_tailProcess_trivial [StandardBorelSpace α]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : ℕ → Ω → α}
    (hX_meas : ∀ n, AEMeasurable (X n) μ)
    (hX : Exchangeable μ X)
    (htriv : ∀ s, MeasurableSet[tailProcess X] s → μ s = 0 ∨ μ s = 1) :
    iIndepFun X μ := by
  obtain ⟨P, hP⟩ :=
    exists_mixedIIDWith_const_of_exchangeable_of_tailProcess_trivial hX_meas hX htriv
  exact hP.iIndepFun_of_const

end Probability

end TauCeti

end

end
