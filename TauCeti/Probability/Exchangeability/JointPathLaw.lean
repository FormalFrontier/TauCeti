/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Exchangeability.FiniteMarginals
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# The joint law of a directing measure and a path

For a process `X : ℕ → Ω → α` carried along by a candidate directing measure
`ν : Ω → ProbabilityMeasure α`, `jointPathLaw μ X ν` is the law of the pair
`(ν ω, fun i => X i ω)` on `ProbabilityMeasure α × (ℕ → α)`.

## Main declarations

* `jointPathLaw` — the definition, with `jointPathLaw_def` its unfolding;
* `map_fst_jointPathLaw`, `map_snd_jointPathLaw` — the two marginals, `μ.map ν` and
  `pathLaw μ X`;
* `map_prefixProjPair_jointPathLaw` — the pushforward along the paired prefix projection.

Nothing here mentions conditional independence: these are facts about the law of a pair, and hold
for an arbitrary `ν`. The conditional statements that consume them — in particular the full-path
disintegration identifying this law with a mixture — live in
`Exchangeability/ConditionallyIID/PathDisintegration.lean`.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
  {μ : Measure Ω} {X : ℕ → Ω → α} {ν : Ω → ProbabilityMeasure α}

/-- The joint path law: the law of the directing measure together with the whole path. -/
def jointPathLaw (μ : Measure Ω) (X : ℕ → Ω → α) (ν : Ω → ProbabilityMeasure α) :
    Measure (ProbabilityMeasure α × (ℕ → α)) :=
  μ.map fun ω => (ν ω, fun i => X i ω)

/-- The definitional expansion of `jointPathLaw`: the pushforward of `μ` along
`ω ↦ (ν ω, fun i => X i ω)`. -/
@[simp]
theorem jointPathLaw_def (μ : Measure Ω) (X : ℕ → Ω → α) (ν : Ω → ProbabilityMeasure α) :
    jointPathLaw μ X ν = μ.map fun ω => (ν ω, fun i => X i ω) := (rfl)

/-- The first marginal of the joint path law is the law of the directing measure. -/
-- `@[grind =>]` rather than `@[simp]`: `jointPathLaw_def` is the registered simp normal form, so
-- simp rewrites this left-hand side away before the lemma could fire and `simpNF` rejects the
-- annotation; `grind` is not subject to that normalisation.
@[grind =>]
theorem map_fst_jointPathLaw (hX : ∀ i, AEMeasurable (X i) μ) :
    (jointPathLaw μ X ν).map Prod.fst = μ.map ν := by
  rw [jointPathLaw_def]
  exact Measure.fst_map_prodMk₀ (aemeasurable_pi_lambda _ hX)

/-- The second marginal of the joint path law is the law of the path. -/
@[grind =>]
theorem map_snd_jointPathLaw (hν : AEMeasurable ν μ) :
    (jointPathLaw μ X ν).map Prod.snd = pathLaw μ X := by
  rw [jointPathLaw_def, pathLaw_def]
  exact Measure.snd_map_prodMk₀ hν

/-- The prefix pushforward of the joint path law is the joint block law of the first `n`
coordinates. -/
theorem map_prefixProjPair_jointPathLaw (hX : ∀ i, AEMeasurable (X i) μ) (hν : AEMeasurable ν μ)
    (n : ℕ) :
    (jointPathLaw μ X ν).map (prefixProjPair (ProbabilityMeasure α) α n)
      = μ.map fun ω => (ν ω, fun i : Fin n => X i ω) := by
  have hpath : AEMeasurable (fun ω => (ν ω, fun i => X i ω) :
      Ω → ProbabilityMeasure α × (ℕ → α)) μ :=
    hν.prodMk (aemeasurable_pi_lambda _ hX)
  rw [jointPathLaw_def,
    AEMeasurable.map_map_of_aemeasurable
      (measurable_prefixProjPair (ProbabilityMeasure α) α n).aemeasurable hpath]
  simp only [Function.comp_def, prefixProjPair_apply]

end Probability

end TauCeti

end

end
