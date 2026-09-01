/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Exchangeability.Recurrence.Excursion
-- Non-public: supplies the discrete-measurability instances the change of variables needs.
import TauCeti.Probability.Exchangeability.MixedIID.Mixture

/-!
# Reconstructing a recurrent path from its excursions

A recurrent process that starts at `a₀` returns to it infinitely often, so it is spelled out by its
excursions and nothing else: reading the excursions off a path and concatenating them back are
mutually inverse.  This file turns that bijection into an identity of laws,

```text
pathLaw μ X = (pathLaw of the excursion process).map (pathOfExcursions a₀)
```

and nothing more.  It is deliberately independent of de Finetti: the reconstruction is a change of
variables along a measurable bijection, and holds whether or not the excursion law is a mixture.
The representation theorem that identifies that law as a mixture is in `Recurrence.Representation`,
which is the only file in this subtree that reaches the de Finetti summit.

## Main results

* `TauCeti.Probability.measurable_pathOfExcursions` — concatenation is measurable;
* `TauCeti.Probability.pathLaw_eq_map_pathOfExcursions` and its `Recurrent` form — the path law is
  the pushforward of the excursion path law along it.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
  {μ : Measure Ω} {X : ℕ → Ω → α} {a₀ : α}

/-- **Concatenating a sequence of excursions is measurable.** Each coordinate of the concatenated
sequence depends on finitely many excursions, and over a countable discrete state space the finite
words form a countable discrete space, on which every map is measurable. -/
theorem measurable_pathOfExcursions [Countable α] [MeasurableSingletonClass α] (a₀ : α) :
    Measurable (pathOfExcursions a₀ : (ℕ → List α) → ℕ → α) := by
  refine measurable_pi_lambda _ fun i => ?_
  have hfac : (fun b : ℕ → List α => pathOfExcursions a₀ b i) =
      (fun v : Fin (i + 1) → List α => loopPathAt a₀ (List.ofFn v) i) ∘
        fun (b : ℕ → List α) (j : Fin (i + 1)) => b j.val := by
    funext b
    have hi : i ≤ loopSteps ((List.range (i + 1)).map b) := by
      have hle := length_le_loopSteps ((List.range (i + 1)).map b)
      simp only [List.length_map, List.length_range] at hle
      omega
    rw [Function.comp_apply, pathOfExcursions_eq_loopPathAt a₀ b hi]
    congr 1
    refine List.ext_getElem (by simp) fun j hj hj' => ?_
    rw [List.getElem_map, List.getElem_range, List.getElem_ofFn]
  rw [hfac]
  exact Measurable.of_discrete.comp (measurable_pi_lambda _ fun j => measurable_pi_apply _)

/-! ## The path law of a recurrent process -/

variable {μ : Measure Ω} {X : ℕ → Ω → α} {a₀ : α}

/-- **The path law of a process returning infinitely often to `a₀` is the image of its excursion
law.** Almost every sample path starts at and returns infinitely often to `a₀`, so concatenating
its excursions recovers it. -/
theorem pathLaw_eq_map_pathOfExcursions [Countable α] [MeasurableSingletonClass α]
    (hX : ∀ i, AEMeasurable (X i) μ) (hreturns : ∀ᵐ ω ∂μ, {n | X n ω = a₀}.Infinite)
    (h0 : ∀ᵐ ω ∂μ, X 0 ω = a₀) :
    pathLaw μ X = (pathLaw μ (excursionProcess X a₀)).map (pathOfExcursions a₀) := by
  have hΦ : AEMeasurable (fun ω k => excursionProcess X a₀ k ω) μ :=
    aemeasurable_pi_lambda _ fun k => aemeasurable_excursionProcess hX a₀ k
  have hae : (pathOfExcursions a₀ ∘ fun ω k => excursionProcess X a₀ k ω) =ᵐ[μ]
      fun ω i => X i ω := by
    filter_upwards [h0, hreturns] with ω hω0 hωinf
    simpa [Function.comp_def] using pathOfExcursions_excursion hωinf hω0
  rw [pathLaw_def, pathLaw_def,
    AEMeasurable.map_map_of_aemeasurable (measurable_pathOfExcursions a₀).aemeasurable hΦ,
    Measure.map_congr hae]

/-- **The path law of a recurrent process started at `a₀` is the image of its excursion law.** -/
theorem Recurrent.pathLaw_eq_map_pathOfExcursions [Countable α] [MeasurableSingletonClass α]
    (hrec : Recurrent μ X) (hX : ∀ i, AEMeasurable (X i) μ) (h0 : ∀ᵐ ω ∂μ, X 0 ω = a₀) :
    pathLaw μ X = (pathLaw μ (excursionProcess X a₀)).map (pathOfExcursions a₀) := by
  apply TauCeti.Probability.pathLaw_eq_map_pathOfExcursions hX _ h0
  filter_upwards [h0, hrec.ae_infinite_setOf_eq] with ω hω0 hωinf
  have h := hωinf 0
  rwa [hω0] at h

/-! ## Excursion laws avoid the base state -/


end Probability

end TauCeti
