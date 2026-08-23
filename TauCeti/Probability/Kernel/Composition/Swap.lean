/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Kernel.Composition.MeasureCompProd
public import Mathlib.Probability.Kernel.Disintegration.StandardBorel

/-!
# The composition-product of a measure and a kernel, in the reversed coordinate order

Mathlib's `μ ⊗ₘ κ` records the joint law of "draw `q` from `μ`, then `p` from `κ q`" as a measure
on `V × Ω`, the base coordinate first. `TauCeti.swapCompProd μ κ` is that same joint law written
on `Ω × V`, the kernel coordinate first, which is the order some product semigroups come in.

Everything Mathlib proves about `⊗ₘ` transports across the swap, and this file records the
transported statements that are awkward to reconstruct at each use: the mass of a measurable
rectangle, the integral of a general function, the second marginal of a Markov composition, and
— for a nonempty standard Borel kernel target — the converse, that *every* finite measure on
`Ω × V` is such a composition over its second marginal.

## Main declarations

* `TauCeti.swapCompProd`: the measure `(μ ⊗ₘ κ).map Prod.swap` on `Ω × V`, with
  `TauCeti.swapCompProd_prod` and `TauCeti.lintegral_swapCompProd` evaluating it.
* `TauCeti.exists_eq_swapCompProd`: every finite measure whose first coordinate is nonempty
  standard Borel is a `TauCeti.swapCompProd` over its second marginal, by disintegration.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

open scoped ENNReal

namespace TauCeti

variable {V Ω : Type*} [MeasurableSpace V] [MeasurableSpace Ω]

/-- The measure on `Ω × V` assembled from a measure `μ` on `V` and a kernel `κ` from `V` to
`Ω`: draw the `V` coordinate from `μ`, then the `Ω` coordinate from `κ`, and swap the pair. -/
def swapCompProd (μ : Measure V) (κ : Kernel V Ω) : Measure (Ω × V) :=
  (μ ⊗ₘ κ).map Prod.swap

/-- The assembled measure is the swap-map of Mathlib's composition-product measure. -/
theorem swapCompProd_def (μ : Measure V) (κ : Kernel V Ω) :
    swapCompProd μ κ = (μ ⊗ₘ κ).map Prod.swap :=
  (rfl)

instance isFiniteMeasure_swapCompProd (μ : Measure V) [IsFiniteMeasure μ]
    (κ : Kernel V Ω) [IsFiniteKernel κ] : IsFiniteMeasure (swapCompProd μ κ) := by
  rw [swapCompProd]
  infer_instance

/-- The mass an assembled measure gives to a measurable rectangle: integrate the kernel mass of
the first-coordinate side over the second-coordinate side. -/
theorem swapCompProd_prod (μ : Measure V) [SFinite μ] (κ : Kernel V Ω)
    [IsSFiniteKernel κ] {A : Set Ω} (hA : MeasurableSet A) {B : Set V} (hB : MeasurableSet B) :
    swapCompProd μ κ (A ×ˢ B) = ∫⁻ q in B, κ q A ∂μ := by
  rw [swapCompProd, Measure.map_apply measurable_swap (hA.prod hB),
    Set.preimage_swap_prod, Measure.compProd_apply_prod hB hA]

/-- Integrating against an assembled measure means first integrating over the kernel fibre and
then over the base measure. -/
theorem lintegral_swapCompProd (μ : Measure V) [SFinite μ] (κ : Kernel V Ω)
    [IsSFiniteKernel κ] {f : Ω × V → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ y, f y ∂(swapCompProd μ κ) = ∫⁻ q, ∫⁻ p, f (p, q) ∂(κ q) ∂μ := by
  have hf_swap : Measurable (fun z : V × Ω => f z.swap) := hf.comp measurable_swap
  rw [swapCompProd, lintegral_map hf measurable_swap,
    Measure.lintegral_compProd hf_swap]
  simp

/-- The second marginal of an assembled measure is the measure it was assembled from. -/
@[simp]
theorem snd_swapCompProd (μ : Measure V) [SFinite μ] (κ : Kernel V Ω) [IsMarkovKernel κ] :
    (swapCompProd μ κ).snd = μ := by
  rw [swapCompProd, Measure.snd_map_swap, Measure.fst_compProd]

/-- **Every finite measure on `Ω × V` is assembled from its second marginal and a Markov
kernel.** The kernel is the conditional distribution of the first coordinate given the second,
which exists because `Ω` is a nonempty standard Borel space. -/
theorem exists_eq_swapCompProd [StandardBorelSpace Ω] [Nonempty Ω]
    (μ : Measure (Ω × V)) [IsFiniteMeasure μ] :
    ∃ κ : Kernel V Ω, IsMarkovKernel κ ∧ μ = swapCompProd μ.snd κ := by
  set ρ : Measure (V × Ω) := μ.map Prod.swap with hρ
  have hfin : IsFiniteMeasure ρ := by rw [hρ]; infer_instance
  refine ⟨ρ.condKernel, inferInstance, ?_⟩
  rw [swapCompProd, ← Measure.fst_map_swap (ρ := μ), ← hρ, Measure.disintegrate ρ, hρ,
    Measure.map_map measurable_swap measurable_swap, Prod.swap_swap_eq, Measure.map_id]

end TauCeti

end

end
