/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Kernel.CondDistrib
public import TauCeti.MeasureTheory.OptimalTransport.Coupling

/-!
# Disintegrating transport plans

A coupling can be read in two equivalent ways: as a measure on a product with prescribed
marginals, or as a source measure followed by a probability kernel whose averaged law is the
target. This file connects the coupling API to Mathlib's composition-product and regular
conditional-kernel APIs.

For a Markov kernel `κ : Kernel X Y`, the composition-product `μ ⊗ₘ κ` couples `μ` to the
averaged law `κ ∘ₘ μ`. Conversely, when the target space is standard Borel, a finite coupling
`π` reconstructs as `μ ⊗ₘ π.condKernel`, and its conditional kernel averages to the prescribed
target. Any other finite kernel reconstructing the same plan agrees with `π.condKernel`
`μ`-almost everywhere.

## Main statements

* `TauCeti.isCoupling_compProd` constructs a coupling from a source measure and a Markov kernel;
* `TauCeti.isCoupling_compProd_iff` characterizes when that coupling has a specified target;
* `TauCeti.IsCoupling.compProd_condKernel` reconstructs a finite coupling from its source
  marginal and Mathlib's conditional kernel;
* `TauCeti.IsCoupling.condKernel_comp` identifies the averaged conditional law with the target
  marginal;
* `TauCeti.IsCoupling.ae_eq_condKernel_iff_compProd_eq` gives the coupling-facing uniqueness
  criterion for conditional kernels;
* `TauCeti.IsCoupling.compProd_condDistrib` and
  `TauCeti.IsCoupling.condDistrib_ae_eq_condKernel` give the same reconstruction through the
  conditional distribution of the two coordinate maps and identify the two Mathlib interfaces;
* the corresponding declarations in `TauCeti.Coupling` specialize these results to the bundled
  probability-coupling type.

This is Layer 0, item 3 of the optimal-transport roadmap. The construction and uniqueness theorem
consume Mathlib's `MeasureTheory.Measure.disintegrate` and
`ProbabilityTheory.eq_condKernel_of_measure_eq_compProd`; no disintegration is rebuilt here.

## References

* C. Villani, *Optimal Transport: Old and New*, Grundlehren 338, 2009, Chapter 5, especially
  Theorem 5.3 (disintegration of measures). The presentation here uses Mathlib's regular
  conditional kernels on a standard Borel target.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace TauCeti

universe u v

variable {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSpace Y]
  {π : Measure (X × Y)} {μ : Measure X} {ν : Measure Y}

/-- The composition-product of a measure and a Markov kernel couples the measure to the law
obtained by averaging the kernel against it. This is the unbundled reconstruction of a joint law
from a marginal and a conditional probability kernel. -/
theorem isCoupling_compProd (μ : Measure X) [SFinite μ] (κ : Kernel X Y) [IsMarkovKernel κ] :
    IsCoupling (μ ⊗ₘ κ) μ (κ ∘ₘ μ) where
  fst_eq := Measure.fst_compProd μ κ
  snd_eq := Measure.snd_compProd μ κ

/-- A composition-product has prescribed marginals `μ` and `ν` exactly when averaging its Markov
kernel against `μ` gives `ν`. -/
@[simp]
theorem isCoupling_compProd_iff (μ : Measure X) [SFinite μ] (κ : Kernel X Y) [IsMarkovKernel κ] :
    IsCoupling (μ ⊗ₘ κ) μ ν ↔ κ ∘ₘ μ = ν := by
  constructor
  · intro h
    simpa only [Measure.snd_compProd] using h.snd_eq
  · intro h
    exact ⟨Measure.fst_compProd μ κ, (Measure.snd_compProd μ κ).trans h⟩

namespace IsCoupling

variable [StandardBorelSpace Y] [Nonempty Y] [IsFiniteMeasure π]

/-- A finite coupling is reconstructed by composing its source marginal with Mathlib's regular
conditional kernel of the second coordinate given the first. -/
theorem compProd_condKernel (hπ : IsCoupling π μ ν) : μ ⊗ₘ π.condKernel = π := by
  rw [← hπ.fst_eq]
  exact Measure.disintegrate π π.condKernel

/-- Averaging the conditional kernel of a finite coupling against its source marginal gives its
target marginal. -/
theorem condKernel_comp (hπ : IsCoupling π μ ν) : π.condKernel ∘ₘ μ = ν := by
  let _ : IsFiniteMeasure μ := by
    rw [← hπ.fst_eq]
    infer_instance
  rw [← Measure.snd_compProd, hπ.compProd_condKernel, hπ.snd_eq]

/-- A finite kernel agrees almost everywhere with the regular conditional kernel of a finite
coupling exactly when its composition-product with the source marginal reconstructs that
coupling. This is the coupling-facing uniqueness theorem for disintegration. -/
theorem ae_eq_condKernel_iff_compProd_eq (hπ : IsCoupling π μ ν) (κ : Kernel X Y)
    [IsFiniteKernel κ] : κ =ᵐ[μ] π.condKernel ↔ μ ⊗ₘ κ = π := by
  let _ : IsFiniteMeasure μ := by
    rw [← hπ.fst_eq]
    infer_instance
  constructor
  · intro hκ
    exact (Measure.compProd_congr hκ).trans hπ.compProd_condKernel
  · intro hκ
    have hreconstruct : π = π.fst ⊗ₘ κ := by
      rw [hπ.fst_eq, hκ]
    have hunique := ProbabilityTheory.eq_condKernel_of_measure_eq_compProd κ hreconstruct
    rw [hπ.fst_eq] at hunique
    filter_upwards [hunique] with x hx
    exact hx

/-- The conditional distribution of the second coordinate given the first reconstructs a finite
coupling from its source marginal. This is the coordinate-map form of
`TauCeti.IsCoupling.compProd_condKernel`. -/
theorem compProd_condDistrib (hπ : IsCoupling π μ ν) :
    μ ⊗ₘ condDistrib Prod.snd Prod.fst π = π := by
  rw [← hπ.fst_eq]
  have heta : (fun z : X × Y ↦ (z.1, z.2)) = id := funext Prod.eta
  simpa only [Measure.fst, heta, Measure.map_id] using
    (ProbabilityTheory.compProd_map_condDistrib (μ := π) (X := Prod.fst) (Y := Prod.snd)
      measurable_snd.aemeasurable)

/-- The conditional distribution of the second coordinate given the first averages against the
source marginal to the target marginal. -/
theorem condDistrib_comp (hπ : IsCoupling π μ ν) :
    condDistrib Prod.snd Prod.fst π ∘ₘ μ = ν := by
  rw [← hπ.fst_eq, ← hπ.snd_eq]
  exact ProbabilityTheory.condDistrib_comp_map measurable_fst.aemeasurable
    measurable_snd.aemeasurable

/-- For a finite coupling, the conditional distribution of the second coordinate given the first
is almost everywhere the same kernel as Mathlib's regular conditional kernel of the joint
measure. -/
theorem condDistrib_ae_eq_condKernel (hπ : IsCoupling π μ ν) :
    condDistrib Prod.snd Prod.fst π =ᵐ[μ] π.condKernel :=
  (hπ.ae_eq_condKernel_iff_compProd_eq _).2 hπ.compProd_condDistrib

end IsCoupling

namespace Coupling

variable {μ : ProbabilityMeasure X} {ν : ProbabilityMeasure Y}
  [StandardBorelSpace Y] [Nonempty Y]

/-- The underlying measure of a bundled probability coupling is reconstructed from its source
law and regular conditional kernel. -/
@[simp]
theorem compProd_condKernel (π : Coupling μ ν) :
    μ.toMeasure ⊗ₘ π.1.toMeasure.condKernel = π.1.toMeasure :=
  π.2.compProd_condKernel

/-- The regular conditional kernel of a bundled probability coupling averages to its prescribed
target law. -/
@[simp]
theorem condKernel_comp (π : Coupling μ ν) :
    π.1.toMeasure.condKernel ∘ₘ μ.toMeasure = ν.toMeasure :=
  π.2.condKernel_comp

/-- A finite kernel is a version of the regular conditional kernel of a bundled probability
coupling exactly when it reconstructs the coupling from its source law. -/
theorem ae_eq_condKernel_iff_compProd_eq (π : Coupling μ ν) (κ : Kernel X Y)
    [IsFiniteKernel κ] :
    κ =ᵐ[μ.toMeasure] π.1.toMeasure.condKernel ↔ μ.toMeasure ⊗ₘ κ = π.1.toMeasure :=
  π.2.ae_eq_condKernel_iff_compProd_eq κ

/-- The coordinate conditional distribution of a bundled probability coupling reconstructs its
underlying joint law. -/
@[simp]
theorem compProd_condDistrib (π : Coupling μ ν) :
    μ.toMeasure ⊗ₘ condDistrib Prod.snd Prod.fst π.1.toMeasure = π.1.toMeasure :=
  π.2.compProd_condDistrib

/-- The coordinate conditional distribution of a bundled probability coupling averages to its
target law. -/
@[simp]
theorem condDistrib_comp (π : Coupling μ ν) :
    condDistrib Prod.snd Prod.fst π.1.toMeasure ∘ₘ μ.toMeasure = ν.toMeasure :=
  π.2.condDistrib_comp

/-- The coordinate conditional distribution and regular conditional kernel of a bundled
probability coupling agree almost everywhere under its source law. -/
theorem condDistrib_ae_eq_condKernel (π : Coupling μ ν) :
    condDistrib Prod.snd Prod.fst π.1.toMeasure =ᵐ[μ.toMeasure]
      π.1.toMeasure.condKernel :=
  π.2.condDistrib_ae_eq_condKernel

end Coupling

end TauCeti
