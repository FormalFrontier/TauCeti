/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Couplings of measures

A **coupling** of two measures `μ₁` and `μ₂` is a measure on their product whose marginals are
`μ₁` and `μ₂`. This file provides the carrier-independent coupling API used by the dense graph
limit theory: marginal projection rules, measure-preserving projections, integral transfer,
coordinate swapping, and the independent and diagonal constructions.

`IsCoupling` is deliberately a `Prop`, rather than a structure or typeclass. A coupling is
generally not canonical, and consumers such as the cut distance minimize over all witnesses. The
product and diagonal measures provide two standard constructions on a common probability carrier;
depending on the measure, they may or may not differ.

The declarations live in `TauCeti.MeasureTheory` because none depends on graphons or cut metrics.

## Main definitions

* `TauCeti.MeasureTheory.IsCoupling` — the predicate that a measure has prescribed marginals;
* `TauCeti.MeasureTheory.diagonalCoupling` — the pushforward of a measure along the diagonal.

## Main results

* `isCoupling_prod` and `isCoupling_diagonalCoupling` construct couplings;
* `IsCoupling.isProbabilityMeasure` and `IsCoupling.isFiniteMeasure` record that a coupling of
  probability measures is one;
* `IsCoupling.measurePreserving_fst` and `IsCoupling.measurePreserving_snd` expose the marginal
  projections as measure-preserving maps;
* `IsCoupling.integral_comp_fst` and `IsCoupling.integral_comp_snd` transfer integrals depending on
  one coordinate to the corresponding marginal;
* `IsCoupling.swap` swaps the coordinates of a coupling;
* `isCoupling_map_prodMk` builds the graph coupling of two measure-preserving maps out of a common
  carrier, of which `isCoupling_diagonalCoupling` is the identity case.

## References

* Roadmap: `TauCetiRoadmap/DenseGraphLimits/README.md`, Layer 1 — the coupling-primary,
  cross-carrier cut distance and its `IsCoupling` input.
* `TauCeti/MeasureTheory/OptimalTransport/Gluing.lean` — the existing gluing API whose formulation
  of marginal conditions via `Measure.fst` and `Measure.snd` is followed here.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace MeasureTheory

variable {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]

/-- A **coupling** of `μ₁` and `μ₂`: a measure on the product whose marginals are `μ₁` and `μ₂`.

Deliberately a `Prop` rather than a structure or a class: a coupling of two given marginals is not
canonical, and the cut distance minimizes over all of them. Use `isCoupling_iff` to unfold. -/
def IsCoupling (μ₁ : Measure Ω₁) (μ₂ : Measure Ω₂) (π : Measure (Ω₁ × Ω₂)) : Prop :=
  π.fst = μ₁ ∧ π.snd = μ₂

variable {μ₁ : Measure Ω₁} {μ₂ : Measure Ω₂} {π : Measure (Ω₁ × Ω₂)}

/-- The defining conditions of `IsCoupling`. The definition's body is not exposed, so this is the
lemma downstream modules should rewrite with. -/
theorem isCoupling_iff : IsCoupling μ₁ μ₂ π ↔ π.fst = μ₁ ∧ π.snd = μ₂ := (Iff.rfl)

/-- The first marginal of a coupling. -/
theorem IsCoupling.fst_eq (hπ : IsCoupling μ₁ μ₂ π) : π.fst = μ₁ := isCoupling_iff.1 hπ |>.1

/-- The second marginal of a coupling. -/
theorem IsCoupling.snd_eq (hπ : IsCoupling μ₁ μ₂ π) : π.snd = μ₂ := isCoupling_iff.1 hπ |>.2

/-- The first projection out of a coupling is measure preserving. This is the marginal condition in
the form the integral transfer below consumes, and the form the measure-preserving-map picture of
the cut distance is stated in. -/
theorem IsCoupling.measurePreserving_fst (hπ : IsCoupling μ₁ μ₂ π) :
    MeasurePreserving Prod.fst π μ₁ :=
  ⟨measurable_fst, hπ.fst_eq⟩

/-- The second projection out of a coupling is measure preserving. -/
theorem IsCoupling.measurePreserving_snd (hπ : IsCoupling μ₁ μ₂ π) :
    MeasurePreserving Prod.snd π μ₂ :=
  ⟨measurable_snd, hπ.snd_eq⟩

/-- A coupling of probability measures is itself a probability measure. -/
theorem IsCoupling.isProbabilityMeasure [IsProbabilityMeasure μ₁] (hπ : IsCoupling μ₁ μ₂ π) :
    IsProbabilityMeasure π :=
  ⟨by rw [← Measure.fst_univ, hπ.fst_eq, measure_univ]⟩

/-- A coupling whose first marginal is finite is a finite measure.

This weakening is what an existentially quantified coupling has to supply by hand: a consumer such
as the cut norm asks for `IsFiniteMeasure`, and a witness bound by an existential cannot provide an
instance by unification, so it passes this term explicitly. -/
theorem IsCoupling.isFiniteMeasure [IsFiniteMeasure μ₁] (hπ : IsCoupling μ₁ μ₂ π) :
    IsFiniteMeasure π :=
  ⟨by rw [← Measure.fst_univ, hπ.fst_eq]; exact measure_lt_top μ₁ Set.univ⟩

/-- The **independent coupling**: the product measure couples its two factors. -/
theorem isCoupling_prod (μ₁ : Measure Ω₁) (μ₂ : Measure Ω₂) [IsProbabilityMeasure μ₁]
    [IsProbabilityMeasure μ₂] : IsCoupling μ₁ μ₂ (μ₁.prod μ₂) :=
  isCoupling_iff.2 ⟨Measure.fst_prod, Measure.snd_prod⟩

/-- Swapping the two coordinates of a coupling of `μ₁` and `μ₂` gives a coupling of `μ₂` and `μ₁`.
-/
theorem IsCoupling.swap (hπ : IsCoupling μ₁ μ₂ π) : IsCoupling μ₂ μ₁ (π.map Prod.swap) :=
  isCoupling_iff.2
    ⟨by rw [Measure.fst_map_swap, hπ.snd_eq], by rw [Measure.snd_map_swap, hπ.fst_eq]⟩

section Integral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A function of the first coordinate integrates against a coupling as it does against the first
marginal. -/
theorem IsCoupling.integral_comp_fst (hπ : IsCoupling μ₁ μ₂ π) {f : Ω₁ → E}
    (hf : AEStronglyMeasurable f μ₁) : ∫ p, f p.1 ∂π = ∫ x, f x ∂μ₁ := by
  rw [← hπ.measurePreserving_fst.map_eq] at hf ⊢
  exact (integral_map measurable_fst.aemeasurable hf).symm

/-- A function of the second coordinate integrates against a coupling as it does against the second
marginal. -/
theorem IsCoupling.integral_comp_snd (hπ : IsCoupling μ₁ μ₂ π) {f : Ω₂ → E}
    (hf : AEStronglyMeasurable f μ₂) : ∫ p, f p.2 ∂π = ∫ x, f x ∂μ₂ := by
  rw [← hπ.measurePreserving_snd.map_eq] at hf ⊢
  exact (integral_map measurable_snd.aemeasurable hf).symm

end Integral

section Graph

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The **graph coupling** of two measure-preserving maps out of a common carrier: pushing `μ`
forward along `x ↦ (f x, g x)` couples `μ₁` and `μ₂`.

This is the coupling a common-carrier comparison of two objects contributes to a coupling
infimum, and it is where the measure-preserving-map picture enters the coupling-primary one. The
diagonal coupling below is the case `f = g = id`. -/
theorem isCoupling_map_prodMk {f : Ω → Ω₁} {g : Ω → Ω₂} (hf : MeasurePreserving f μ μ₁)
    (hg : MeasurePreserving g μ μ₂) : IsCoupling μ₁ μ₂ (μ.map fun x => (f x, g x)) :=
  isCoupling_iff.2
    ⟨by rw [Measure.fst_map_prodMk hg.measurable, hf.map_eq],
      by rw [Measure.snd_map_prodMk hf.measurable, hg.map_eq]⟩

end Graph

section Diagonal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The **diagonal coupling** of a measure with itself: the pushforward of `μ` along `x ↦ (x, x)`.
-/
def diagonalCoupling (μ : Measure Ω) : Measure (Ω × Ω) := μ.map fun x => (x, x)

/-- The diagonal coupling of a measurable set is the measure of its diagonal slice. -/
theorem diagonalCoupling_apply (μ : Measure Ω) {s : Set (Ω × Ω)} (hs : MeasurableSet s) :
    diagonalCoupling μ s = μ {x | (x, x) ∈ s} := by
  rw [diagonalCoupling, Measure.map_apply (measurable_id'.prodMk measurable_id') hs]
  rfl

/-- The diagonal coupling is a coupling of `μ` with itself: the graph coupling of the identity
with itself. -/
theorem isCoupling_diagonalCoupling (μ : Measure Ω) : IsCoupling μ μ (diagonalCoupling μ) :=
  isCoupling_map_prodMk (MeasurePreserving.id μ) (MeasurePreserving.id μ)

/-- The diagonal coupling of a probability measure is a probability measure. -/
instance instIsProbabilityMeasureDiagonalCoupling (μ : Measure Ω) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (diagonalCoupling μ) :=
  (isCoupling_diagonalCoupling μ).isProbabilityMeasure

end Diagonal

end MeasureTheory

end TauCeti
