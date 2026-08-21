/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.EnergyForm.Continuity
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas

/-!
# Measurability of pointwise PDE energy integrands

The weak-form lane of the PDE roadmap is stated for bounded measurable coefficients.  Before the
pointwise jet integrand
`x ↦ energyIntegrand (a x) (b x) (c x)` can be integrated over a domain, it must be available as a
strongly measurable field of continuous bilinear forms, and its scalar evaluations on measurable
jet fields must be a.e. strongly measurable.

This file supplies that finite-dimensional bookkeeping.  It does not introduce a bundled
bounded-measurable-coefficient predicate; coefficient regularity remains stated inline,
following the roadmap and Mathlib style.

## Main declarations

* `stronglyMeasurable_energyIntegrand` and `aestronglyMeasurable_energyIntegrand`: measurable
  coefficient fields give a measurable field of pointwise energy integrands.
* `stronglyMeasurable_energyIntegrand_apply`, `stronglyMeasurable_energyIntegrand_apply₂`,
  `aestronglyMeasurable_energyIntegrand_apply`, and
  `aestronglyMeasurable_energyIntegrand_apply₂`: scalar evaluations on fixed or measurable jet
  fields are measurable.
-/

public section

namespace TauCeti

namespace PDE

open MeasureTheory

variable {α n : Type*} [MeasurableSpace α] [Fintype n]

/-- Strongly measurable coefficient fields give a strongly measurable field of pointwise energy
integrands. -/
lemma stronglyMeasurable_energyIntegrand {a : α → Matrix n n ℝ} {b : α → EuclideanSpace ℝ n}
    {c : α → ℝ}
    (ha : StronglyMeasurable a) (hb : StronglyMeasurable b) (hc : StronglyMeasurable c) :
    StronglyMeasurable (fun x => PDE.energyIntegrand (a x) (b x) (c x)) :=
  continuous_energyIntegrand.comp_stronglyMeasurable (ha.prodMk (hb.prodMk hc))

/-- Strongly measurable coefficient fields and strongly measurable jet fields give a strongly
measurable scalar energy density. -/
lemma stronglyMeasurable_energyIntegrand_apply₂ {a : α → Matrix n n ℝ}
    {b : α → EuclideanSpace ℝ n} {c : α → ℝ} {U V : α → ℝ × EuclideanSpace ℝ n}
    (ha : StronglyMeasurable a) (hb : StronglyMeasurable b) (hc : StronglyMeasurable c)
    (hU : StronglyMeasurable U) (hV : StronglyMeasurable V) :
    StronglyMeasurable (fun x => PDE.energyIntegrand (a x) (b x) (c x) (U x) (V x)) := by
  let Jet := ℝ × EuclideanSpace ℝ n
  have hform : StronglyMeasurable (fun x => PDE.energyIntegrand (a x) (b x) (c x)) :=
    stronglyMeasurable_energyIntegrand ha hb hc
  have hcont : Continuous (fun p : (Jet →L[ℝ] Jet →L[ℝ] ℝ) × Jet × Jet =>
      p.1 p.2.1 p.2.2) := by
    exact (continuous_fst.clm_apply (continuous_fst.comp continuous_snd)).clm_apply
      (continuous_snd.comp continuous_snd)
  exact hcont.comp_stronglyMeasurable (hform.prodMk (hU.prodMk hV))

/-- Strongly measurable coefficient fields give strongly measurable scalar evaluations of the
pointwise energy integrand on fixed jets. -/
lemma stronglyMeasurable_energyIntegrand_apply {a : α → Matrix n n ℝ}
    {b : α → EuclideanSpace ℝ n} {c : α → ℝ}
    (ha : StronglyMeasurable a) (hb : StronglyMeasurable b) (hc : StronglyMeasurable c)
    (U V : ℝ × EuclideanSpace ℝ n) :
    StronglyMeasurable (fun x => PDE.energyIntegrand (a x) (b x) (c x) U V) :=
  stronglyMeasurable_energyIntegrand_apply₂ ha hb hc stronglyMeasurable_const
    stronglyMeasurable_const

variable {μ : MeasureTheory.Measure α}

/-- A.e. strongly measurable coefficient fields give an a.e. strongly measurable field of
pointwise energy integrands. -/
lemma aestronglyMeasurable_energyIntegrand {a : α → Matrix n n ℝ}
    {b : α → EuclideanSpace ℝ n} {c : α → ℝ}
    (ha : MeasureTheory.AEStronglyMeasurable a μ) (hb : MeasureTheory.AEStronglyMeasurable b μ)
    (hc : MeasureTheory.AEStronglyMeasurable c μ) :
    AEStronglyMeasurable (fun x => PDE.energyIntegrand (a x) (b x) (c x)) μ :=
  continuous_energyIntegrand.comp_aestronglyMeasurable (ha.prodMk (hb.prodMk hc))

/-- A.e. strongly measurable coefficient fields give a.e. strongly measurable scalar evaluations of
the pointwise energy integrand on fixed jets. -/
lemma aestronglyMeasurable_energyIntegrand_apply {a : α → Matrix n n ℝ}
    {b : α → EuclideanSpace ℝ n} {c : α → ℝ}
    (ha : MeasureTheory.AEStronglyMeasurable a μ) (hb : MeasureTheory.AEStronglyMeasurable b μ)
    (hc : MeasureTheory.AEStronglyMeasurable c μ) (U V : ℝ × EuclideanSpace ℝ n) :
    AEStronglyMeasurable (fun x => PDE.energyIntegrand (a x) (b x) (c x) U V) μ :=
  MeasureTheory.AEStronglyMeasurable.apply_continuousLinearMap
    (MeasureTheory.AEStronglyMeasurable.apply_continuousLinearMap
      (aestronglyMeasurable_energyIntegrand ha hb hc) U) V

/-- A.e. strongly measurable coefficient fields and a.e. strongly measurable jet fields give an
a.e. strongly measurable scalar energy density. -/
lemma aestronglyMeasurable_energyIntegrand_apply₂ {a : α → Matrix n n ℝ}
    {b : α → EuclideanSpace ℝ n} {c : α → ℝ} {U V : α → ℝ × EuclideanSpace ℝ n}
    (ha : MeasureTheory.AEStronglyMeasurable a μ) (hb : MeasureTheory.AEStronglyMeasurable b μ)
    (hc : MeasureTheory.AEStronglyMeasurable c μ) (hU : MeasureTheory.AEStronglyMeasurable U μ)
    (hV : MeasureTheory.AEStronglyMeasurable V μ) :
    AEStronglyMeasurable (fun x => PDE.energyIntegrand (a x) (b x) (c x) (U x) (V x)) μ := by
  let Jet := ℝ × EuclideanSpace ℝ n
  have hform : AEStronglyMeasurable (fun x => PDE.energyIntegrand (a x) (b x) (c x)) μ :=
    aestronglyMeasurable_energyIntegrand ha hb hc
  have hcont : Continuous (fun p : (Jet →L[ℝ] Jet →L[ℝ] ℝ) × Jet × Jet =>
      p.1 p.2.1 p.2.2) := by
    exact (continuous_fst.clm_apply (continuous_fst.comp continuous_snd)).clm_apply
      (continuous_snd.comp continuous_snd)
  exact hcont.comp_aestronglyMeasurable (hform.prodMk (hU.prodMk hV))

end PDE

end TauCeti
