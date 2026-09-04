/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.DiracProba
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Basic

/-!
# Finite-distance Wasserstein spaces

The Wasserstein distance can be infinite, even between probability measures. This file isolates
the parts on which it is finite and hence defines an ordinary pseudometric:

* `TauCeti.WassersteinComponent p μ₀` consists of the probability measures at finite
  `p`-Wasserstein distance from the anchor `μ₀`;
* `TauCeti.WassersteinSpace p X` consists of the probability measures on `X` with finite
  `p`-moment.

Every pseudoemetric and pseudometric structure below needs `1 ≤ p`, since that is the range in
which the Wasserstein triangle inequality holds; the abstract constructors take it as an explicit
hypothesis and the instances read it off `Fact (1 ≤ p)`. For such `p`, on a standard Borel extended
pseudometric space with measurable ground distance, every anchored component carries the
Wasserstein pseudoemetric, and hence the real-valued Wasserstein pseudometric, because distances
inside a single component are finite. On an ordinary pseudometric space, finite moment about one
point is equivalent to finite Wasserstein distance from the Dirac mass at any point.
Consequently `WassersteinSpace p X` is canonically equivalent, after choosing a point `x₀`, to
the component anchored at `δ_[x₀]`, and it carries the same Wasserstein pseudometric without a
basepoint appearing in its definition.

When moreover the ground space is Polish and its distance separates points, both pseudometrics
are metrics. The measurable structures are the subtype structures inherited from
`ProbabilityMeasure`; no second measurable-space instance is introduced. Identifying these
measurable structures with the Borel sigma algebras of the Wasserstein metrics is a separate
topological result.

Neither carrier exposes its subtype body: elements are built with `TauCeti.WassersteinComponent.mk`
and `TauCeti.WassersteinSpace.mk`, and taken apart with `toProbabilityMeasure` together with
`TauCeti.WassersteinComponent.wassersteinEDist_anchor_ne_top` and
`TauCeti.WassersteinSpace.hasFiniteMoment`. The identification `equivComponent` leaves the
underlying probability measure unchanged, hence is an isometry for the two Wasserstein
pseudometrics and is measurable in both directions.

## Main definitions

* `TauCeti.WassersteinComponent p μ₀` — the finite-distance component of an anchor law;
* `TauCeti.WassersteinSpace p X` — probability laws with finite `p`-moment;
* `TauCeti.WassersteinSpace.equivComponent` — identification with a Dirac-anchored component.

## References

* C. Villani, *Optimal Transport: Old and New*, Grundlehren 338, Springer 2009, Chapter 6.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace TauCeti

universe u

variable {X : Type u} {p : ℝ≥0∞}

/-- Probability measures at finite `p`-Wasserstein distance from the anchor `μ₀`.

This is a type synonym for a subtype, so it can carry the Wasserstein topology independently of
the weak topology already present on `ProbabilityMeasure`. Its measurable structure is still the
canonical subtype structure. The subtype body is not exposed: use
`TauCeti.WassersteinComponent.mk` and `TauCeti.WassersteinComponent.toProbabilityMeasure`. -/
def WassersteinComponent [MeasurableSpace X] [PseudoEMetricSpace X]
    (p : ℝ≥0∞) (μ₀ : ProbabilityMeasure X) :=
  {μ : ProbabilityMeasure X //
    wassersteinEDist p (μ₀ : Measure X) (μ : Measure X) ≠ ∞}

/-- Probability measures on `X` with finite `p`-moment.

As for `TauCeti.WassersteinComponent`, the subtype body is not exposed: use
`TauCeti.WassersteinSpace.mk` and `TauCeti.WassersteinSpace.toProbabilityMeasure`. -/
def WassersteinSpace (p : ℝ≥0∞) (X : Type u) [MeasurableSpace X] [PseudoEMetricSpace X] :=
  {μ : ProbabilityMeasure X // HasFiniteMoment p (μ : Measure X)}

namespace WassersteinComponent

section Basic

variable [MeasurableSpace X] [PseudoEMetricSpace X] {μ₀ : ProbabilityMeasure X}

/-- The element of the component anchored at `μ₀` given by a probability measure at finite
`p`-Wasserstein distance from `μ₀`. -/
def mk (μ : ProbabilityMeasure X)
    (hμ : wassersteinEDist p (μ₀ : Measure X) (μ : Measure X) ≠ ∞) :
    WassersteinComponent p μ₀ :=
  ⟨μ, hμ⟩

/-- The probability measure underlying an element of a Wasserstein component. -/
@[coe]
def toProbabilityMeasure (μ : WassersteinComponent p μ₀) : ProbabilityMeasure X := μ.1

instance : CoeOut (WassersteinComponent p μ₀) (ProbabilityMeasure X) :=
  ⟨toProbabilityMeasure⟩

/-- The inclusion of a Wasserstein component into probability measures is injective. -/
theorem toProbabilityMeasure_injective :
    Function.Injective (toProbabilityMeasure : WassersteinComponent p μ₀ → ProbabilityMeasure X) :=
  fun _ _ h ↦ Subtype.ext h

/-- Two elements of a Wasserstein component are equal when their probability measures are equal. -/
@[ext]
theorem ext {μ ν : WassersteinComponent p μ₀}
    (h : (μ : ProbabilityMeasure X) = (ν : ProbabilityMeasure X)) : μ = ν :=
  toProbabilityMeasure_injective h

/-- A Wasserstein component inherits the Giry measurable structure from probability measures. -/
instance instMeasurableSpace : MeasurableSpace (WassersteinComponent p μ₀) :=
  inferInstanceAs (MeasurableSpace
    {μ : ProbabilityMeasure X //
      wassersteinEDist p (μ₀ : Measure X) (μ : Measure X) ≠ ∞})

/-- The inclusion of a Wasserstein component into probability measures is measurable. -/
theorem measurable_toProbabilityMeasure :
    Measurable (toProbabilityMeasure : WassersteinComponent p μ₀ → ProbabilityMeasure X) :=
  measurable_subtype_coe

@[simp]
theorem coe_mk (μ : ProbabilityMeasure X) (hμ) :
    toProbabilityMeasure (mk (p := p) (μ₀ := μ₀) μ hμ) = μ :=
  (rfl)

/-- Every element of the component anchored at `μ₀` is at finite Wasserstein distance from `μ₀`;
together with `TauCeti.WassersteinComponent.mk` this characterises the elements of the
component. -/
theorem wassersteinEDist_anchor_ne_top (μ : WassersteinComponent p μ₀) :
    wassersteinEDist p (μ₀ : Measure X) ((μ : ProbabilityMeasure X) : Measure X) ≠ ∞ :=
  μ.2

@[simp]
theorem mk_coe (μ : WassersteinComponent p μ₀) :
    mk (μ : ProbabilityMeasure X) (wassersteinEDist_anchor_ne_top μ) = μ :=
  (rfl)

end Basic

section PseudoEMetric

variable [MeasurableSpace X] [PseudoEMetricSpace X] [StandardBorelSpace X]
  {μ₀ : ProbabilityMeasure X}

/-- The Wasserstein extended distance equips every anchored finite-distance component with a
pseudoemetric space structure whenever the ground extended distance is measurable and `1 ≤ p`. -/
@[instance_reducible]
noncomputable def pseudoEMetricSpace
    (hd : Measurable fun z : X × X ↦ edist z.1 z.2) (hp : 1 ≤ p) :
    PseudoEMetricSpace (WassersteinComponent p μ₀) :=
  PseudoEMetricSpace.ofEDist
    (fun μ ν ↦ wassersteinEDist p
      ((μ : ProbabilityMeasure X) : Measure X) ((ν : ProbabilityMeasure X) : Measure X))
    (fun μ ↦ wassersteinEDist_self p ((μ : ProbabilityMeasure X) : Measure X))
    (fun μ ν ↦ wassersteinEDist_comm hd p
      ((μ : ProbabilityMeasure X) : Measure X) ((ν : ProbabilityMeasure X) : Measure X))
    (fun μ ν ρ ↦ wassersteinEDist_triangle hd hp
      ((μ : ProbabilityMeasure X) : Measure X) ((ν : ProbabilityMeasure X) : Measure X)
      ((ρ : ProbabilityMeasure X) : Measure X))

variable [BorelSpace X] [SecondCountableTopology X] [Fact (1 ≤ p)]

/-- The canonical Wasserstein pseudoemetric on an anchored component when the ground extended
distance is Borel measurable. -/
noncomputable instance instPseudoEMetricSpace :
    PseudoEMetricSpace (WassersteinComponent p μ₀) :=
  pseudoEMetricSpace measurable_edist Fact.out

/-- The extended distance on a Wasserstein component is the Wasserstein distance of the
underlying probability measures. -/
@[simp]
theorem edist_def (μ ν : WassersteinComponent p μ₀) :
    edist μ ν = wassersteinEDist p
      ((μ : ProbabilityMeasure X) : Measure X) ((ν : ProbabilityMeasure X) : Measure X) :=
  (rfl)

/-- Any two laws in one anchored Wasserstein component are at finite distance from one another. -/
theorem edist_ne_top (μ ν : WassersteinComponent p μ₀) : edist μ ν ≠ ∞ := by
  rw [edist_def]
  have hμ : wassersteinEDist p
      ((μ : ProbabilityMeasure X) : Measure X) (μ₀ : Measure X) ≠ ∞ := by
    rw [wassersteinEDist_comm measurable_edist]
    exact wassersteinEDist_anchor_ne_top μ
  apply ne_top_of_le_ne_top
    (ENNReal.add_ne_top.mpr ⟨hμ, wassersteinEDist_anchor_ne_top ν⟩)
  exact wassersteinEDist_triangle measurable_edist Fact.out
    ((μ : ProbabilityMeasure X) : Measure X) (μ₀ : Measure X)
    ((ν : ProbabilityMeasure X) : Measure X)

/-- Every anchored finite-distance component carries the real-valued Wasserstein
pseudometric. -/
noncomputable instance instPseudoMetricSpace :
    PseudoMetricSpace (WassersteinComponent p μ₀) :=
  PseudoEMetricSpace.toPseudoMetricSpace edist_ne_top

/-- The distance on a Wasserstein component is the real value of the Wasserstein extended
distance. -/
@[simp]
theorem dist_def (μ ν : WassersteinComponent p μ₀) :
    dist μ ν = (wassersteinEDist p
      ((μ : ProbabilityMeasure X) : Measure X) ((ν : ProbabilityMeasure X) : Measure X)).toReal :=
  (rfl)

end PseudoEMetric

section Metric

variable [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [CompleteSpace X] [Fact (1 ≤ p)] {μ₀ : ProbabilityMeasure X}

/-- On a Polish metric ground space, Wasserstein distance separates laws, so every anchored
finite-distance component is a metric space. -/
noncomputable instance instMetricSpace : MetricSpace (WassersteinComponent p μ₀) where
  toPseudoMetricSpace := inferInstance
  eq_of_dist_eq_zero {μ ν} h := by
    have hp : (1 : ℝ≥0∞) ≤ p := Fact.out
    apply ext
    apply ProbabilityMeasure.toMeasure_injective
    refine eq_of_wassersteinEDist_eq_zero (ne_of_gt (zero_lt_one.trans_le hp)) _ _ ?_
    rw [← edist_def, edist_dist, h]
    simp

end Metric

end WassersteinComponent

namespace WassersteinSpace

section Basic

variable [MeasurableSpace X] [PseudoEMetricSpace X]

/-- The element of `WassersteinSpace p X` given by a probability measure of finite `p`-moment. -/
def mk (μ : ProbabilityMeasure X) (hμ : HasFiniteMoment p (μ : Measure X)) :
    WassersteinSpace p X :=
  ⟨μ, hμ⟩

/-- The probability measure underlying an element of `WassersteinSpace p X`. -/
@[coe]
def toProbabilityMeasure (μ : WassersteinSpace p X) : ProbabilityMeasure X := μ.1

instance : CoeOut (WassersteinSpace p X) (ProbabilityMeasure X) :=
  ⟨toProbabilityMeasure⟩

/-- The inclusion of finite-moment laws into probability measures is injective. -/
theorem toProbabilityMeasure_injective :
    Function.Injective (toProbabilityMeasure : WassersteinSpace p X → ProbabilityMeasure X) :=
  fun _ _ h ↦ Subtype.ext h

/-- Two finite-moment laws are equal when their probability measures are equal. -/
@[ext]
theorem ext {μ ν : WassersteinSpace p X}
    (h : (μ : ProbabilityMeasure X) = (ν : ProbabilityMeasure X)) : μ = ν :=
  toProbabilityMeasure_injective h

/-- `WassersteinSpace p X` inherits the Giry measurable structure from probability measures. -/
instance instMeasurableSpace : MeasurableSpace (WassersteinSpace p X) :=
  inferInstanceAs (MeasurableSpace
    {μ : ProbabilityMeasure X // HasFiniteMoment p (μ : Measure X)})

/-- The inclusion of finite-moment laws into probability measures is measurable. -/
theorem measurable_toProbabilityMeasure :
    Measurable (toProbabilityMeasure : WassersteinSpace p X → ProbabilityMeasure X) :=
  measurable_subtype_coe

@[simp]
theorem coe_mk (μ : ProbabilityMeasure X) (hμ) :
    toProbabilityMeasure (mk (p := p) μ hμ) = μ :=
  (rfl)

/-- Every law in `WassersteinSpace p X` has finite `p`-moment; together with
`TauCeti.WassersteinSpace.mk` this characterises its elements. -/
theorem hasFiniteMoment (μ : WassersteinSpace p X) :
    HasFiniteMoment p ((μ : ProbabilityMeasure X) : Measure X) :=
  μ.2

@[simp]
theorem mk_coe (μ : WassersteinSpace p X) :
    mk (μ : ProbabilityMeasure X) (hasFiniteMoment μ) = μ :=
  (rfl)

end Basic

section MetricGround

variable [MeasurableSpace X] [PseudoMetricSpace X] [BorelSpace X] [SecondCountableTopology X]

/-- Choosing a basepoint identifies the finite-moment Wasserstein space with the finite-distance
component anchored at its Dirac law. The underlying probability measure is unchanged. -/
def equivComponent (x₀ : X) : WassersteinSpace p X ≃ WassersteinComponent p (diracProba x₀) where
  toFun μ := WassersteinComponent.mk (μ : ProbabilityMeasure X)
    ((hasFiniteMoment_iff_wassersteinEDist_dirac_ne_top measurable_edist x₀ _).1
      (hasFiniteMoment μ))
  invFun μ := mk (WassersteinComponent.toProbabilityMeasure μ)
    ((hasFiniteMoment_iff_wassersteinEDist_dirac_ne_top measurable_edist x₀ _).2
      (WassersteinComponent.wassersteinEDist_anchor_ne_top μ))
  left_inv _ := ext (rfl)
  right_inv _ := WassersteinComponent.ext (rfl)

@[simp]
theorem coe_equivComponent (x₀ : X) (μ : WassersteinSpace p X) :
    WassersteinComponent.toProbabilityMeasure (equivComponent x₀ μ) =
      (μ : ProbabilityMeasure X) :=
  (rfl)

@[simp]
theorem coe_equivComponent_symm (x₀ : X) (μ : WassersteinComponent p (diracProba x₀)) :
    toProbabilityMeasure ((equivComponent x₀).symm μ) =
      WassersteinComponent.toProbabilityMeasure μ :=
  (rfl)

/-- The identification with a Dirac-anchored component is measurable: it does not change the
underlying probability measure, and both sides carry the subtype measurable structure. -/
theorem measurable_equivComponent (x₀ : X) :
    Measurable (equivComponent (p := p) x₀) :=
  measurable_toProbabilityMeasure.subtype_mk

/-- The inverse of the identification with a Dirac-anchored component is measurable. -/
theorem measurable_equivComponent_symm (x₀ : X) :
    Measurable (equivComponent (p := p) x₀).symm :=
  WassersteinComponent.measurable_toProbabilityMeasure.subtype_mk

end MetricGround

section PseudoMetric

variable [MeasurableSpace X] [PseudoMetricSpace X] [StandardBorelSpace X]

/-- Two finite-moment laws are at finite Wasserstein distance. -/
theorem wassersteinEDist_ne_top
    (hd : Measurable fun z : X × X ↦ edist z.1 z.2) (hp : 1 ≤ p)
    (μ ν : WassersteinSpace p X) :
    wassersteinEDist p
      ((μ : ProbabilityMeasure X) : Measure X) ((ν : ProbabilityMeasure X) : Measure X) ≠ ∞ := by
  obtain ⟨x₀, _⟩ := hasFiniteMoment_def.1 μ.2
  have hleft : wassersteinEDist p
      ((μ : ProbabilityMeasure X) : Measure X) (Measure.dirac x₀) ≠ ∞ := by
    rw [wassersteinEDist_comm hd]
    exact (hasFiniteMoment_iff_wassersteinEDist_dirac_ne_top hd x₀ _).1 μ.2
  have hright : wassersteinEDist p
      (Measure.dirac x₀) ((ν : ProbabilityMeasure X) : Measure X) ≠ ∞ := by
    exact (hasFiniteMoment_iff_wassersteinEDist_dirac_ne_top hd x₀ _).1 ν.2
  apply ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hleft, hright⟩)
  exact wassersteinEDist_triangle hd hp
    ((μ : ProbabilityMeasure X) : Measure X) (Measure.dirac x₀)
    ((ν : ProbabilityMeasure X) : Measure X)

/-- The Wasserstein extended distance equips finite-moment laws with a pseudoemetric space
structure whenever the ground distance is measurable and `1 ≤ p`. -/
@[instance_reducible]
noncomputable def pseudoEMetricSpace
    (hd : Measurable fun z : X × X ↦ edist z.1 z.2) (hp : 1 ≤ p) :
    PseudoEMetricSpace (WassersteinSpace p X) :=
  PseudoEMetricSpace.ofEDist
    (fun μ ν ↦ wassersteinEDist p
      ((μ : ProbabilityMeasure X) : Measure X) ((ν : ProbabilityMeasure X) : Measure X))
    (fun μ ↦ wassersteinEDist_self p ((μ : ProbabilityMeasure X) : Measure X))
    (fun μ ν ↦ wassersteinEDist_comm hd p
      ((μ : ProbabilityMeasure X) : Measure X) ((ν : ProbabilityMeasure X) : Measure X))
    (fun μ ν ρ ↦ wassersteinEDist_triangle hd hp
      ((μ : ProbabilityMeasure X) : Measure X) ((ν : ProbabilityMeasure X) : Measure X)
      ((ρ : ProbabilityMeasure X) : Measure X))

variable [BorelSpace X] [SecondCountableTopology X] [Fact (1 ≤ p)]

/-- The canonical Wasserstein pseudoemetric on finite-moment laws when the ground distance is
Borel measurable. -/
noncomputable instance instPseudoEMetricSpace : PseudoEMetricSpace (WassersteinSpace p X) :=
  pseudoEMetricSpace measurable_edist Fact.out

/-- The extended distance on finite-moment laws is their Wasserstein distance. -/
@[simp]
theorem edist_def (μ ν : WassersteinSpace p X) :
    edist μ ν = wassersteinEDist p
      ((μ : ProbabilityMeasure X) : Measure X) ((ν : ProbabilityMeasure X) : Measure X) :=
  (rfl)

/-- Finite-moment laws carry the real-valued Wasserstein pseudometric. -/
noncomputable instance instPseudoMetricSpace : PseudoMetricSpace (WassersteinSpace p X) :=
  PseudoEMetricSpace.toPseudoMetricSpace fun μ ν ↦ by
    rw [edist_def]
    exact wassersteinEDist_ne_top measurable_edist Fact.out μ ν

/-- The distance on finite-moment laws is the real value of the Wasserstein extended distance. -/
@[simp]
theorem dist_def (μ ν : WassersteinSpace p X) :
    dist μ ν = (wassersteinEDist p
      ((μ : ProbabilityMeasure X) : Measure X) ((ν : ProbabilityMeasure X) : Measure X)).toReal :=
  (rfl)

end PseudoMetric

section EquivMetric

variable [MeasurableSpace X] [PseudoMetricSpace X] [StandardBorelSpace X] [BorelSpace X]
  [SecondCountableTopology X] [Fact (1 ≤ p)]

/-- The identification with a Dirac-anchored component preserves the Wasserstein extended
distance, since it does not change the underlying probability measure. -/
theorem edist_equivComponent (x₀ : X) (μ ν : WassersteinSpace p X) :
    edist (equivComponent x₀ μ) (equivComponent x₀ ν) = edist μ ν := by
  rw [WassersteinComponent.edist_def, edist_def, coe_equivComponent, coe_equivComponent]

/-- Choosing a basepoint identifies `WassersteinSpace p X` isometrically with the finite-distance
component anchored at the Dirac law of that basepoint. -/
theorem isometry_equivComponent (x₀ : X) : Isometry (equivComponent (p := p) x₀) :=
  edist_equivComponent x₀

/-- The identification with a Dirac-anchored component preserves the real-valued Wasserstein
distance. -/
theorem dist_equivComponent (x₀ : X) (μ ν : WassersteinSpace p X) :
    dist (equivComponent x₀ μ) (equivComponent x₀ ν) = dist μ ν :=
  (isometry_equivComponent x₀).dist_eq μ ν

end EquivMetric

section Metric

variable [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [CompleteSpace X] [Fact (1 ≤ p)]

/-- On a Polish metric ground space, the Wasserstein pseudometric on finite-moment laws is a
metric. -/
noncomputable instance instMetricSpace : MetricSpace (WassersteinSpace p X) where
  toPseudoMetricSpace := inferInstance
  eq_of_dist_eq_zero {μ ν} h := by
    have hp : (1 : ℝ≥0∞) ≤ p := Fact.out
    apply ext
    apply ProbabilityMeasure.toMeasure_injective
    refine eq_of_wassersteinEDist_eq_zero (ne_of_gt (zero_lt_one.trans_le hp)) _ _ ?_
    rw [← edist_def, edist_dist, h]
    simp

end Metric

end WassersteinSpace

end TauCeti
