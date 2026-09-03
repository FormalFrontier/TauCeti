/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Basic

/-!
# Finite-distance Wasserstein spaces

The Wasserstein distance can be infinite, even between probability measures. This file isolates
the parts on which it is finite and hence defines an ordinary pseudometric:

* `TauCeti.WassersteinComponent p μ₀` consists of the probability measures at finite
  `p`-Wasserstein distance from the anchor `μ₀`;
* `TauCeti.WassersteinSpace p X` consists of the probability measures on `X` with finite
  `p`-moment.

On a standard Borel extended pseudometric space with measurable ground distance, every anchored
component carries the Wasserstein pseudometric. On an ordinary pseudometric space, finite moment
about one point is equivalent to finite Wasserstein distance from the Dirac mass at any point.
Consequently `WassersteinSpace p X` is canonically equivalent, after choosing a point `x₀`, to
the component anchored at `δ_[x₀]`, and it carries the same Wasserstein pseudometric without a
basepoint appearing in its definition.

When the ground space is Polish and its distance separates points, both pseudometrics are metrics.
The measurable structures are the subtype structures inherited from `ProbabilityMeasure`; no
second measurable-space instance is introduced. Identifying these measurable structures with the
Borel sigma algebras of the Wasserstein metrics is a separate topological result.

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
canonical subtype structure. -/
@[expose]
def WassersteinComponent [MeasurableSpace X] [PseudoEMetricSpace X]
    (p : ℝ≥0∞) (μ₀ : ProbabilityMeasure X) :=
  {μ : ProbabilityMeasure X //
    wassersteinEDist p (μ₀ : Measure X) (μ : Measure X) ≠ ∞}

/-- Probability measures on `X` with finite `p`-moment. -/
@[expose]
def WassersteinSpace (p : ℝ≥0∞) (X : Type u) [MeasurableSpace X] [PseudoEMetricSpace X] :=
  {μ : ProbabilityMeasure X // HasFiniteMoment p (μ : Measure X)}

namespace WassersteinComponent

section Basic

variable [MeasurableSpace X] [PseudoEMetricSpace X] {μ₀ : ProbabilityMeasure X}

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
    toProbabilityMeasure (⟨μ, hμ⟩ : WassersteinComponent p μ₀) = μ :=
  (rfl)

/-- Membership in an anchored component is exactly finite Wasserstein distance from its anchor. -/
theorem mem_component (μ : WassersteinComponent p μ₀) :
    wassersteinEDist p (μ₀ : Measure X) ((μ : ProbabilityMeasure X) : Measure X) ≠ ∞ :=
  μ.2

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
    exact μ.2
  apply ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hμ, ν.2⟩)
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
    apply ext
    apply ProbabilityMeasure.toMeasure_injective
    have hw : wassersteinEDist p
        ((μ : ProbabilityMeasure X) : Measure X) ((ν : ProbabilityMeasure X) : Measure X) = 0 := by
      rw [← edist_def, edist_dist, h]
      simp
    by_cases hp : p = ∞
    · subst p
      exact (wassersteinEDist_top_eq_zero_iff
        ((μ : ProbabilityMeasure X) : Measure X) ((ν : ProbabilityMeasure X) : Measure X)).1 hw
    · exact (wassersteinEDist_eq_zero_iff
        (ne_of_gt (zero_lt_one.trans_le Fact.out)) hp
        ((μ : ProbabilityMeasure X) : Measure X) ((ν : ProbabilityMeasure X) : Measure X)).1 hw

end Metric

end WassersteinComponent

namespace WassersteinSpace

section Basic

variable [MeasurableSpace X] [PseudoEMetricSpace X]

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
    toProbabilityMeasure (⟨μ, hμ⟩ : WassersteinSpace p X) = μ :=
  (rfl)

/-- A law in `WassersteinSpace p X` has finite `p`-moment. -/
theorem hasFiniteMoment (μ : WassersteinSpace p X) :
    HasFiniteMoment p ((μ : ProbabilityMeasure X) : Measure X) :=
  μ.2

end Basic

section MetricGround

variable [MeasurableSpace X] [PseudoMetricSpace X] [BorelSpace X]

/-- On an ordinary pseudometric space, finite moment can be checked at any prescribed basepoint. -/
theorem hasFiniteMoment_iff_memLp_edist (x₀ : X) (μ : ProbabilityMeasure X) :
    HasFiniteMoment p (μ : Measure X) ↔ MemLp (fun x ↦ edist x₀ x) p (μ : Measure X) := by
  constructor
  · intro h
    exact h.memLp measurable_edist_right.aestronglyMeasurable
  · exact fun h ↦ hasFiniteMoment_def.2 ⟨x₀, h⟩

variable [SecondCountableTopology X]

/-- On an ordinary pseudometric space, finite moment is equivalent to finite Wasserstein distance
from the Dirac law at any prescribed basepoint. -/
theorem hasFiniteMoment_iff_wassersteinEDist_dirac_ne_top (x₀ : X)
    (μ : ProbabilityMeasure X) :
    HasFiniteMoment p (μ : Measure X) ↔
      wassersteinEDist p (Measure.dirac x₀) (μ : Measure X) ≠ ∞ := by
  rw [hasFiniteMoment_iff_memLp_edist x₀]
  exact memLp_edist_iff_wassersteinEDist_dirac_ne_top measurable_edist x₀ μ

/-- Choosing a basepoint identifies the finite-moment Wasserstein space with the finite-distance
component anchored at its Dirac law. The underlying probability measure is unchanged. -/
def equivComponent (x₀ : X) :
    WassersteinSpace p X ≃
      WassersteinComponent p (⟨Measure.dirac x₀, inferInstance⟩ : ProbabilityMeasure X) where
  toFun μ := ⟨μ.1, (hasFiniteMoment_iff_wassersteinEDist_dirac_ne_top x₀ μ.1).1 μ.2⟩
  invFun μ := ⟨μ.1, (hasFiniteMoment_iff_wassersteinEDist_dirac_ne_top x₀ μ.1).2 μ.2⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

@[simp]
theorem coe_equivComponent (x₀ : X) (μ : WassersteinSpace p X) :
    WassersteinComponent.toProbabilityMeasure (equivComponent x₀ μ) =
      (μ : ProbabilityMeasure X) :=
  (rfl)

end MetricGround

section PseudoMetric

variable [MeasurableSpace X] [PseudoMetricSpace X] [StandardBorelSpace X]

/-- Two finite-moment laws are at finite Wasserstein distance. -/
theorem wassersteinEDist_ne_top
    (hd : Measurable fun z : X × X ↦ edist z.1 z.2) (hp : 1 ≤ p)
    (μ ν : WassersteinSpace p X) :
    wassersteinEDist p
      ((μ : ProbabilityMeasure X) : Measure X) ((ν : ProbabilityMeasure X) : Measure X) ≠ ∞ := by
  obtain ⟨x₀, hμ⟩ := hasFiniteMoment_def.1 μ.2
  have hν : MemLp (fun x ↦ edist x₀ x) p ((ν : ProbabilityMeasure X) : Measure X) :=
    ν.2.memLp (hd.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  have hleft : wassersteinEDist p
      ((μ : ProbabilityMeasure X) : Measure X) (Measure.dirac x₀) ≠ ∞ := by
    rw [wassersteinEDist_comm hd, wassersteinEDist_dirac_left hd]
    exact hμ.eLpNorm_ne_top
  have hright : wassersteinEDist p
      (Measure.dirac x₀) ((ν : ProbabilityMeasure X) : Measure X) ≠ ∞ := by
    rw [wassersteinEDist_dirac_left hd]
    exact hν.eLpNorm_ne_top
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
theorem dist_def (μ ν : WassersteinSpace p X) :
    dist μ ν = (wassersteinEDist p
      ((μ : ProbabilityMeasure X) : Measure X) ((ν : ProbabilityMeasure X) : Measure X)).toReal :=
  (rfl)

end PseudoMetric

section Metric

variable [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [CompleteSpace X] [Fact (1 ≤ p)]

/-- On a Polish metric ground space, the Wasserstein pseudometric on finite-moment laws is a
metric. -/
noncomputable instance instMetricSpace : MetricSpace (WassersteinSpace p X) where
  toPseudoMetricSpace := inferInstance
  eq_of_dist_eq_zero {μ ν} h := by
    apply ext
    apply ProbabilityMeasure.toMeasure_injective
    have hw : wassersteinEDist p
        ((μ : ProbabilityMeasure X) : Measure X) ((ν : ProbabilityMeasure X) : Measure X) = 0 := by
      rw [← edist_def, edist_dist, h]
      simp
    by_cases hp : p = ∞
    · subst p
      exact (wassersteinEDist_top_eq_zero_iff
        ((μ : ProbabilityMeasure X) : Measure X) ((ν : ProbabilityMeasure X) : Measure X)).1 hw
    · exact (wassersteinEDist_eq_zero_iff
        (ne_of_gt (zero_lt_one.trans_le Fact.out)) hp
        ((μ : ProbabilityMeasure X) : Measure X) ((ν : ProbabilityMeasure X) : Measure X)).1 hw

end Metric

end WassersteinSpace

end TauCeti
