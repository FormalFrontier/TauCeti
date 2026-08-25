/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.Topology.Instances.EReal.Lemmas
public import Mathlib.Topology.Semicontinuity.Basic
public import TauCeti.Data.EReal.Operations
public import TauCeti.MeasureTheory.OptimalTransport.CTransform.Basic
public import TauCeti.Topology.Semicontinuity.Compact

/-!
# Attainment and lower semicontinuity of the infimal `c`-transform

The upper-semicontinuity half of the topological theory of the infimal `c`-transform lives in
`TauCeti.MeasureTheory.OptimalTransport.CTransform.Basic`: an infimum of upper-semicontinuous
sections is upper semicontinuous, with no compactness anywhere. This file proves the other
half, the compact regime.

The engine is a pair of value-function facts proved in
`TauCeti/Topology/Semicontinuity/Compact.lean`, stated there for arbitrary spaces: if
`g : X × Y → EReal` is jointly lower semicontinuous, then `y ↦ ⨅ x, g x y` is lower
semicontinuous whenever `X` is compact (`TauCeti.lowerSemicontinuous_ciInf_of_isCompact`), and
if moreover every section is lower semicontinuous, the infimum is attained
(`TauCeti.exists_ciInf_eq_of_isCompact`).

Applied to the transform integrand `(x, y) ↦ (c (x, y) : EReal) - φ x`, this gives the compact
regime for Kantorovich potentials: against a jointly lower-semicontinuous cost and an
upper-semicontinuous potential, the infimal `c`-transform is lower semicontinuous
(`TauCeti.lowerSemicontinuous_cTransform_of_lowerSemicontinuous`), while its defining infimum
is attained over a compact nonempty source already under the weaker assumption that every cost
section is lower semicontinuous
(`TauCeti.exists_cTransform_eq_of_lowerSemicontinuous`);
with both halves the transform is continuous
(`TauCeti.continuous_cTransform_of_continuous_of_lowerSemicontinuous`), and either
semicontinuity regime yields Borel measurability (`TauCeti.measurable_cTransform_*`). Every
statement has a symmetric counterpart for `TauCeti.cTransformSymm`.

## Main statements

* `TauCeti.lowerSemicontinuous_cTransform_of_lowerSemicontinuous`,
  `TauCeti.exists_cTransform_eq_of_lowerSemicontinuous`,
  `TauCeti.continuous_cTransform_of_continuous_of_lowerSemicontinuous`;
* `TauCeti.measurable_cTransform_of_lowerSemicontinuous`,
  `TauCeti.measurable_cTransform_of_continuous`.

## References

* C. Villani, *Optimal Transport: Old and New*, Springer 2009, Chapter 2: the regularity and
  stability facts on `c`-transforms in this compact/lower-semicontinuous regime.

This is Layer 2, item 2 of the optimal-transport roadmap.
-/

public section

noncomputable section

open Set Filter
open scoped Topology

namespace TauCeti

universe u v

variable {X : Type u} {Y : Type v} {c : X × Y → ℝ} {φ : X → EReal} {ψ : Y → EReal}

/-- A function into `EReal` that is both lower and upper semicontinuous is continuous: at each
point its value is squeezed between the liminf and the limsup along the neighborhood filter,
and those two extremes coincide. -/
private theorem continuous_of_lowerSemicontinuous_upperSemicontinuous {α : Type*}
    [TopologicalSpace α] {f : α → EReal} (hl : LowerSemicontinuous f)
    (hu : UpperSemicontinuous f) : Continuous f :=
  continuous_iff_continuousAt.2 fun x =>
    tendsto_of_le_liminf_of_limsup_le (lowerSemicontinuous_iff_le_liminf.1 hl x)
      (upperSemicontinuous_iff_limsup_le.1 hu x)

/-! ### Application to the transform -/

variable [TopologicalSpace X] [TopologicalSpace Y]

omit [TopologicalSpace Y] in
/-- For a fixed target point, subtracting an upper-semicontinuous source potential from a
lower-semicontinuous cost section keeps the section of the transform integrand lower
semicontinuous. -/
private theorem lowerSemicontinuous_section_sub_of_upperSemicontinuous {y : Y}
    (hc : LowerSemicontinuous fun x => ((c (x, y) : ℝ) : EReal))
    (hφ : UpperSemicontinuous φ) :
    LowerSemicontinuous fun x => ((c (x, y) : ℝ) : EReal) - φ x := by
  refine hc.add' ?_ ?_
  · exact continuous_neg.comp_upperSemicontinuous_antitone hφ EReal.neg_strictAnti.antitone
  · intro _
    exact EReal.continuousAt_add (Or.inl (by simp)) (Or.inl (by simp))

/-- Against a jointly lower-semicontinuous real cost, subtracting an upper-semicontinuous
potential on the source keeps the integrand of the `c`-transform jointly lower
semicontinuous. The potential may take the values `±∞`; subtraction by them makes the
integrand constant. -/
theorem lowerSemicontinuous_coe_sub_of_upperSemicontinuous
    (hc : LowerSemicontinuous fun z : X × Y => ((c z : ℝ) : EReal))
    (hφ : UpperSemicontinuous φ) :
    LowerSemicontinuous fun z : X × Y => ((c z : ℝ) : EReal) - φ z.1 := by
  refine hc.add' ?_ ?_
  · refine continuous_neg.comp_upperSemicontinuous_antitone
      (Semicontinuous.comp (r := fun (a : X) (b : EReal) => φ a < b) hφ continuous_fst)
      EReal.neg_strictAnti.antitone
  · intro z
    exact EReal.continuousAt_add (Or.inl (by simp)) (Or.inl (by simp))

omit [TopologicalSpace Y] in
/-- If every cost section is lower semicontinuous and the potential is upper semicontinuous,
the infimum defining the `c`-transform is attained at some source point, provided the source
space is compact and nonempty. No joint lower semicontinuity of the cost is needed. -/
theorem exists_cTransform_eq_of_lowerSemicontinuous [CompactSpace X] (hne : Nonempty X)
    (hc : ∀ y', LowerSemicontinuous fun x' => ((c (x', y') : ℝ) : EReal))
    (hφ : UpperSemicontinuous φ) (y : Y) :
    ∃ x : X, cTransform c φ y = ((c (x, y) : ℝ) : EReal) - φ x := by
  obtain ⟨x, hx⟩ :=
    exists_ciInf_eq_of_isCompact (g := fun z => ((c z : ℝ) : EReal) - φ z.1) hne
      (fun y' ↦ lowerSemicontinuous_section_sub_of_upperSemicontinuous (hc y') hφ) y
  refine ⟨x, ?_⟩
  rw [cTransform_apply]
  exact hx

/-- If the cost is jointly lower semicontinuous and the potential is upper semicontinuous,
the infimal `c`-transform against a compact source space is lower semicontinuous. Together
with the upper semicontinuity of `CTransform.Basic` this yields continuity under continuous
cost sections. -/
theorem lowerSemicontinuous_cTransform_of_lowerSemicontinuous [CompactSpace X]
    (hc : LowerSemicontinuous fun z : X × Y => ((c z : ℝ) : EReal))
    (hφ : UpperSemicontinuous φ) :
    LowerSemicontinuous (cTransform c φ) := by
  have hEq : cTransform c φ = fun y => ⨅ x, ((c (x, y) : ℝ) : EReal) - φ x :=
    funext (cTransform_apply c φ)
  rw [hEq]
  exact lowerSemicontinuous_ciInf_of_isCompact
    (lowerSemicontinuous_coe_sub_of_upperSemicontinuous hc hφ)

/-- The compact/lower-semicontinuous regime in which the infimal `c`-transform is continuous:
the cost sections are continuous and the cost is jointly lower semicontinuous, so the upper
semicontinuity of `CTransform.Basic` combines with
`lowerSemicontinuous_cTransform_of_lowerSemicontinuous`. -/
theorem continuous_cTransform_of_continuous_of_lowerSemicontinuous [CompactSpace X]
    (hcsec : ∀ x, Continuous fun y => c (x, y))
    (hc : LowerSemicontinuous fun z : X × Y => ((c z : ℝ) : EReal))
    (hφ : UpperSemicontinuous φ) :
    Continuous (cTransform c φ) :=
  continuous_of_lowerSemicontinuous_upperSemicontinuous
    (lowerSemicontinuous_cTransform_of_lowerSemicontinuous hc hφ)
    (upperSemicontinuous_cTransform_of_continuous hcsec φ)

/-- In the compact/lower-semicontinuous regime the `c`-transform is Borel measurable. -/
theorem measurable_cTransform_of_lowerSemicontinuous [CompactSpace X]
    [MeasurableSpace Y] [OpensMeasurableSpace Y]
    (hc : LowerSemicontinuous fun z : X × Y => ((c z : ℝ) : EReal))
    (hφ : UpperSemicontinuous φ) :
    Measurable (cTransform c φ) :=
  (lowerSemicontinuous_cTransform_of_lowerSemicontinuous hc hφ).measurable

omit [TopologicalSpace X] in
/-- With continuous cost sections the `c`-transform is Borel measurable, on an arbitrary
source space and with no compactness. -/
theorem measurable_cTransform_of_continuous
    [MeasurableSpace Y] [OpensMeasurableSpace Y]
    (hcsec : ∀ x, Continuous fun y => c (x, y)) (φ : X → EReal) :
    Measurable (cTransform c φ) :=
  (upperSemicontinuous_cTransform_of_continuous hcsec φ).measurable

/-! ### The symmetric transform -/

omit [TopologicalSpace X] in
/-- If every cost section is lower semicontinuous and the potential is upper semicontinuous,
the infimum defining the symmetric `c`-transform is attained at some target point, provided
the target space is compact and nonempty. No joint lower semicontinuity of the cost is
needed. -/
theorem exists_cTransformSymm_eq_of_lowerSemicontinuous [CompactSpace Y] (hne : Nonempty Y)
    (hc : ∀ x', LowerSemicontinuous fun y' => ((c (x', y') : ℝ) : EReal))
    (hψ : UpperSemicontinuous ψ) (x : X) :
    ∃ y : Y, cTransformSymm c ψ x = ((c (x, y) : ℝ) : EReal) - ψ y := by
  obtain ⟨y, hy⟩ :=
    exists_cTransform_eq_of_lowerSemicontinuous (c := fun z : Y × X => c (z.2, z.1)) hne hc hψ x
  refine ⟨y, ?_⟩
  rw [cTransform_apply (fun z : Y × X => c (z.2, z.1)) ψ x] at hy
  rw [cTransformSymm_apply, hy]

/-- If the cost is jointly lower semicontinuous and the potential is upper semicontinuous,
the symmetric `c`-transform against a compact target space is lower semicontinuous. -/
theorem lowerSemicontinuous_cTransformSymm_of_lowerSemicontinuous [CompactSpace Y]
    (hc : LowerSemicontinuous fun z : X × Y => ((c z : ℝ) : EReal))
    (hψ : UpperSemicontinuous ψ) :
    LowerSemicontinuous (cTransformSymm c ψ) := by
  rw [cTransformSymm_eq_cTransform]
  exact lowerSemicontinuous_cTransform_of_lowerSemicontinuous
    (c := fun z : Y × X => c (z.2, z.1)) (Semicontinuous.comp hc continuous_swap) hψ

/-- The compact/lower-semicontinuous regime in which the symmetric `c`-transform is
continuous. -/
theorem continuous_cTransformSymm_of_continuous_of_lowerSemicontinuous [CompactSpace Y]
    (hcsec : ∀ y, Continuous fun x => c (x, y))
    (hc : LowerSemicontinuous fun z : X × Y => ((c z : ℝ) : EReal))
    (hψ : UpperSemicontinuous ψ) :
    Continuous (cTransformSymm c ψ) := by
  rw [cTransformSymm_eq_cTransform]
  exact continuous_cTransform_of_continuous_of_lowerSemicontinuous
    (c := fun z : Y × X => c (z.2, z.1))
    hcsec (Semicontinuous.comp hc continuous_swap) hψ

/-- In the compact/lower-semicontinuous regime the symmetric `c`-transform is Borel
measurable. -/
theorem measurable_cTransformSymm_of_lowerSemicontinuous [CompactSpace Y]
    [MeasurableSpace X] [OpensMeasurableSpace X]
    (hc : LowerSemicontinuous fun z : X × Y => ((c z : ℝ) : EReal))
    (hψ : UpperSemicontinuous ψ) :
    Measurable (cTransformSymm c ψ) :=
  (lowerSemicontinuous_cTransformSymm_of_lowerSemicontinuous hc hψ).measurable

omit [TopologicalSpace Y] in
/-- With continuous cost sections the symmetric `c`-transform is Borel measurable. -/
theorem measurable_cTransformSymm_of_continuous
    [MeasurableSpace X] [OpensMeasurableSpace X]
    (hcsec : ∀ y, Continuous fun x => c (x, y)) (ψ : Y → EReal) :
    Measurable (cTransformSymm c ψ) :=
  (upperSemicontinuous_cTransformSymm_of_continuous hcsec ψ).measurable

end TauCeti
