/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.Graphon.Basic
public import TauCeti.Order.Partition.Finpartition
import Mathlib.Data.Setoid.Partition

/-!
# Step graphons

A step graphon is specified by a measurable finite partition of its probability carrier and a
symmetric matrix of values in `[0, 1]`, indexed by the parts.  The resulting graphon is constant
on every rectangle cut out by the partition.

The definition uses Mathlib's `Finpartition` directly.  Its value is written as a finite sum of
indicators of the measurable rectangles.  Pairwise disjointness and coverage of the partition
then show that exactly one summand is nonzero at every point.  This presentation makes joint
measurability immediate and does not choose a distinguished index for each point of the carrier.

## Main definitions

* `TauCeti.DenseGraphLimits.stepGraphon` is the graphon associated to a measurable finite
  partition and a symmetric matrix of block values.

## Main results

* `TauCeti.DenseGraphLimits.stepGraphon_apply` evaluates the graphon on a specified block;
* `TauCeti.DenseGraphLimits.stepGraphon_inj` says that, for a fixed partition, two step graphons
  are equal exactly when their block values agree;
* `TauCeti.DenseGraphLimits.stepGraphon_const` identifies a constant block matrix with the
  constant graphon.

## References

* Roadmap: `TauCetiRoadmap/DenseGraphLimits/README.md`, Layer 2 — the block-constant
  `stepGraphon`, which is the carrier for `stepGraphonAvg` and the Frieze--Kannan weak regularity
  output.
* L. Lovász, *Large Networks and Graph Limits*, AMS Colloquium Publications 60 (2012), §9.2.
-/

public section

noncomputable section

open Set

namespace TauCeti

namespace DenseGraphLimits

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
  [MeasureTheory.IsProbabilityMeasure μ]

section StepValue

variable (P : Finpartition (Set.univ : Set Ω))

omit [MeasurableSpace Ω] in
/-- Every point of the carrier belongs to one of the parts of a partition of `Set.univ`. -/
private theorem exists_part (x : Ω) : ∃ p : P.parts, x ∈ (p : Set Ω) := by
  obtain ⟨p, ⟨hp, hxp⟩, _⟩ := P.isPartition_parts.2 x
  exact ⟨⟨p, hp⟩, hxp⟩

/-- The finite rectangle-indicator sum underlying a step graphon. -/
private def stepValue (val : P.parts → P.parts → Set.Icc (0 : ℝ) 1) (x y : Ω) : ℝ :=
  ∑ p : P.parts, ∑ q : P.parts,
    ((p : Set Ω) ×ˢ (q : Set Ω)).indicator (fun _ => (val p q : ℝ)) (x, y)

omit [MeasurableSpace Ω] in
/-- On a specified rectangle, the finite indicator sum has the prescribed block value. -/
private theorem stepValue_apply (val : P.parts → P.parts → Set.Icc (0 : ℝ) 1)
    {p q : P.parts} {x y : Ω} (hx : x ∈ (p : Set Ω)) (hy : y ∈ (q : Set Ω)) :
    stepValue P val x y = (val p q : ℝ) := by
  classical
  rw [stepValue, Fintype.sum_eq_single p]
  · rw [Fintype.sum_eq_single q]
    · simp [hx, hy]
    · intro q' hq'
      have hy' : y ∉ (q' : Set Ω) := by
        intro hy'
        apply hq'
        apply Subtype.ext
        exact P.disjoint.elim q'.property q.property (not_disjoint_iff.2 ⟨y, hy', hy⟩)
      simp [hy']
  · intro p' hp'
    have hx' : x ∉ (p' : Set Ω) := by
      intro hx'
      apply hp'
      apply Subtype.ext
      exact P.disjoint.elim p'.property p.property (not_disjoint_iff.2 ⟨x, hx', hx⟩)
    simp [hx']

end StepValue

/-- The step graphon associated to a measurable finite partition and a symmetric matrix of block
values in `[0, 1]`.

The matrix is indexed by the subtype of parts of `P`; consequently it has no entries unrelated to
an actual block of the partition.  Use `stepGraphon_apply` as the evaluation rule. -/
def stepGraphon (P : Finpartition (Set.univ : Set Ω))
    (hP : ∀ p ∈ P.parts, MeasurableSet p)
    (val : P.parts → P.parts → Set.Icc (0 : ℝ) 1) (hsymm : ∀ p q, val p q = val q p) :
    Graphon Ω μ where
  toFun := stepValue P val
  symm' x y := by
    obtain ⟨p, hxp⟩ := exists_part P x
    obtain ⟨q, hyq⟩ := exists_part P y
    rw [stepValue_apply P val hxp hyq, stepValue_apply P val hyq hxp, hsymm]
  meas' := by
    apply Finset.measurable_sum
    intro p _
    apply Finset.measurable_sum
    intro q _
    exact measurable_const.indicator ((hP p p.property).prod (hP q q.property))
  bdd' := ⟨1, fun x y => by
    obtain ⟨p, hxp⟩ := exists_part P x
    obtain ⟨q, hyq⟩ := exists_part P y
    rw [stepValue_apply P val hxp hyq, abs_of_nonneg (val p q).property.1]
    exact (val p q).property.2⟩
  mem01' x y := by
    obtain ⟨p, hxp⟩ := exists_part P x
    obtain ⟨q, hyq⟩ := exists_part P y
    rw [stepValue_apply P val hxp hyq]
    exact (val p q).property

/-- A step graphon takes its prescribed value on each rectangle of the partition. -/
theorem stepGraphon_apply (P : Finpartition (Set.univ : Set Ω))
    (hP : ∀ p ∈ P.parts, MeasurableSet p)
    (val : P.parts → P.parts → Set.Icc (0 : ℝ) 1) (hsymm : ∀ p q, val p q = val q p)
    {p q : P.parts} {x y : Ω} (hx : x ∈ (p : Set Ω)) (hy : y ∈ (q : Set Ω)) :
    stepGraphon (μ := μ) P hP val hsymm x y = (val p q : ℝ) :=
  stepValue_apply P val hx hy

/-- Two step graphons on a fixed partition are equal exactly when their block matrices agree. -/
@[simp]
theorem stepGraphon_inj (P : Finpartition (Set.univ : Set Ω))
    (hP : ∀ p ∈ P.parts, MeasurableSet p)
    (val val' : P.parts → P.parts → Set.Icc (0 : ℝ) 1)
    (hsymm : ∀ p q, val p q = val q p) (hsymm' : ∀ p q, val' p q = val' q p) :
    stepGraphon (μ := μ) P hP val hsymm = stepGraphon (μ := μ) P hP val' hsymm' ↔ val = val' := by
  constructor
  · intro h
    funext p q
    obtain ⟨x, hxp⟩ := Set.nonempty_iff_ne_empty.mpr (P.ne_bot p.property)
    obtain ⟨y, hyq⟩ := Set.nonempty_iff_ne_empty.mpr (P.ne_bot q.property)
    apply Subtype.ext
    simpa only [stepGraphon_apply P hP val hsymm hxp hyq,
      stepGraphon_apply P hP val' hsymm' hxp hyq] using
      congrArg (fun W : Graphon Ω μ => W x y) h
  · rintro rfl
    rfl

/-- A step graphon whose block matrix is constant is the corresponding constant graphon. -/
@[simp]
theorem stepGraphon_const (P : Finpartition (Set.univ : Set Ω))
    (hP : ∀ p ∈ P.parts, MeasurableSet p) (c : Set.Icc (0 : ℝ) 1) :
    stepGraphon (μ := μ) P hP (fun _ _ => c) (fun _ _ => rfl) = Graphon.const μ c := by
  ext x y
  obtain ⟨p, hxp⟩ := exists_part P x
  obtain ⟨q, hyq⟩ := exists_part P y
  rw [stepGraphon_apply P hP (fun _ _ => c) (fun _ _ => rfl) hxp hyq,
    Graphon.const_apply]

end DenseGraphLimits

end TauCeti
