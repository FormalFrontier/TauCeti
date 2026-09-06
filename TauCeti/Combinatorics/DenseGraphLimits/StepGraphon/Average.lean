/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.Kernel.Integral
public import TauCeti.Combinatorics.DenseGraphLimits.StepGraphon.Basic
public import Mathlib.MeasureTheory.Integral.Average

/-!
# Block-averaged step graphons

This file specializes `stepGraphon` to the matrix of averages of a graphon over the rectangles
of a measurable finite partition.  This is the step graphon used by the Frieze--Kannan weak
regularity argument: on a block `p ×ˢ q`, its value is the Mathlib set average of the original
graphon over that block.

The set-average convention matters for strict graphon representatives.  A nonempty partition
part may have measure zero, and Mathlib assigns average zero to a null rectangle.  Thus
`stepGraphonAvg` is everywhere `[0, 1]`-valued without choosing arbitrary values on null blocks.
The block-integral theorem below shows that this convention does not change any weighted block
contribution.

## Main definitions

* `TauCeti.DenseGraphLimits.stepGraphonAvg` is the block-average step graphon.

## Main results

* `TauCeti.DenseGraphLimits.stepGraphonAvg_apply` is its pointwise block formula;
* `TauCeti.DenseGraphLimits.stepGraphonAvg_apply_of_measure_eq_zero_left` and
  `TauCeti.DenseGraphLimits.stepGraphonAvg_apply_of_measure_eq_zero_right` record the null-cell
  convention;
* `TauCeti.DenseGraphLimits.stepGraphonAvg_rectIntegral` says block averaging preserves the
  integral on every partition rectangle;
* `TauCeti.DenseGraphLimits.stepGraphonAvg_idem` says block averaging is strictly idempotent;
* `TauCeti.DenseGraphLimits.stepGraphonAvg_stepGraphon_apply` verifies that a non-null constant
  block is recovered exactly.

## References

* L. Lovász, *Large Networks and Graph Limits*, AMS Colloquium Publications 60 (2012), §9.2.
* Roadmap: `TauCetiRoadmap/DenseGraphLimits/README.md`, Layer 2 — `stepGraphonAvg` and the
  null-cell validation gate preceding graphon partition energy.
* The null-cell convention and its compatibility with Mathlib set averages follow
  `Graphon/RegularityFinpartition.lean` in `cameronfreer/graphon` (Apache 2.0) at commit
  `dfd7ecc9b197d8211842935204bcec6051d57863`.
-/

public section

noncomputable section

open MeasureTheory Set

namespace TauCeti

namespace DenseGraphLimits

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

section BlockAverage

variable (P : Finpartition (Set.univ : Set Ω)) (W : Graphon Ω μ)

/-- The average of a graphon over one rectangle of a finite partition, regarded as a point of
`[0, 1]`. -/
private def blockAverage (p q : P.parts) : Set.Icc (0 : ℝ) 1 :=
  ⟨⨍ z in (p : Set Ω) ×ˢ (q : Set Ω), W z.1 z.2 ∂(μ.prod μ),
    average_nonneg fun z => W.nonneg z.1 z.2,
    by
      let s := (p : Set Ω) ×ˢ (q : Set Ω)
      let one : Ω × Ω → ℝ := fun _ => 1
      let f : Ω × Ω → ℝ := fun z => W z.1 z.2
      have hW : IntegrableOn f s (μ.prod μ) :=
        W.toSymmKernel.integrable_uncurry.integrableOn
      have honeInt : IntegrableOn one s (μ.prod μ) :=
        integrableOn_const (C := (1 : ℝ)) (measure_ne_top _ _)
      have hsub : 0 ≤ ⨍ z in s, (one - f) z ∂(μ.prod μ) :=
        average_nonneg fun z => sub_nonneg.mpr (W.le_one z.1 z.2)
      rw [setAverage_sub honeInt hW] at hsub
      have hone : (⨍ z in s, one z ∂(μ.prod μ)) ≤ 1 := by
        by_cases hs : (μ.prod μ) s = 0
        · rw [setAverage_eq]
          simp [measureReal_def, hs]
        · simpa [one] using le_of_eq (setAverage_const hs (measure_ne_top _ _) (1 : ℝ))
      dsimp only [one, f] at hsub hone
      linarith⟩

/-- Rectangle averages of a symmetric graphon are symmetric in the two partition parts. -/
private theorem blockAverage_comm (p q : P.parts) :
    blockAverage P W p q = blockAverage P W q p := by
  apply Subtype.ext
  simp only [blockAverage]
  rw [setAverage_eq, setAverage_eq, measureReal_prod_prod, measureReal_prod_prod,
    mul_comm (μ.real (p : Set Ω)) (μ.real (q : Set Ω))]
  congr 1
  simpa only [SymmKernel.rectIntegral_def, Graphon.coe_toSymmKernel] using
    W.toSymmKernel.rectIntegral_comm μ (p : Set Ω) (q : Set Ω)

end BlockAverage

/-- The block-average step graphon of `W` with respect to a measurable finite partition `P`.

Its value on `p ×ˢ q` is Mathlib's set average of `W` over that rectangle.  In particular its
value is zero when either side of the rectangle has measure zero. -/
def stepGraphonAvg (P : Finpartition (Set.univ : Set Ω))
    (hP : ∀ p ∈ P.parts, MeasurableSet p) (W : Graphon Ω μ) : Graphon Ω μ :=
  stepGraphon (μ := μ) P hP (blockAverage P W) (blockAverage_comm P W)

/-- The block-average step graphon takes the average of `W` over its containing partition
rectangle. -/
theorem stepGraphonAvg_apply (P : Finpartition (Set.univ : Set Ω))
    (hP : ∀ p ∈ P.parts, MeasurableSet p) (W : Graphon Ω μ) {p q : P.parts} {x y : Ω}
    (hx : x ∈ (p : Set Ω)) (hy : y ∈ (q : Set Ω)) :
    stepGraphonAvg (μ := μ) P hP W x y =
      ⨍ z in (p : Set Ω) ×ˢ (q : Set Ω), W z.1 z.2 ∂(μ.prod μ) := by
  rw [stepGraphonAvg, stepGraphon_apply P hP (blockAverage P W) (blockAverage_comm P W) hx hy]
  rfl

/-- On a partition rectangle whose left side is null, the block-average step graphon is zero.

This is not a simp lemma because the partition parts cannot be inferred from its left-hand side. -/
theorem stepGraphonAvg_apply_of_measure_eq_zero_left
    (P : Finpartition (Set.univ : Set Ω)) (hP : ∀ p ∈ P.parts, MeasurableSet p)
    (W : Graphon Ω μ) {p q : P.parts} {x y : Ω} (hp : μ (p : Set Ω) = 0)
    (hx : x ∈ (p : Set Ω)) (hy : y ∈ (q : Set Ω)) :
    stepGraphonAvg (μ := μ) P hP W x y = 0 := by
  rw [stepGraphonAvg_apply P hP W hx hy, setAverage_eq, measureReal_prod_prod]
  simp [hp]

/-- On a partition rectangle whose right side is null, the block-average step graphon is zero.

This is not a simp lemma because the partition parts cannot be inferred from its left-hand side. -/
theorem stepGraphonAvg_apply_of_measure_eq_zero_right
    (P : Finpartition (Set.univ : Set Ω)) (hP : ∀ p ∈ P.parts, MeasurableSet p)
    (W : Graphon Ω μ) {p q : P.parts} {x y : Ω} (hq : μ (q : Set Ω) = 0)
    (hx : x ∈ (p : Set Ω)) (hy : y ∈ (q : Set Ω)) :
    stepGraphonAvg (μ := μ) P hP W x y = 0 := by
  rw [stepGraphonAvg_apply P hP W hx hy, setAverage_eq, measureReal_prod_prod]
  simp [hq]

/-- Block averaging preserves the integral over each rectangle of the partition.  This includes
null rectangles: both sides are then zero under Mathlib's set-average convention. -/
@[simp]
theorem stepGraphonAvg_rectIntegral (P : Finpartition (Set.univ : Set Ω))
    (hP : ∀ p ∈ P.parts, MeasurableSet p) (W : Graphon Ω μ) (p q : P.parts) :
    (stepGraphonAvg (μ := μ) P hP W).toSymmKernel.rectIntegral μ (p : Set Ω) (q : Set Ω) =
      W.toSymmKernel.rectIntegral μ (p : Set Ω) (q : Set Ω) := by
  rw [SymmKernel.rectIntegral_def, SymmKernel.rectIntegral_def]
  calc
    (∫ z in (p : Set Ω) ×ˢ (q : Set Ω),
        stepGraphonAvg (μ := μ) P hP W z.1 z.2 ∂(μ.prod μ)) =
        ∫ _z in (p : Set Ω) ×ˢ (q : Set Ω),
          (⨍ w in (p : Set Ω) ×ˢ (q : Set Ω), W w.1 w.2 ∂(μ.prod μ)) ∂(μ.prod μ) := by
      apply setIntegral_congr_fun ((hP p p.property).prod (hP q q.property))
      intro z hz
      exact stepGraphonAvg_apply P hP W hz.1 hz.2
    _ = ∫ z in (p : Set Ω) ×ˢ (q : Set Ω), W z.1 z.2 ∂(μ.prod μ) :=
      setIntegral_setAverage _ _ _

/-- Block averaging with respect to a fixed partition is strictly idempotent.  This is equality
of strict graphon representatives, not merely almost-everywhere equality: after the first
averaging, every null block already has the canonical value zero. -/
@[simp]
theorem stepGraphonAvg_idem (P : Finpartition (Set.univ : Set Ω))
    (hP : ∀ p ∈ P.parts, MeasurableSet p) (W : Graphon Ω μ) :
    stepGraphonAvg (μ := μ) P hP (stepGraphonAvg (μ := μ) P hP W) =
      stepGraphonAvg (μ := μ) P hP W := by
  apply (stepGraphon_inj P hP
    (blockAverage P (stepGraphonAvg (μ := μ) P hP W)) (blockAverage P W)
    (blockAverage_comm P (stepGraphonAvg (μ := μ) P hP W)) (blockAverage_comm P W)).2
  funext p q
  apply Subtype.ext
  simp only [blockAverage, setAverage_eq]
  congr 1
  simpa only [SymmKernel.rectIntegral_def, Graphon.coe_toSymmKernel] using
    stepGraphonAvg_rectIntegral P hP W p q

/-- Averaging a step graphon recovers its prescribed value on every rectangle with two non-null
sides.  The non-null hypotheses are necessary: the strict null-cell convention replaces the
value on a null rectangle by zero.  This is not a simp lemma because the partition parts cannot be
inferred from its left-hand side. -/
theorem stepGraphonAvg_stepGraphon_apply (P : Finpartition (Set.univ : Set Ω))
    (hP : ∀ p ∈ P.parts, MeasurableSet p)
    (val : P.parts → P.parts → Set.Icc (0 : ℝ) 1) (hsymm : ∀ p q, val p q = val q p)
    {p q : P.parts} {x y : Ω} (hp : μ (p : Set Ω) ≠ 0) (hq : μ (q : Set Ω) ≠ 0)
    (hx : x ∈ (p : Set Ω)) (hy : y ∈ (q : Set Ω)) :
    stepGraphonAvg (μ := μ) P hP (stepGraphon (μ := μ) P hP val hsymm) x y =
      (val p q : ℝ) := by
  rw [stepGraphonAvg_apply P hP (stepGraphon (μ := μ) P hP val hsymm) hx hy]
  calc
    (⨍ z in (p : Set Ω) ×ˢ (q : Set Ω),
        stepGraphon (μ := μ) P hP val hsymm z.1 z.2 ∂(μ.prod μ)) =
        ⨍ _z in (p : Set Ω) ×ˢ (q : Set Ω), (val p q : ℝ) ∂(μ.prod μ) := by
      apply setAverage_congr_fun ((hP p p.property).prod (hP q q.property))
      exact ae_of_all _ fun z hz => stepGraphon_apply P hP val hsymm hz.1 hz.2
    _ = (val p q : ℝ) := by
      apply setAverage_const
      · simpa [Measure.prod_prod] using mul_ne_zero hp hq
      · exact measure_ne_top _ _

end DenseGraphLimits

end TauCeti
