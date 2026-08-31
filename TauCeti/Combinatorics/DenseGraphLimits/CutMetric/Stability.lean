/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.CutMetric.Distance
import TauCeti.Combinatorics.DenseGraphLimits.Kernel.Pullback

/-!
# Stability of graphon cut distance under approximation

The coupling cut distance is stable when either graphon is replaced by a nearby graphon on the
same carrier.  Quantitatively,

`|δ□(U, W) - δ□(U', W')| ≤ ‖U - U'‖□ + ‖W - W'‖□`.

This estimate does not use the triangle inequality for `cutDist`.  Instead, fix a coupling used to
compare `U'` and `W`.  On that coupling, the overlaid difference of `U` and `W` splits into the
pullback of `U - U'` plus the overlaid difference of `U'` and `W`.  The cut-norm triangle
inequality bounds the sum, and invariance under the measure-preserving coordinate projection
identifies the first summand with `‖U - U'‖□`.  Taking the infimum over the same couplings gives the
one-coordinate estimate; symmetry and a second replacement give the displayed bound.

The result is the stability input for the finite-step reduction in the arbitrary-carrier triangle
inequality.  Once graphons have been approximated by finite step graphons, a triangle estimate for
the finite approximants transfers to the original graphons with precisely the two cut-norm errors
recorded here.  Thus no disintegration of an arbitrary intermediate carrier is hidden in this
module.

## Main results

* `TauCeti.DenseGraphLimits.abs_cutDist_sub_left_le_cutNorm` bounds the effect of changing the
  graphon on the left carrier.
* `TauCeti.DenseGraphLimits.abs_cutDist_sub_right_le_cutNorm` is the corresponding bound on the
  right carrier.
* `TauCeti.DenseGraphLimits.abs_cutDist_sub_le_cutNorm_add_cutNorm` changes both graphons at once.
* `TauCeti.DenseGraphLimits.cutDist_le_add_two_mul_cutNorm_of_le_add` transfers a triangle
  estimate proved with an approximating intermediate graphon back to the original intermediate.

## References

* S. Janson, *Graphons, cut norm and distance, couplings and rearrangements*, NYJM Monographs 4
  (2013), Lemma 6.5.
* Roadmap: `TauCetiRoadmap/DenseGraphLimits/README.md`, the Layer-1 design-validation milestone
  requiring stability of the finite coupling reduction under step approximation.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace DenseGraphLimits

variable {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
variable {μ₁ : Measure Ω₁} {μ₂ : Measure Ω₂}
variable [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]

/-- Replacing the graphon on the left carrier changes the cut distance by at most the cut norm of
the replacement.  This one-sided form is kept private; the absolute-value form below is the
stable public interface. -/
private theorem cutDist_sub_le_cutNorm_left (U U' : Graphon Ω₁ μ₁) (W : Graphon Ω₂ μ₂) :
    cutDist U W - cutDist U' W ≤ cutNorm μ₁ (U.toSymmKernel - U'.toSymmKernel) := by
  let C := cutNorm μ₁ (U.toSymmKernel - U'.toSymmKernel)
  have hsub : cutDist U W - C ≤ cutDist U' W := by
    refine le_cutDist U' W fun π hπ => ?_
    let _ := hπ.isFiniteMeasure
    have hoverlay :
        overlayDiff U W π =
          (U.toSymmKernel - U'.toSymmKernel).comap Prod.fst measurable_fst π +
            overlayDiff U' W π := by
      ext p q
      simp only [overlayDiff_apply, SymmKernel.comap_apply, SymmKernel.coe_sub,
        Pi.sub_apply, SymmKernel.coe_add, Pi.add_apply, Graphon.coe_toSymmKernel]
      ring
    calc
      cutDist U W - C ≤ cutNorm π (overlayDiff U W π) - C :=
        sub_le_sub_right (cutDist_le U W hπ) C
      _ = cutNorm π
            ((U.toSymmKernel - U'.toSymmKernel).comap Prod.fst measurable_fst π +
              overlayDiff U' W π) - C := by rw [hoverlay]
      _ ≤ (cutNorm π
              ((U.toSymmKernel - U'.toSymmKernel).comap Prod.fst measurable_fst π) +
            cutNorm π (overlayDiff U' W π)) - C :=
        sub_le_sub_right (cutNorm_add_le π _ _) C
      _ = cutNorm π (overlayDiff U' W π) := by
        rw [cutNorm_comap hπ.measurePreserving_fst]
        simp only [C]
        ring
  linarith

/-- **Stability under replacement on the left carrier.**  If `U` and `U'` are graphons on the
same probability space, then their cut distances to any graphon `W` differ by at most
`‖U - U'‖□`.

No triangle inequality for `cutDist` is used: the proof compares the two overlaid differences
along each individual coupling. -/
theorem abs_cutDist_sub_left_le_cutNorm (U U' : Graphon Ω₁ μ₁) (W : Graphon Ω₂ μ₂) :
    |cutDist U W - cutDist U' W| ≤ cutNorm μ₁ (U.toSymmKernel - U'.toSymmKernel) := by
  rw [abs_le]
  refine ⟨?_, cutDist_sub_le_cutNorm_left U U' W⟩
  have h := cutDist_sub_le_cutNorm_left U' U W
  rw [cutNorm_sub_rev] at h
  linarith

/-- **Stability under replacement on the right carrier.**  If `W` and `W'` are graphons on the
same probability space, then their cut distances from any graphon `U` differ by at most
`‖W - W'‖□`. -/
theorem abs_cutDist_sub_right_le_cutNorm (U : Graphon Ω₁ μ₁) (W W' : Graphon Ω₂ μ₂) :
    |cutDist U W - cutDist U W'| ≤ cutNorm μ₂ (W.toSymmKernel - W'.toSymmKernel) := by
  rw [cutDist_comm U W, cutDist_comm U W']
  exact abs_cutDist_sub_left_le_cutNorm W W' U

/-- **Two-coordinate stability of coupling cut distance.**  Replacing both graphons by graphons
on their respective carriers changes their cut distance by at most the sum of the two same-carrier
cut-norm errors.

This is the quantitative form used by step approximation: a finite-step estimate transfers to
the original pair once each endpoint is close to its finite-step approximant in cut norm. -/
theorem abs_cutDist_sub_le_cutNorm_add_cutNorm (U U' : Graphon Ω₁ μ₁)
    (W W' : Graphon Ω₂ μ₂) :
    |cutDist U W - cutDist U' W'| ≤
      cutNorm μ₁ (U.toSymmKernel - U'.toSymmKernel) +
        cutNorm μ₂ (W.toSymmKernel - W'.toSymmKernel) := by
  calc
    |cutDist U W - cutDist U' W'| =
        |(cutDist U W - cutDist U' W) + (cutDist U' W - cutDist U' W')| := by
          congr 1
          ring
    _ ≤ |cutDist U W - cutDist U' W| + |cutDist U' W - cutDist U' W'| := abs_add_le _ _
    _ ≤ cutNorm μ₁ (U.toSymmKernel - U'.toSymmKernel) +
          cutNorm μ₂ (W.toSymmKernel - W'.toSymmKernel) :=
      add_le_add (abs_cutDist_sub_left_le_cutNorm U U' W)
        (abs_cutDist_sub_right_le_cutNorm U' W W')

section TriangleReduction

variable {Ω₃ : Type*} [MeasurableSpace Ω₃] {μ₃ : Measure Ω₃} [IsProbabilityMeasure μ₃]

/-- **Transfer of a triangle estimate from an approximating intermediate graphon.**  Suppose a
triangle estimate has been proved with `W'` as the intermediate graphon.  Replacing `W'` by a
graphon `W` on the same carrier costs at most twice `‖W - W'‖□`, once for each leg of the triangle.

The finite-step reduction uses this with `W'` a step approximation of `W`: finite-middle coupling
gluing supplies the hypothesis, and letting the cut-norm error tend to zero yields the desired
triangle estimate through `W`. -/
theorem cutDist_le_add_two_mul_cutNorm_of_le_add (U : Graphon Ω₁ μ₁)
    (W W' : Graphon Ω₂ μ₂) (X : Graphon Ω₃ μ₃)
    (h : cutDist U X ≤ cutDist U W' + cutDist W' X) :
    cutDist U X ≤ cutDist U W + cutDist W X +
      2 * cutNorm μ₂ (W.toSymmKernel - W'.toSymmKernel) := by
  have hleft := abs_cutDist_sub_right_le_cutNorm U W' W
  have hright := abs_cutDist_sub_left_le_cutNorm W' W X
  rw [cutNorm_sub_rev] at hleft hright
  linarith [le_abs_self (cutDist U W' - cutDist U W),
    le_abs_self (cutDist W' X - cutDist W X)]

end TriangleReduction

end DenseGraphLimits

end TauCeti
