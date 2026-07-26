/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Complex.Conformal.Reflection.Basic
public import TauCeti.Analysis.Complex.Conformal.Reflection.Circle.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Conjugating a holomorphic map by circle reflections

This file develops the analytic operation used to transport Schwarz reflection from a line to a
circle. Given source and target circles, `circleReflectionConjugate` reflects the argument in the
source circle, applies a map, and reflects its value in the target circle. Although each circle
reflection is antiholomorphic, their composite around a holomorphic map is holomorphic away from
the source centre and points mapped to the target centre.

The main result, `differentiableOn_circleReflectionConjugate`, proves this holomorphy transfer on
an arbitrary set. The proof reduces circle inversion to conjugation followed by a holomorphic
fractional-linear coordinate, then uses the conjugation-composition lemma from
`Reflection/Basic.lean`. The accompanying involution theorem records that applying the operation
again recovers the original map when both radii are nonzero.

This is a prerequisite for the circle case of layer L4 in the conformal-mapping roadmap: Schwarz
reflection "across an analytic arc / circle by Möbius reduction". The construction follows the
standard circle-reflection formula; see Ahlfors, *Complex Analysis*, Chapters 4--6. This L4
material is absent from the upstream Mathlib Riemann-mapping draft mathlib4#33505.
-/

public section

namespace TauCeti

open Complex EuclideanGeometry Set
open scoped ComplexConjugate

/-- Conjugate a map by reflections in a source circle and a target circle.

The source circle has centre `c` and radius `r`, and the target circle has centre `d` and radius
`s`. Thus the value at `z` is `R_{d,s} (f (R_{c,r} z))`, where `R` denotes Euclidean inversion.
The definition is total; analytic results exclude the centres where the inversion formula has a
pole. -/
noncomputable def circleReflectionConjugate (c : ℂ) (r : ℝ) (d : ℂ) (s : ℝ)
    (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  inversion d s (f (inversion c r z))

/-- The circle-reflection conjugate is the composite of the two inversions and the map. -/
@[simp]
lemma circleReflectionConjugate_apply (c : ℂ) (r : ℝ) (d : ℂ) (s : ℝ)
    (f : ℂ → ℂ) (z : ℂ) :
    circleReflectionConjugate c r d s f z = inversion d s (f (inversion c r z)) :=
  (rfl)

/-- With zero source radius, the circle-reflection conjugate is constant. -/
@[simp]
theorem circleReflectionConjugate_zero_source_radius (c d : ℂ) (s : ℝ)
    (f : ℂ → ℂ) :
    circleReflectionConjugate c 0 d s f = fun _ => inversion d s (f c) := by
  funext z
  simp

/-- With zero target radius, the circle-reflection conjugate is constant. -/
@[simp]
theorem circleReflectionConjugate_zero_target_radius (c : ℂ) (r : ℝ) (d : ℂ)
    (f : ℂ → ℂ) : circleReflectionConjugate c r d 0 f = fun _ => d := by
  funext z
  simp

/-- The circle-reflection conjugate agrees with the original map on the source circle when the
map sends the source circle into the target circle. -/
theorem circleReflectionConjugate_eqOn_sphere (c : ℂ) (r : ℝ) (d : ℂ) (s : ℝ)
    (f : ℂ → ℂ) (hmap : MapsTo f (Metric.sphere c r) (Metric.sphere d s)) :
    EqOn (circleReflectionConjugate c r d s f) f (Metric.sphere c r) := by
  intro z hz
  simp [inversion_of_mem_sphere hz, inversion_of_mem_sphere (hmap hz)]

/-- Applying the same circle-reflection conjugation twice recovers the original map. -/
@[simp]
theorem circleReflectionConjugate_circleReflectionConjugate (c : ℂ) {r : ℝ} (d : ℂ)
    {s : ℝ} (hr : r ≠ 0) (hs : s ≠ 0) (f : ℂ → ℂ) :
    circleReflectionConjugate c r d s (circleReflectionConjugate c r d s f) = f := by
  funext z
  simp only [circleReflectionConjugate_apply, inversion_inversion _ hr,
    inversion_inversion _ hs]

/-- The holomorphic coordinate whose complex conjugate is reflection in the circle centred at
`c` with radius `r`. -/
private noncomputable def circleReflectionCoord (c : ℂ) (r : ℝ) (z : ℂ) : ℂ :=
  (starRingEnd ℂ) c + (r : ℂ) ^ 2 / (z - c)

private lemma conj_circleReflectionCoord (c : ℂ) (r : ℝ) (z : ℂ) :
    (starRingEnd ℂ) (circleReflectionCoord c r z) = inversion c r z := by
  rw [circleReflectionCoord, map_add, map_div₀, map_pow, map_sub,
    starRingEnd_self_apply]
  rw [starRingEnd_apply, Complex.star_def, Complex.conj_ofReal]
  rw [← map_sub]
  exact (inversion_eq_conj_reciprocal c r z).symm

private lemma differentiableOn_circleReflectionCoord {c : ℂ} {r : ℝ} {S : Set ℂ}
    (hc : c ∉ S) : DifferentiableOn ℂ (circleReflectionCoord c r) S := by
  intro z hz
  exact ((differentiableAt_const (𝕜 := ℂ) (x := z) ((starRingEnd ℂ) c)).add
    ((differentiableAt_const (𝕜 := ℂ) (x := z) ((r : ℂ) ^ 2)).div
      (differentiableAt_id.sub_const c)
      (sub_ne_zero.mpr (fun h => hc (h ▸ hz)))))
    |>.differentiableWithinAt

/-- Conjugating a holomorphic map by source and target circle reflections is holomorphic away
from the inversion centres.

When both radii are nonzero, the set `S` is mapped into the original holomorphy domain `Ω` by
source reflection, and the two nonincidence hypotheses remove the poles of the source and target
inversions. These hypotheses are unnecessary when either radius is zero, since the conjugate is
then constant. -/
theorem differentiableOn_circleReflectionConjugate {c : ℂ} {r : ℝ} {d : ℂ} {s : ℝ}
    {f : ℂ → ℂ} {Ω S : Set ℂ}
    (hf : r ≠ 0 ∧ s ≠ 0 → DifferentiableOn ℂ f Ω)
    (hmap : r ≠ 0 ∧ s ≠ 0 → MapsTo (inversion c r) S Ω)
    (hc : r ≠ 0 ∧ s ≠ 0 → c ∉ S)
    (hd : r ≠ 0 ∧ s ≠ 0 → ∀ z ∈ S, f (inversion c r z) ≠ d) :
    DifferentiableOn ℂ (circleReflectionConjugate c r d s f) S := by
  by_cases hr : r = 0
  · simp [hr]
  by_cases hs : s = 0
  · simp [hs]
  have hrs : r ≠ 0 ∧ s ≠ 0 := ⟨hr, hs⟩
  let q := circleReflectionCoord c r
  let g := fun z => (starRingEnd ℂ) (f ((starRingEnd ℂ) z))
  have hg : DifferentiableOn ℂ g ((starRingEnd ℂ) '' Ω) :=
    differentiableOn_conj_conj (hf hrs)
  have hq : DifferentiableOn ℂ q S := differentiableOn_circleReflectionCoord (hc hrs)
  have hqmap : MapsTo q S ((starRingEnd ℂ) '' Ω) := by
    intro z hz
    refine ⟨inversion c r z, hmap hrs hz, ?_⟩
    simpa [q] using (congrArg (starRingEnd ℂ) (conj_circleReflectionCoord c r z)).symm
  have hcomp : DifferentiableOn ℂ (g ∘ q) S := hg.comp hq hqmap
  have hden : ∀ z ∈ S, g (q z) - (starRingEnd ℂ) d ≠ 0 := by
    intro z hz hzero
    apply hd hrs z hz
    apply (starRingEnd ℂ).injective
    simpa [g, q, sub_eq_zero, conj_circleReflectionCoord] using hzero
  have hformula : EqOn (circleReflectionConjugate c r d s f)
      (fun z => d + (s : ℂ) ^ 2 / (g (q z) - (starRingEnd ℂ) d)) S := by
    intro z hz
    rw [circleReflectionConjugate_apply, inversion_eq_conj_reciprocal,
      map_sub]
    simp only [g, q, conj_circleReflectionCoord]
  have hdiff : DifferentiableOn ℂ
      (fun z => d + (s : ℂ) ^ 2 / (g (q z) - (starRingEnd ℂ) d)) S := by
    intro z hz
    exact (differentiableWithinAt_const (𝕜 := ℂ) (x := z) (s := S) d).add
      ((differentiableWithinAt_const (𝕜 := ℂ) (x := z) (s := S) ((s : ℂ) ^ 2)).div
        ((hcomp z hz).sub
          (differentiableWithinAt_const (𝕜 := ℂ) (x := z) (s := S)
            ((starRingEnd ℂ) d)))
        (hden z hz))
  refine hdiff.congr ?_
  intro z hz
  exact hformula hz

end TauCeti
