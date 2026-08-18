/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.NullHomologous
public import TauCeti.Analysis.Contour.Winding.Number.Homotopy
import TauCeti.Analysis.Contour.HomologyCauchy

/-!
# Cauchy's theorem for null-homotopic contours

A closed piecewise-`C¹` path continuously homotopic to its constant path inside an open set is
null-homologous there. Consequently, the homology form of Cauchy's theorem makes the contour
integral of every holomorphic function vanish along such a path. This supplies the
null-homotopic special case explicitly requested in Layer 3 of the Contour Integration roadmap.

The homotopy is represented by Mathlib's `Path.Homotopy`; no differentiability of it is required.
The source path itself is assumed piecewise `C¹`, matching the raw-curve interface expected by
`homologyCauchyTheorem`.

## Main results

* `windingNumber_eq_zero_of_pathHomotopy_refl` — a loop continuously homotopic to its constant path
  through a point-avoiding homotopy has winding number zero about that point.
* `isNullHomologous_of_pathHomotopy_refl` — a loop continuously contracted inside `Ω` is
  null-homologous in `Ω`.
* `cauchyTheorem_of_pathHomotopy_refl` — Cauchy's theorem for such a contractible contour.

## Provenance

No formalization is vendored. The proof combines Tau Ceti's homotopy invariance of the winding
number with its homology Cauchy theorem. The implication “null-homotopic implies
null-homologous” and the resulting Cauchy theorem are standard; see S. Lang, *Complex Analysis*,
Chapter VI, and L. Ahlfors, *Complex Analysis*, Chapter 4, as cited by the Contour Integration
roadmap.
-/

public section

noncomputable section

open scoped unitInterval
open Set

namespace TauCeti.Contour

/-- The extension of a constant path is the constant function on `ℝ`, hence piecewise `C¹`. -/
private theorem isPiecewiseC1On_refl_extend (x : ℂ) :
    IsPiecewiseC1On (Path.refl x).extend 0 1 := by
  simpa only [Path.refl_extend, ContinuousMap.coe_const] using
    IsPiecewiseC1On.of_contDiffOn (γ := Function.const ℝ x) contDiff_const.contDiffOn

/-- A piecewise-`C¹` loop continuously homotopic to its constant path through points avoiding `w`
has winding number zero about `w`. -/
theorem windingNumber_eq_zero_of_pathHomotopy_refl {x w : ℂ} {p : Path x x}
    (hp : IsPiecewiseC1On p.extend 0 1) (φ : p.Homotopy (Path.refl x))
    (havoid : ∀ st : I × I, φ st ≠ w) :
    windingNumber p.extend 0 1 w = 0 := by
  have hrefl : IsPiecewiseC1On (Path.refl x).extend 0 1 :=
    isPiecewiseC1On_refl_extend x
  rw [windingNumber_eq_of_pathHomotopy φ hp hrefl havoid]
  rw [Path.refl_extend]
  exact windingNumber_const x 0 1 w

/-- **Null-homotopic implies null-homologous.** If a piecewise-`C¹` loop admits a continuous path
homotopy to its constant path whose image lies in `Ω`, then its generalized winding number vanishes
at every point outside `Ω`. Thus the loop is null-homologous in `Ω`.

This is one direction only: a null-homologous loop need not be null-homotopic. -/
theorem isNullHomologous_of_pathHomotopy_refl {x : ℂ} {p : Path x x} {Ω : Set ℂ}
    (hp : IsPiecewiseC1On p.extend 0 1) (φ : p.Homotopy (Path.refl x))
    (hφΩ : ∀ st : I × I, φ st ∈ Ω) : IsNullHomologous p.extend 0 1 Ω := by
  have hrefl : IsPiecewiseC1On (Path.refl x).extend 0 1 :=
    isPiecewiseC1On_refl_extend x
  exact (isNullHomologous_iff_of_pathHomotopy φ hp hrefl hφΩ).2
    (by
      rw [Path.refl_extend]
      exact isNullHomologous_const x 0 1 Ω)

/-- **Cauchy's theorem for a null-homotopic contour.** Let `p` be a piecewise-`C¹` loop admitting
a continuous path homotopy to its constant path inside an open set `Ω`. If `f` is holomorphic on
`Ω`, then the contour integral of `f` along `p` vanishes.

The path regularity is exactly what `homologyCauchyTheorem` expects; the homotopy supplies
containment of the source path in `Ω` and its null-homology there. -/
theorem cauchyTheorem_of_pathHomotopy_refl {f : ℂ → ℂ} {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {x : ℂ} (p : Path x x) (hp : IsPiecewiseC1On p.extend 0 1)
    (φ : p.Homotopy (Path.refl x)) (hφΩ : ∀ st : I × I, φ st ∈ Ω)
    (hf : DifferentiableOn ℂ f Ω) :
    ∫ t in (0 : ℝ)..1, deriv p.extend t • f (p.extend t) = 0 := by
  apply homologyCauchyTheorem hΩ p.extend 0 1 hp
  · intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    rw [Path.extend_apply p ht]
    simpa using hφΩ ((0 : Set.Icc (0 : ℝ) 1), ⟨t, ht⟩)
  · simp only [Path.extend_zero, Path.extend_one]
  · exact hf
  · exact isNullHomologous_of_pathHomotopy_refl hp φ hφΩ

end TauCeti.Contour

end
