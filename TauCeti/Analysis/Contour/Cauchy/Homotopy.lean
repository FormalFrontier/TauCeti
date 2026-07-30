/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Contour.Winding.Number.Homotopy
import TauCeti.Analysis.Contour.HomologyCauchy

/-!
# Cauchy's theorem for null-homotopic contours

A closed path that is smoothly homotopic to its constant path inside an open set is
null-homologous there. Consequently, the homology form of Cauchy's theorem makes the contour
integral of every holomorphic function vanish along such a path. This supplies the
null-homotopic special case explicitly requested in Layer 3 of the Contour Integration roadmap.

The homotopy is represented by Mathlib's `Path.Homotopy`, and the same `C²` regularity used by
`windingNumber_eq_of_pathHomotopy` is retained. That regularity supplies a piecewise-`C¹` source
path, matching the raw-curve interface expected by `homologyCauchyTheorem`.

## Main results

* `windingNumber_const` — a constant curve has winding number zero on every parameter interval.
* `windingNumber_eq_zero_of_pathHomotopy_refl` — a loop smoothly homotopic to its constant path
  through a point-avoiding homotopy has winding number zero about that point.
* `isNullHomologous_of_pathHomotopy_refl` — a loop smoothly contracted inside `Ω` is
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

/-- The generalized winding number of a constant curve is zero on every parameter interval. -/
@[simp]
theorem windingNumber_const (x : ℂ) (a b : ℝ) (z : ℂ) :
    windingNumber (fun _ : ℝ => x) a b z = 0 := by
  have hpv :
      HasCauchyPVAt (fun _ : ℝ => x) a b (fun w => (w - z)⁻¹) z 0 := by
    refine HasCauchyPVAt.intro ?_ ?_
    · filter_upwards with ε
      simp only [deriv_const, mul_zero, ite_self]
      exact IntervalIntegrable.zero
    · simpa only [deriv_const, mul_zero, ite_self, intervalIntegral.integral_zero] using
        (tendsto_const_nhds :
          Filter.Tendsto (fun _ : ℝ => (0 : ℂ)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
  rw [windingNumber_eq_of_hasCauchyPVAt hpv]
  simp

/-- A constant curve is null-homologous in every ambient set and on every parameter interval. -/
@[simp]
theorem isNullHomologous_const (x : ℂ) (a b : ℝ) (Ω : Set ℂ) :
    IsNullHomologous (fun _ : ℝ => x) a b Ω := by
  rw [isNullHomologous_iff]
  intro w _hw
  exact windingNumber_const x a b w

/-- A loop smoothly homotopic to its constant path through points avoiding `w` has winding number
zero about `w`. -/
theorem windingNumber_eq_zero_of_pathHomotopy_refl {x w : ℂ} {p : Path x x}
    (φ : p.Homotopy (Path.refl x))
    (hφsmooth : ContDiffOn ℝ 2
      (fun st : ℝ × ℝ ↦ Set.IccExtend zero_le_one (φ.toHomotopy.extend st.1) st.2)
      (Set.Icc 0 1))
    (havoid : ∀ st : Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) 1, φ st ≠ w) :
    windingNumber p.extend 0 1 w = 0 := by
  rw [windingNumber_eq_of_pathHomotopy φ hφsmooth havoid]
  rw [Path.refl_extend]
  exact windingNumber_const x 0 1 w

/-- **Null-homotopic implies null-homologous.** If a loop admits a `C²` path homotopy to its
constant path whose image lies in `Ω`, then its generalized winding number vanishes at every point
outside `Ω`. Thus the loop is null-homologous in `Ω`.

This is one direction only: a null-homologous loop need not be null-homotopic. -/
theorem isNullHomologous_of_pathHomotopy_refl {x : ℂ} {p : Path x x} {Ω : Set ℂ}
    (φ : p.Homotopy (Path.refl x))
    (hφsmooth : ContDiffOn ℝ 2
      (fun st : ℝ × ℝ ↦ Set.IccExtend zero_le_one (φ.toHomotopy.extend st.1) st.2)
      (Set.Icc 0 1))
    (hφΩ : ∀ st : Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) 1, φ st ∈ Ω) :
    IsNullHomologous p.extend 0 1 Ω :=
  (isNullHomologous_iff_of_pathHomotopy φ hφsmooth hφΩ).2
    (by
      rw [Path.refl_extend]
      exact isNullHomologous_const x 0 1 Ω)

/-- **Cauchy's theorem for a null-homotopic contour.** Let `p` be a piecewise-`C¹` loop admitting
a `C²` path homotopy to its constant path inside an open set `Ω`. If `f` is holomorphic on `Ω`,
then the contour integral of `f` along `p` vanishes.

The smooth homotopy supplies the piecewise-`C¹` regularity expected by
`homologyCauchyTheorem`, as well as containment of the source path in `Ω` and its null-homology
there. -/
theorem cauchyTheorem_of_pathHomotopy_refl {f : ℂ → ℂ} {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {x : ℂ} (p : Path x x)
    (φ : p.Homotopy (Path.refl x))
    (hφsmooth : ContDiffOn ℝ 2
      (fun st : ℝ × ℝ ↦ Set.IccExtend zero_le_one (φ.toHomotopy.extend st.1) st.2)
      (Set.Icc 0 1))
    (hφΩ : ∀ st : Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) 1, φ st ∈ Ω)
    (hf : DifferentiableOn ℂ f Ω) :
    ∫ t in (0 : ℝ)..1, deriv p.extend t • f (p.extend t) = 0 := by
  have hp : IsPiecewiseC1On p.extend 0 1 := by
    simpa using isPiecewiseC1On_eval_of_smoothPathHomotopy φ hφsmooth (0 : I)
  apply homologyCauchyTheorem hΩ p.extend 0 1 hp
  · intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    rw [Path.extend_apply p ht]
    simpa using hφΩ ((0 : Set.Icc (0 : ℝ) 1), ⟨t, ht⟩)
  · simp only [Path.extend_zero, Path.extend_one]
  · exact hf
  · exact isNullHomologous_of_pathHomotopy_refl φ hφsmooth hφΩ

end TauCeti.Contour

end
