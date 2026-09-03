/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import TauCeti.Analysis.Complex.Conformal.ImageSimplyConnected
public import Mathlib.Topology.OpenPartialHomeomorph.Basic
public import TauCeti.Analysis.Complex.Conformal.LocalDegree

/-!
# Holomorphic inverse functions

This file supplies global-on-the-image forms of the holomorphic inverse function theorem for
functions that are injective on an open set and for holomorphic open partial homeomorphisms.

## Main results

* `TauCeti.DifferentiableOn.invFunOn` — the inverse of a holomorphic injection on an open set is
  holomorphic on its image.
* `TauCeti.hasDerivAt_invFunOn` — the derivative of the inverse at `f z₀` is
  `(deriv f z₀)⁻¹`, via `HasDerivAt.of_local_left_inverse`.
* `TauCeti.hasDerivAt_invFunOn_comp_segment` — the chain rule for the inverse along an affine
  segment through the image of `z₀`.
* `TauCeti.OpenPartialHomeomorph.differentiableOn_symm` — the inverse of a holomorphic open partial
  homeomorphism is holomorphic on its target.
-/

public section

namespace TauCeti

open Complex Filter Function Set
open scoped Topology

/--
The inverse of a holomorphic injection on an open set is holomorphic on its image.

The inverse is `Function.invFunOn f U`, which chooses the unique preimage lying in `U`. No global
injectivity of `f` outside `U` is required.
-/
theorem DifferentiableOn.invFunOn {f : ℂ → ℂ} {U : Set ℂ} (hf : DifferentiableOn ℂ f U)
    (hU : IsOpen U) (hinj : InjOn f U) :
    DifferentiableOn ℂ (Function.invFunOn f U) (f '' U) := by
  rintro _ ⟨z, hz, rfl⟩
  have hfz : AnalyticAt ℂ f z := hf.analyticAt (hU.mem_nhds hz)
  have hderiv : deriv f z ≠ 0 := deriv_ne_zero_of_injOn hf hU hinj hz
  have hleft : (Function.invFunOn f U ∘ f) =ᶠ[𝓝 z] id := by
    filter_upwards [hU.mem_nhds hz] with w hw
    exact hinj.leftInvOn_invFunOn hw
  have hcomp : AnalyticAt ℂ (Function.invFunOn f U ∘ f) z :=
    analyticAt_id.congr hleft.symm
  exact ((analyticAt_comp_iff_of_deriv_ne_zero hfz hderiv).mp hcomp).differentiableAt
    |>.differentiableWithinAt

/-- The inverse of a holomorphic open partial homeomorphism of `ℂ` is holomorphic on its target. -/
theorem OpenPartialHomeomorph.differentiableOn_symm {e : OpenPartialHomeomorph ℂ ℂ}
    (he : DifferentiableOn ℂ e e.source) :
    DifferentiableOn ℂ e.symm e.target := by
  have hinv := TauCeti.DifferentiableOn.invFunOn he e.open_source e.injOn
  rw [e.image_source_eq_target] at hinv
  exact hinv.congr fun z hz => by
    calc
      e.symm z =
          Function.invFunOn e e.source (e (e.symm z)) :=
        (e.injOn.leftInvOn_invFunOn (e.map_target hz)).symm
      _ = Function.invFunOn e e.source z :=
        congrArg (Function.invFunOn e e.source) (e.right_inv hz)

/-- **The derivative of the holomorphic inverse.** At `f z₀`, the inverse `Function.invFunOn f U`
of a holomorphic injection `f` of the open set `U` has derivative `(deriv f z₀)⁻¹`, by
`HasDerivAt.of_local_left_inverse` applied to the right-inverse relation
`f (invFunOn f U w) = w` on the open image `f '' U`. -/
theorem hasDerivAt_invFunOn {f : ℂ → ℂ} {U : Set ℂ}
    (hf : DifferentiableOn ℂ f U) (hU : IsOpen U) (hinj : InjOn f U) {z₀ : ℂ}
    (hz₀ : z₀ ∈ U) :
    HasDerivAt (Function.invFunOn f U) (deriv f z₀)⁻¹ (f z₀) := by
  have hΩ : IsOpen (f '' U) := isOpen_image_of_differentiableOn_of_injOn hU hf hinj
  have hp : f z₀ ∈ f '' U := mem_image_of_mem f hz₀
  have hgcont : ContinuousAt (Function.invFunOn f U) (f z₀) :=
    ((TauCeti.DifferentiableOn.invFunOn hf hU hinj).differentiableAt
      (hΩ.mem_nhds hp)).continuousAt
  have hgz : Function.invFunOn f U (f z₀) = z₀ := hinj.leftInvOn_invFunOn hz₀
  have hfz : HasDerivAt f (deriv f z₀) (Function.invFunOn f U (f z₀)) := by
    rw [hgz]; exact (hf.differentiableAt (hU.mem_nhds hz₀)).hasDerivAt
  have hd0 : deriv f z₀ ≠ 0 := deriv_ne_zero_of_injOn hf hU hinj hz₀
  have hfg : ∀ᶠ y in 𝓝 (f z₀), f (Function.invFunOn f U y) = y :=
    Filter.eventually_of_mem (hΩ.mem_nhds hp) fun w hw => Function.invFunOn_eq hw
  exact HasDerivAt.of_local_left_inverse hgcont hfz hd0 hfg

/-- **The chain rule for an inverse along a segment.** Composing `g` with the affine segment
`t ↦ d * n * t + w` gives a curve whose derivative at `t = 0` is `n`, when `g` has derivative
`d⁻¹` at `w` and `d ≠ 0`. -/
private theorem hasDerivAt_comp_segment_of_hasDerivAt_inv {g : ℂ → ℂ} {w d : ℂ}
    (hd0 : d ≠ 0) (hg : HasDerivAt g d⁻¹ w) (n : ℂ) :
    HasDerivAt (fun t : ℝ => g (d * n * t + w)) n 0 := by
  have h1 : HasDerivAt (fun t : ℝ => d * n * (t : ℂ) + w)
      (d * n) 0 := by
    simpa using
      (((hasDerivAt_id (0 : ℝ)).ofReal_comp.const_mul (d * n)).add_const w)
  have h2 : HasDerivAt g d⁻¹
      (d * n * ((0 : ℝ) : ℂ) + w) := by simpa using hg
  have h3 := HasDerivAt.scomp (0 : ℝ) h2 h1
  have h4 : (d * n) • d⁻¹ = n := by
    rw [smul_eq_mul]; field_simp [hd0]
  rw [h4] at h3
  exact h3

/-- **The chain rule for `invFunOn` along a segment.** Specialization of
`hasDerivAt_comp_segment_of_hasDerivAt_inv` to the canonical inverse. -/
theorem hasDerivAt_invFunOn_comp_segment {f : ℂ → ℂ} {U : Set ℂ}
    (hf : DifferentiableOn ℂ f U) (hU : IsOpen U) (hinj : InjOn f U) {z₀ : ℂ}
    (hz₀ : z₀ ∈ U) (n : ℂ) :
    HasDerivAt (fun t : ℝ => Function.invFunOn f U
      (deriv f z₀ * n * t + f z₀)) n 0 :=
  hasDerivAt_comp_segment_of_hasDerivAt_inv (d := deriv f z₀) (w := f z₀)
    (deriv_ne_zero_of_injOn hf hU hinj hz₀)
    (hasDerivAt_invFunOn hf hU hinj hz₀) n

end TauCeti
