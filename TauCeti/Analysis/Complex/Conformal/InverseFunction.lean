/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
public import Mathlib.Topology.OpenPartialHomeomorph.Basic
public import TauCeti.Analysis.Complex.Conformal.LocalDegree

/-!
# Holomorphic inverse functions

This file supplies global-on-the-image forms of the holomorphic inverse function theorem for
functions that are injective on an open set and for holomorphic open partial homeomorphisms.
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
  have hderiv : deriv f z ≠ 0 :=
    (exists_injOn_nhds_iff_deriv_ne_zero hfz).mp ⟨U, hU.mem_nhds hz, hinj⟩
  have hleft : (Function.invFunOn f U ∘ f) =ᶠ[𝓝 z] id := by
    filter_upwards [hU.mem_nhds hz] with w hw
    exact hinj.leftInvOn_invFunOn hw
  have hcomp : AnalyticAt ℂ (Function.invFunOn f U ∘ f) z :=
    analyticAt_id.congr hleft.symm
  exact ((analyticAt_comp_iff_of_deriv_ne_zero hfz hderiv).mp hcomp).differentiableAt
    |>.differentiableWithinAt

/-- The inverse of a holomorphic open partial homeomorphism of `ℂ` is holomorphic on its target. -/
theorem DifferentiableOn.openPartialHomeomorph_symm {e : OpenPartialHomeomorph ℂ ℂ}
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

end TauCeti
