/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
public import TauCeti.Analysis.Complex.Conformal.LocalDegree

/-!
# Holomorphic inverse functions

This file supplies a global-on-the-image form of the holomorphic inverse function theorem for
functions that are injective on an open set.
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

end TauCeti
