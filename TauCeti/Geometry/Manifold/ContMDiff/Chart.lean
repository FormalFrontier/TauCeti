/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# Differentiability in extended charts

This file records model-space differentiability consequences of manifold differentiability for
curves read in an extended chart.
-/

public section

open scoped Manifold

namespace TauCeti.Manifold

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

/-- A curve differentiable within `s` at `t` in the manifold sense reads as a differentiable
model-space curve in any extended chart whose source contains `γ t`. -/
theorem differentiableWithinAt_extChartAt_comp (γ : 𝕜 → M) {s : Set 𝕜} {x : M} {t : 𝕜}
    (hγ : MDifferentiableWithinAt 𝓘(𝕜, 𝕜) I γ s t)
    (hx : γ t ∈ (chartAt H x).source) :
    DifferentiableWithinAt 𝕜 (extChartAt I x ∘ γ) s t :=
  ((mdifferentiableAt_extChartAt hx).comp_mdifferentiableWithinAt t hγ).differentiableWithinAt

/-- A curve differentiable at `t` in the manifold sense reads as a differentiable model-space
curve in any extended chart whose source contains `γ t`. -/
theorem differentiableAt_extChartAt_comp (γ : 𝕜 → M) {x : M} {t : 𝕜}
    (hγ : MDifferentiableAt 𝓘(𝕜, 𝕜) I γ t) (hx : γ t ∈ (chartAt H x).source) :
    DifferentiableAt 𝕜 (extChartAt I x ∘ γ) t := by
  rw [← differentiableWithinAt_univ]
  exact differentiableWithinAt_extChartAt_comp γ hγ.mdifferentiableWithinAt hx

end TauCeti.Manifold
