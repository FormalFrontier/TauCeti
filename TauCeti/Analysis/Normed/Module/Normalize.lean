/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Normalize

/-!
# Radial projection to the unit sphere

This file packages pointwise normalization of a continuous nowhere-zero map as a continuous map
to the unit sphere.
-/

public section

noncomputable section

open Metric NormedSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Radial projection sends a continuous nowhere-zero map into a real normed space continuously
to its unit sphere. -/
noncomputable def normalizeToSphere {Y : Type*} [TopologicalSpace Y] (f : Y → E)
    (hf : Continuous f) (h0 : ∀ y, f y ≠ 0) : C(Y, sphere (0 : E) 1) where
  toFun y := ⟨normalize (f y), mem_sphere_zero_iff_norm.mpr (norm_normalize (h0 y))⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    simp only [NormedSpace.normalize]
    exact ((continuous_norm.comp hf).inv₀
      (fun y => norm_ne_zero_iff.mpr (h0 y))).smul hf

/-- The underlying vector of `normalizeToSphere f hf h0 y` is the normalization of `f y`. -/
@[simp]
theorem coe_normalizeToSphere_apply {Y : Type*} [TopologicalSpace Y] (f : Y → E)
    (hf : Continuous f) (h0 : ∀ y, f y ≠ 0) (y : Y) :
    ((normalizeToSphere f hf h0 y : sphere (0 : E) 1) : E) = normalize (f y) :=
  (rfl)

end TauCeti

end
