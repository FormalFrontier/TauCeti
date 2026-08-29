/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear
public import TauCeti.Geometry.Symplectic.Cotangent.Basic

import Mathlib.Analysis.LocallyConvex.SeparatingDual

/-!
# The canonical symplectic form on a continuous-dual cotangent space

For a real normed space `V`, the continuous-dual cotangent model `V × StrongDual ℝ V` carries
the canonical symplectic form

`ω((v, α), (w, β)) = β(v) - α(w)`.

This file constructs the form directly and, in finite dimension, identifies the continuous-dual
model with the algebraic cotangent model `V × Module.Dual ℝ V`.

## Main declarations

* `TauCeti.strongDualCotangentSymplecticForm`: the canonical symplectic form on
  `V × StrongDual ℝ V`.
* `TauCeti.strongDualCotangentEquiv`: the finite-dimensional identification with
  `V × Module.Dual ℝ V`.
-/

public section

noncomputable section

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The bilinear form underlying the canonical symplectic form on
`V × StrongDual ℝ V`. -/
private def strongDualCotangentBilinForm :
    LinearMap.BilinForm ℝ (V × StrongDual ℝ V) where
  toFun x :=
    { toFun := fun y ↦ y.2 x.1 - x.2 y.1
      map_add' := by
        intro y z
        simp
        ring
      map_smul' := by
        intro c y
        simp
        ring }
  map_add' := by
    intro x y
    apply LinearMap.ext
    intro z
    simp
    ring
  map_smul' := by
    intro c x
    apply LinearMap.ext
    intro y
    simp
    ring

@[simp]
private lemma strongDualCotangentBilinForm_apply (x y : V × StrongDual ℝ V) :
    strongDualCotangentBilinForm x y = y.2 x.1 - x.2 y.1 := by
  rfl

private lemma strongDualCotangentBilinForm_isAlt :
    (strongDualCotangentBilinForm (V := V)).IsAlt := by
  intro x
  simp

private lemma strongDualCotangentBilinForm_nondegenerate :
    (strongDualCotangentBilinForm (V := V)).Nondegenerate := by
  refine (LinearMap.IsAlt.isRefl
    strongDualCotangentBilinForm_isAlt).nondegenerate_iff_separatingLeft.mpr ?_
  rintro ⟨v, α⟩ h
  have hα : α = 0 := by
    apply ContinuousLinearMap.ext
    intro w
    have := h (w, 0)
    simpa using this
  have hv : v = 0 := by
    exact SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℝ) fun β ↦ by
      have := h (0, β)
      simpa using this
  exact Prod.ext hv hα

/-- The canonical symplectic form on the normed linear cotangent space
`V × StrongDual ℝ V`. -/
noncomputable def strongDualCotangentSymplecticForm :
    SymplecticForm (V × StrongDual ℝ V) where
  toBilinForm := strongDualCotangentBilinForm
  isAlt := strongDualCotangentBilinForm_isAlt
  nondegenerate := strongDualCotangentBilinForm_nondegenerate

/-- The canonical symplectic form on the continuous-dual model has the usual evaluation formula. -/
@[simp]
lemma strongDualCotangentSymplecticForm_apply (x y : V × StrongDual ℝ V) :
    strongDualCotangentSymplecticForm x y = y.2 x.1 - x.2 y.1 := by
  rfl

section FiniteDimensional

variable [FiniteDimensional ℝ V]

/-- Identify the normed linear cotangent space, formed with the continuous dual, with the
algebraic linear cotangent space. -/
noncomputable def strongDualCotangentEquiv :
    (V × StrongDual ℝ V) ≃ₗ[ℝ] (V × Module.Dual ℝ V) :=
  (LinearEquiv.refl ℝ V).prodCongr LinearMap.toContinuousLinearMap.symm

/-- The identification of cotangent models forgets the continuity of the covector. -/
@[simp]
lemma strongDualCotangentEquiv_apply (q : V) (p : StrongDual ℝ V) :
    strongDualCotangentEquiv (q, p) = (q, (p : Module.Dual ℝ V)) := by
  simp [strongDualCotangentEquiv]

/-- The inverse identification of cotangent models promotes a covector to a continuous one. -/
@[simp]
lemma strongDualCotangentEquiv_symm_apply (q : V) (p : Module.Dual ℝ V) :
    strongDualCotangentEquiv.symm (q, p) = (q, LinearMap.toContinuousLinearMap p) := by
  simp [strongDualCotangentEquiv]

end FiniteDimensional

end TauCeti

end
