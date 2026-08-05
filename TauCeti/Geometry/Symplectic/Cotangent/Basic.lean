/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import TauCeti.Geometry.Symplectic.Lagrangian.Basic

/-!
# The canonical symplectic form on a cotangent space

For a real vector space `V`, the product `V × V*` is the linear model of its cotangent bundle.
It carries the canonical symplectic form

`ω((v, α), (w, β)) = β(v) - α(w)`.

This file constructs that form directly from Mathlib's evaluation pairing, proves its
nondegeneracy, and records the two canonical Lagrangian subspaces: the zero section `V × {0}`
and a cotangent fiber `{0} × V*`. These are the pointwise linear-algebra inputs for cotangent
bundles in exact Lagrangian Floer theory.

## Main declarations

* `TauCeti.cotangentSymplecticForm`: the canonical symplectic form on `V × Module.Dual ℝ V`.
* `TauCeti.cotangentSymplecticForm_apply`: its evaluation formula.
* `TauCeti.cotangentZeroSection`: the linear zero section `V × {0}`.
* `TauCeti.cotangentFiber`: the linear cotangent fiber `{0} × V*`.
* `TauCeti.SymplecticForm.isLagrangian_cotangentZeroSection`: the zero section is Lagrangian.
* `TauCeti.SymplecticForm.isLagrangian_cotangentFiber`: the cotangent fiber is Lagrangian.

The sign convention is the standard one `ω = -dλ`, where the tautological one-form is
`λ_(q,p)(δq,δp) = p(δq)`.
-/

public section

namespace TauCeti

open LinearMap

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The bilinear form `((v, α), (w, β)) ↦ β(v) - α(w)` underlying the canonical
symplectic form on `V × V*`. -/
private def cotangentBilinForm : LinearMap.BilinForm ℝ (V × Module.Dual ℝ V) :=
  (Module.Dual.eval ℝ V).compl₁₂ (LinearMap.fst ℝ V (Module.Dual ℝ V))
      (LinearMap.snd ℝ V (Module.Dual ℝ V)) -
    (LinearMap.id : Module.Dual ℝ V →ₗ[ℝ] Module.Dual ℝ V).compl₁₂
      (LinearMap.snd ℝ V (Module.Dual ℝ V)) (LinearMap.fst ℝ V (Module.Dual ℝ V))

@[simp]
private lemma cotangentBilinForm_apply (x y : V × Module.Dual ℝ V) :
    cotangentBilinForm x y = y.2 x.1 - x.2 y.1 := by
  rfl

private lemma cotangentBilinForm_isAlt :
    (cotangentBilinForm (V := V)).IsAlt := by
  intro x
  simp

private lemma cotangentBilinForm_nondegenerate :
    (cotangentBilinForm (V := V)).Nondegenerate := by
  refine (LinearMap.IsAlt.isRefl cotangentBilinForm_isAlt).nondegenerate_iff_separatingLeft.mpr ?_
  rintro ⟨v, α⟩ h
  have hα : α = 0 := by
    apply LinearMap.ext
    intro w
    have := h (w, 0)
    simpa using this
  have hv : v = 0 := by
    exact (Module.forall_dual_apply_eq_zero_iff ℝ v).mp fun β => by
      have := h (0, β)
      simpa using this
  exact Prod.ext hv hα

/-- The canonical symplectic form on the linear cotangent space `V × V*`, with formula
`ω((v, α), (w, β)) = β(v) - α(w)`. -/
noncomputable def cotangentSymplecticForm : SymplecticForm (V × Module.Dual ℝ V) where
  toBilinForm := cotangentBilinForm
  isAlt := cotangentBilinForm_isAlt
  nondegenerate := cotangentBilinForm_nondegenerate

/-- Evaluation of the canonical cotangent symplectic form. -/
@[simp]
lemma cotangentSymplecticForm_apply (x y : V × Module.Dual ℝ V) :
    cotangentSymplecticForm x y = y.2 x.1 - x.2 y.1 := by
  rfl

/-- The zero section `V × {0}` in the linear cotangent space `V × V*`. -/
def cotangentZeroSection : Submodule ℝ (V × Module.Dual ℝ V) :=
  LinearMap.range (LinearMap.inl ℝ V (Module.Dual ℝ V))

/-- The cotangent fiber `{0} × V*` in the linear cotangent space `V × V*`. -/
def cotangentFiber : Submodule ℝ (V × Module.Dual ℝ V) :=
  LinearMap.range (LinearMap.inr ℝ V (Module.Dual ℝ V))

@[simp]
lemma mem_cotangentZeroSection_iff {x : V × Module.Dual ℝ V} :
    x ∈ cotangentZeroSection ↔ x.2 = 0 := by
  rw [cotangentZeroSection, LinearMap.range_inl, LinearMap.mem_ker]
  rfl

@[simp]
lemma mem_cotangentFiber_iff {x : V × Module.Dual ℝ V} :
    x ∈ cotangentFiber ↔ x.1 = 0 := by
  rw [cotangentFiber, LinearMap.range_inr, LinearMap.mem_ker]
  rfl

namespace SymplecticForm

/-- The symplectic orthogonal of the zero section is the zero section itself. -/
@[simp]
lemma orthogonal_cotangentZeroSection :
    (cotangentSymplecticForm (V := V)).orthogonal cotangentZeroSection =
      cotangentZeroSection := by
  ext x
  rw [SymplecticForm.mem_orthogonal_iff, mem_cotangentZeroSection_iff]
  constructor
  · intro hx
    apply LinearMap.ext
    intro v
    have := hx (v, 0) (by simp)
    simpa using this
  · intro hx y hy
    simp only [mem_cotangentZeroSection_iff] at hy
    simp [hx, hy]

/-- The symplectic orthogonal of a cotangent fiber is that fiber itself. -/
@[simp]
lemma orthogonal_cotangentFiber :
    (cotangentSymplecticForm (V := V)).orthogonal cotangentFiber = cotangentFiber := by
  ext x
  rw [SymplecticForm.mem_orthogonal_iff, mem_cotangentFiber_iff]
  constructor
  · intro hx
    exact (Module.forall_dual_apply_eq_zero_iff ℝ x.1).mp fun α => by
      have := hx (0, α) (by simp)
      simpa using this
  · intro hx y hy
    simp only [mem_cotangentFiber_iff] at hy
    simp [hx, hy]

/-- The zero section is Lagrangian for the canonical cotangent symplectic form. -/
lemma isLagrangian_cotangentZeroSection :
    (cotangentSymplecticForm (V := V)).IsLagrangian
      (cotangentZeroSection (V := V)) := by
  simp [isLagrangian_iff, isIsotropic_iff_le, isCoisotropic_iff_le,
    orthogonal_cotangentZeroSection]

/-- The vertical subspace `{0} × V*` is Lagrangian for the canonical cotangent symplectic form. -/
lemma isLagrangian_cotangentFiber :
    (cotangentSymplecticForm (V := V)).IsLagrangian (cotangentFiber (V := V)) := by
  simp [isLagrangian_iff, isIsotropic_iff_le, isCoisotropic_iff_le,
    orthogonal_cotangentFiber]

end SymplecticForm

end TauCeti
