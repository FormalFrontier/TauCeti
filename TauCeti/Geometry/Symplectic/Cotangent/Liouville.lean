/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.DifferentialForm.Basic
public import TauCeti.Geometry.Symplectic.Cotangent.Basic

public import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear
import TauCeti.Geometry.Symplectic.SymplecticTransport

/-!
# The Liouville form on a linear cotangent space

The normed linear cotangent space `V × V'`, formed using the continuous dual, carries the
tautological, or Liouville, one-form

`λ_(q,p)(δq,δp) = p(δq)`.

This file constructs that differential form and proves the sign convention already used by
`TauCeti.cotangentSymplecticForm`:

`strongDualCotangentSymplecticForm = -dλ`.

Thus the canonical symplectic form on the linear cotangent model is exact. This is the
finite-dimensional model for the exact cotangent-bundle geometry used in Lagrangian Floer
homology. The construction follows McDuff--Salamon, *Introduction to Symplectic Topology*,
Section 3.2.

## Main declarations

* `TauCeti.cotangentLiouvilleForm`: the tautological one-form on `V × StrongDual ℝ V`.
* `TauCeti.cotangentLiouvilleForm_apply`: its evaluation formula.
* `TauCeti.differentiableAt_cotangentLiouvilleForm`: differentiability of the form-valued map.
* `TauCeti.strongDualCotangentSymplecticForm`: the canonical symplectic form on `V × V'`.
* `TauCeti.extDeriv_cotangentLiouvilleForm_apply`: the coordinate formula for the exterior
  derivative.
* `TauCeti.neg_extDeriv_cotangentLiouvilleForm`: the exactness identity `ω = -dλ`, and
  `TauCeti.neg_extDeriv_cotangentLiouvilleForm_apply`, its evaluation on a pair of vectors.
-/

public section

open ContinuousAlternatingMap

noncomputable section

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

private noncomputable def cotangentLiouvilleFormCLM :
    (V × StrongDual ℝ V) →L[ℝ]
      ((V × StrongDual ℝ V) [⋀^Fin 1]→L[ℝ] ℝ) :=
  (LinearIsometryEquiv.toContinuousLinearEquiv <|
    ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ)
      (E := V × StrongDual ℝ V) (F := ℝ) (0 : Fin 1)).toContinuousLinearMap.comp <|
    ((ContinuousLinearMap.compL ℝ (V × StrongDual ℝ V) V ℝ).flip
      (ContinuousLinearMap.fst ℝ V (StrongDual ℝ V))).comp <|
        ContinuousLinearMap.snd ℝ V (StrongDual ℝ V)

/-- The tautological one-form on the linear cotangent space. At `(q, p)`, it evaluates a tangent
vector `(δq, δp)` by `p(δq)`. -/
noncomputable def cotangentLiouvilleForm (x : V × StrongDual ℝ V) :
    (V × StrongDual ℝ V) [⋀^Fin 1]→L[ℝ] ℝ :=
  cotangentLiouvilleFormCLM x

/-- The Liouville form evaluates by pairing the covector at the base point with the horizontal
component of the tangent vector. -/
@[simp]
lemma cotangentLiouvilleForm_apply (x : V × StrongDual ℝ V)
    (v : Fin 1 → V × StrongDual ℝ V) :
    cotangentLiouvilleForm x v = x.2 (v 0).1 := by
  simp [cotangentLiouvilleForm, cotangentLiouvilleFormCLM]

/-- The Liouville form vanishes at every point of the zero section. -/
@[simp]
lemma cotangentLiouvilleForm_zero_covector (q : V) :
    cotangentLiouvilleForm (q, 0) = 0 := by
  ext v
  simp

/-- The Liouville form vanishes on vertical tangent vectors. -/
lemma cotangentLiouvilleForm_vertical_apply (x : V × StrongDual ℝ V)
    (α : StrongDual ℝ V) :
    cotangentLiouvilleForm x (fun _ ↦ (0, α)) = 0 := by
  simp

/-- The Liouville one-form is differentiable as a form-valued function of its base point. -/
lemma differentiableAt_cotangentLiouvilleForm (x : V × StrongDual ℝ V) :
    DifferentiableAt ℝ (cotangentLiouvilleForm (V := V)) x := by
  have heq : cotangentLiouvilleForm (V := V) = cotangentLiouvilleFormCLM := by
    funext y
    rfl
  have h : HasFDerivAt (cotangentLiouvilleFormCLM (V := V))
      (cotangentLiouvilleFormCLM (V := V)) x :=
    ContinuousLinearMap.hasFDerivAt _
  rw [heq]
  exact h.differentiableAt

/-- The scalar coefficient obtained by evaluating the Liouville form on a fixed vector has the
expected derivative: only the covector coordinate of the base point varies. -/
private lemma hasFDerivAt_cotangentLiouvilleForm_apply
    (v : Fin 1 → V × StrongDual ℝ V)
    (x : V × StrongDual ℝ V) :
    HasFDerivAt (fun y ↦ cotangentLiouvilleForm y v)
      ((ContinuousLinearMap.apply ℝ ℝ (v 0).1).comp
        (ContinuousLinearMap.snd ℝ V (StrongDual ℝ V))) x := by
  let L := (ContinuousLinearMap.apply ℝ ℝ (v 0).1).comp
    (ContinuousLinearMap.snd ℝ V (StrongDual ℝ V))
  have hfun : (fun y ↦ cotangentLiouvilleForm y v) = L := by
    funext y
    simp [L]
  rw [hfun]
  exact L.hasFDerivAt

/-- The exterior derivative of the Liouville form is the negative canonical cotangent symplectic
form. -/
lemma extDeriv_cotangentLiouvilleForm_apply (x : V × StrongDual ℝ V)
    (v : Fin 2 → V × StrongDual ℝ V) :
    extDeriv cotangentLiouvilleForm x v =
      (v 0).2 (v 1).1 - (v 1).2 (v 0).1 := by
  rw [extDeriv_apply]
  · rw [Fin.sum_univ_two]
    simp only [Fin.isValue, Fin.val_zero, pow_zero, one_smul,
      Fin.val_one, pow_one, neg_smul, one_smul]
    rw [(hasFDerivAt_cotangentLiouvilleForm_apply (Fin.removeNth 0 v) x).fderiv,
      (hasFDerivAt_cotangentLiouvilleForm_apply (Fin.removeNth 1 v) x).fderiv]
    simp [Fin.removeNth, sub_eq_add_neg]
  · exact differentiableAt_cotangentLiouvilleForm x

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

/-- The canonical symplectic form on a finite-dimensional normed linear cotangent space. This
is the algebraic canonical form transported from `V × Module.Dual ℝ V` to
`V × StrongDual ℝ V`. -/
noncomputable def strongDualCotangentSymplecticForm : SymplecticForm (V × StrongDual ℝ V) :=
  (cotangentSymplecticForm (V := V)).transport (strongDualCotangentEquiv (V := V)).symm

/-- The canonical symplectic form on the continuous-dual model has the usual evaluation formula. -/
@[simp]
lemma strongDualCotangentSymplecticForm_apply (x y : V × StrongDual ℝ V) :
    strongDualCotangentSymplecticForm x y = y.2 x.1 - x.2 y.1 := by
  simp [strongDualCotangentSymplecticForm, strongDualCotangentEquiv]

/-- The canonical cotangent symplectic form is minus the exterior derivative of the Liouville
form, with the identity stated in the direction of the convention `ω = -dλ`. -/
lemma neg_extDeriv_cotangentLiouvilleForm_apply (x : V × StrongDual ℝ V)
    (v : Fin 2 → V × StrongDual ℝ V) :
    -extDeriv cotangentLiouvilleForm x v =
      strongDualCotangentSymplecticForm (v 0) (v 1) := by
  rw [extDeriv_cotangentLiouvilleForm_apply,
    strongDualCotangentSymplecticForm_apply]
  ring

/-- Exactness with no tangent vectors supplied: at every base point, the negative exterior
derivative of the Liouville form is the canonical symplectic form as a form on the tangent
space. -/
lemma neg_extDeriv_cotangentLiouvilleForm (x : V × StrongDual ℝ V) :
    (fun v w ↦ -extDeriv cotangentLiouvilleForm x ![v, w]) =
      ⇑(strongDualCotangentSymplecticForm (V := V)) := by
  funext v w
  rw [neg_extDeriv_cotangentLiouvilleForm_apply]
  simp

end FiniteDimensional

end TauCeti

end
