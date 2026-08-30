/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.DifferentialForm.Basic
public import TauCeti.Geometry.Symplectic.Cotangent.StrongDual
public import TauCeti.LinearAlgebra.BilinearForm.Multilinear

/-!
# The Liouville form on a linear cotangent space

The normed linear cotangent space `V × V'`, formed using the continuous dual, carries the
tautological, or Liouville, one-form

`λ_(q,p)(δq,δp) = p(δq)`.

This file constructs that differential form and proves the sign convention already used by
`TauCeti.cotangentSymplecticForm`:

`strongDualCotangentSymplecticForm = -dλ`.

Thus the canonical symplectic form on the linear cotangent model is exact. This is the linear
(vector-space) model for the exact cotangent-bundle geometry used in Lagrangian Floer homology;
nothing in this file assumes finite dimension. The construction follows McDuff--Salamon,
*Introduction to Symplectic Topology*, Section 3.2.

## Main declarations

* `TauCeti.cotangentLiouvilleFormCLM`: the Liouville form as a continuous linear map of the base
  point, which is what makes it smooth.
* `TauCeti.cotangentLiouvilleForm`: the tautological one-form on `V × StrongDual ℝ V`.
* `TauCeti.cotangentLiouvilleForm_apply`: its evaluation formula.
* `TauCeti.contDiff_cotangentLiouvilleForm`: smoothness of the form-valued map, from which
  `TauCeti.differentiable_cotangentLiouvilleForm` and
  `TauCeti.differentiableAt_cotangentLiouvilleForm` follow.
* `TauCeti.extDeriv_cotangentLiouvilleForm_apply`: the coordinate formula for the exterior
  derivative.
* `TauCeti.neg_extDeriv_cotangentLiouvilleForm`: the exactness identity `ω = -dλ`, as an equality
  of alternating two-forms, and `TauCeti.neg_extDeriv_cotangentLiouvilleForm_apply`, its
  evaluation on a pair of tangent vectors.
-/

public section

open ContinuousAlternatingMap

noncomputable section

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The Liouville form read as a continuous linear map of the base point: `(q, p)` is sent to the
one-form `(δq, δp) ↦ p(δq)`, which depends linearly and continuously on `(q, p)`. This packaging
is what gives the smoothness of `TauCeti.cotangentLiouvilleForm`. -/
noncomputable def cotangentLiouvilleFormCLM :
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

/-- The Liouville form is the underlying function of the continuous linear map
`TauCeti.cotangentLiouvilleFormCLM`. -/
lemma cotangentLiouvilleForm_eq_coe :
    cotangentLiouvilleForm (V := V) = ⇑(cotangentLiouvilleFormCLM (V := V)) := by
  funext y
  rfl

/-- The Liouville form evaluates by pairing the covector at the base point with the horizontal
component of the tangent vector. -/
@[simp]
lemma cotangentLiouvilleForm_apply (x : V × StrongDual ℝ V)
    (v : Fin 1 → V × StrongDual ℝ V) :
    cotangentLiouvilleForm x v = x.2 (v 0).1 := by
  simp [cotangentLiouvilleForm, cotangentLiouvilleFormCLM]

/-- The Liouville one-form is smooth as a form-valued function of its base point, being a
continuous linear function of that point. -/
lemma contDiff_cotangentLiouvilleForm {n : WithTop ℕ∞} :
    ContDiff ℝ n (cotangentLiouvilleForm (V := V)) := by
  rw [cotangentLiouvilleForm_eq_coe]
  exact ContinuousLinearMap.contDiff _

/-- The Liouville one-form is differentiable as a form-valued function of its base point. -/
lemma differentiable_cotangentLiouvilleForm :
    Differentiable ℝ (cotangentLiouvilleForm (V := V)) := by
  rw [cotangentLiouvilleForm_eq_coe]
  exact ContinuousLinearMap.differentiable _

/-- The Liouville one-form is differentiable at every base point. -/
lemma differentiableAt_cotangentLiouvilleForm (x : V × StrongDual ℝ V) :
    DifferentiableAt ℝ (cotangentLiouvilleForm (V := V)) x :=
  differentiable_cotangentLiouvilleForm x

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

/-- Coordinate formula for the exterior derivative of the Liouville form, evaluated on two
tangent vectors: `dλ_x(v, w) = δp_v(δq_w) - δp_w(δq_v)`. -/
@[simp]
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

/-- The canonical cotangent symplectic form is minus the exterior derivative of the Liouville
form, with the identity stated in the direction of the convention `ω = -dλ`. -/
lemma neg_extDeriv_cotangentLiouvilleForm_apply (x : V × StrongDual ℝ V)
    (v : Fin 2 → V × StrongDual ℝ V) :
    -extDeriv cotangentLiouvilleForm x v =
      strongDualCotangentSymplecticForm (v 0) (v 1) := by
  rw [extDeriv_cotangentLiouvilleForm_apply,
    strongDualCotangentSymplecticForm_apply]
  ring

/-- **Exactness of the canonical cotangent symplectic form.** At every base point, minus the
exterior derivative of the Liouville form is `TauCeti.strongDualCotangentSymplecticForm`, as an
equality of alternating two-forms on the tangent space. This is the convention `ω = -dλ`. -/
lemma neg_extDeriv_cotangentLiouvilleForm (x : V × StrongDual ℝ V) :
    -(extDeriv cotangentLiouvilleForm x).toAlternatingMap =
      (strongDualCotangentSymplecticForm (V := V)).isAlt.toAlternatingMap := by
  ext v
  -- `SymplecticForm.isAlt` is stated for `LinearMap.BilinForm.IsAlt`, so the evaluation lemma is
  -- applied as a term rather than rewritten with, to reach `LinearMap.IsAlt.toAlternatingMap`.
  rw [LinearMap.IsAlt.toAlternatingMap_apply
    (strongDualCotangentSymplecticForm (V := V)).isAlt v]
  simp

end TauCeti

end
