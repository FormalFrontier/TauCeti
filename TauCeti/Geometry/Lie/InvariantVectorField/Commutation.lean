/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import TauCeti.Analysis.Calculus.ParametricFDeriv
import TauCeti.Geometry.Lie.Exponential.Derivative.Basic
public import TauCeti.Geometry.Lie.RightInvariantVectorField
public import TauCeti.Geometry.Manifold.VectorField.LieBracket
import TauCeti.Geometry.Lie.Interior

/-!
# Commutation of left- and right-invariant vector fields

This file proves that left- and right-invariant differentiation commute. The proof uses Clairaut
symmetry for a smooth scalar function evaluated on two multiplied exponential lines, then uses
the tangent-vector/point-derivation equivalence to identify the vector-field bracket.

This supplies a prerequisite for Deliverable A, Layer 1 of
`TauCetiRoadmap/RepresentationTheory/LieGroups/README.md`.

## Main results

* `mvfderiv_mulRightInvariantVectorField_mulInvariantVectorField_commute`: left- and
  right-invariant scalar differentiation commute at every group point.
* `mlieBracket_mulRightInvariantVectorField_mulInvariantVectorField`: the corresponding
  vector-field bracket vanishes everywhere.
* `mlieBracket_mulInvariantVectorField_mulRightInvariantVectorField`: the same vanishing result
  with the bracket arguments reversed.

## References

* [Lie groups and the Lie algebra correspondence roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieGroups/README.md),
  Deliverable A, Layer 1, "The infinitesimal adjoint".
-/

public section

noncomputable section

namespace TauCeti.Lie

open Manifold VectorField
open scoped ContDiff Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G]

attribute [local instance] LieGroup.minSmoothnessThree
attribute [local instance] ContMDiffMul.boundarylessManifold

private theorem two_le_infinite_smoothness :
    ((2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω) :=
  ENat.natCast_le_of_coe_top_le_withTop le_rfl 2

section Complete

variable [CompleteSpace E]

/-- A smooth scalar function evaluated on two exponential lines multiplied around a fixed group
element is smooth in both parameters. -/
private theorem contDiff_comp_mulInvariantExp_mul_mulInvariantExp
    {f : G → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (g : G)
    (X Y : GroupLieAlgebra I G) :
    let _ : T2Space G := t2Space_of_lieGroup (I := I) (n := ∞)
    ContDiff ℝ 2 (fun p : ℝ × ℝ =>
      f (mulInvariantExp (I := I) (G := G) (p.1 • X) * g *
        mulInvariantExp (I := I) (G := G) (p.2 • Y))) := by
  let _ : T2Space G := t2Space_of_lieGroup (I := I) (n := ∞)
  dsimp only
  exact (hf.comp (contMDiff_mulInvariantExp_smul_mul_mul_mulInvariantExp_smul g X Y)).contDiff.of_le
    two_le_infinite_smoothness

private theorem spatialFDeriv_mulInvariantExp_mul_mulInvariantExp
    (f : C^∞⟮I, G; ℝ⟯) (g : G) (X Y : GroupLieAlgebra I G) (s : ℝ) :
    let _ : T2Space G := t2Space_of_lieGroup (I := I) (n := ∞)
    spatialFDeriv (fun p : ℝ × ℝ =>
      f (mulInvariantExp (I := I) (G := G) (p.1 • X) * g *
        mulInvariantExp (I := I) (G := G) (p.2 • Y))) 0 s 1 =
      mvfderiv I f (mulInvariantExp (I := I) (G := G) (s • X) * g)
        (mulInvariantVectorField Y
          (mulInvariantExp (I := I) (G := G) (s • X) * g)) := by
  let _ : T2Space G := t2Space_of_lieGroup (I := I) (n := ∞)
  dsimp only
  let F : ℝ × ℝ → ℝ := fun p =>
    f (mulInvariantExp (I := I) (G := G) (p.1 • X) * g *
      mulInvariantExp (I := I) (G := G) (p.2 • Y))
  have hF : ContDiff ℝ 2 F :=
    contDiff_comp_mulInvariantExp_mul_mulInvariantExp f.contMDiff g X Y
  have hFdiff : DifferentiableAt ℝ F (s, 0) := hF.differentiable (by norm_num) (s, 0)
  have hslice : DifferentiableAt ℝ (fun t => F (s, t)) 0 :=
    hFdiff.comp 0 ((differentiableAt_const s).prodMk differentiableAt_id)
  have hpartial := hslice.hasDerivAt
  rw [← fderiv_apply_one_eq_deriv, fderiv_timeSlice hFdiff] at hpartial
  have hfAt := f.contMDiff.mdifferentiable (by simp)
    (mulInvariantExp (I := I) (G := G) (s • X) * g) |>.hasMFDerivAt
  have hdirection := HasMFDerivAt.hasDerivAt_comp_mul_mulInvariantExp_smul_zero hfAt Y
  have hdirection' : HasDerivAt (fun t => F (s, t))
      ((mfderiv I 𝓘(ℝ, ℝ) f (mulInvariantExp (I := I) (G := G) (s • X) * g))
        (mulInvariantVectorField Y
          (mulInvariantExp (I := I) (G := G) (s • X) * g))) 0 := by
    -- Naming the hypothesis makes the canonical real scalar-structure identification explicit.
    exact hdirection
  rw [mvfderiv_apply_eq_mfderiv_apply]
  exact hpartial.unique hdirection'

private theorem timeFDeriv_mulInvariantExp_mul_mulInvariantExp
    (f : C^∞⟮I, G; ℝ⟯) (g : G) (X Y : GroupLieAlgebra I G) (t : ℝ) :
    let _ : T2Space G := t2Space_of_lieGroup (I := I) (n := ∞)
    timeFDeriv (fun p : ℝ × ℝ =>
      f (mulInvariantExp (I := I) (G := G) (p.1 • X) * g *
        mulInvariantExp (I := I) (G := G) (p.2 • Y))) 0 t =
      mvfderiv I f (g * mulInvariantExp (I := I) (G := G) (t • Y))
        (mulRightInvariantVectorField X
          (g * mulInvariantExp (I := I) (G := G) (t • Y))) := by
  let _ : T2Space G := t2Space_of_lieGroup (I := I) (n := ∞)
  dsimp only
  let F : ℝ × ℝ → ℝ := fun p =>
    f (mulInvariantExp (I := I) (G := G) (p.1 • X) * g *
      mulInvariantExp (I := I) (G := G) (p.2 • Y))
  have hF : ContDiff ℝ 2 F :=
    contDiff_comp_mulInvariantExp_mul_mulInvariantExp f.contMDiff g X Y
  have hFdiff : DifferentiableAt ℝ F (0, t) := hF.differentiable (by norm_num) (0, t)
  have hpartial := hasDerivAt_parameterCurve hFdiff
  have hfAt := f.contMDiff.mdifferentiable (by simp)
    (g * mulInvariantExp (I := I) (G := G) (t • Y)) |>.hasMFDerivAt
  have hdirection := HasMFDerivAt.hasDerivAt_comp_mulInvariantExp_smul_mul_zero hfAt X
  have hdirection' : HasDerivAt (fun s => F (s, t))
      ((mfderiv I 𝓘(ℝ, ℝ) f (g * mulInvariantExp (I := I) (G := G) (t • Y)))
        (mulRightInvariantVectorField X
          (g * mulInvariantExp (I := I) (G := G) (t • Y)))) 0 := by
    -- Reassociate the product while naming the canonical real scalar-structure identification.
    rw [show (fun s => F (s, t)) = fun s =>
      f (mulInvariantExp (I := I) (G := G) (s • X) *
        (g * mulInvariantExp (I := I) (G := G) (t • Y))) by
      funext s
      simp only [F, mul_assoc]]
    exact hdirection
  rw [mvfderiv_apply_eq_mfderiv_apply]
  exact hpartial.unique hdirection'

/-- Left- and right-invariant scalar differentiation commute at every group point. This is
Clairaut symmetry for `(s, t) ↦ f (exp(sX) * g * exp(tY))`. -/
theorem mvfderiv_mulRightInvariantVectorField_mulInvariantVectorField_commute
    (f : C^∞⟮I, G; ℝ⟯) (g : G) (X Y : GroupLieAlgebra I G) :
    mvfderiv I (fun h => mvfderiv I f h (mulInvariantVectorField Y h)) g
        (mulRightInvariantVectorField X g) =
      mvfderiv I (fun h => mvfderiv I f h (mulRightInvariantVectorField X h)) g
        (mulInvariantVectorField Y g) := by
  let _ : T2Space G := t2Space_of_lieGroup (I := I) (n := ∞)
  let γX : ℝ → G := fun t => mulInvariantExp (I := I) (G := G) (t • X)
  let γY : ℝ → G := fun t => mulInvariantExp (I := I) (G := G) (t • Y)
  let F : ℝ × ℝ → ℝ := fun p => f (γX p.1 * g * γY p.2)
  let LYf : C^∞⟮I, G; ℝ⟯ :=
    ⟨fun h => mvfderiv I f h (mulInvariantVectorField Y h),
      contMDiff_mvfderiv_mulInvariantVectorField Y f⟩
  let RXf : C^∞⟮I, G; ℝ⟯ :=
    ⟨fun h => mvfderiv I f h (mulRightInvariantVectorField X h),
      contMDiff_mvfderiv_mulRightInvariantVectorField X f⟩
  have hF : ContDiff ℝ 2 F :=
    contDiff_comp_mulInvariantExp_mul_mulInvariantExp f.contMDiff g X Y
  -- Identify the two partial derivatives with the invariant directional derivatives.
  have hspaceFun : (fun s => spatialFDeriv F 0 s 1) =
      fun s => LYf (γX s * g) := by
    funext s
    simpa only [LYf, ContMDiffMap.coeFn_mk] using
      spatialFDeriv_mulInvariantExp_mul_mulInvariantExp f g X Y s
  have htimeFun : timeFDeriv F 0 =
      fun t => RXf (g * γY t) := by
    funext t
    simpa only [RXf, ContMDiffMap.coeFn_mk] using
      timeFDeriv_mulInvariantExp_mul_mulInvariantExp f g X Y t
  -- Clairaut symmetry equates the derivatives of those two partial-derivative functions.
  have hFmin : ContDiffAt ℝ (minSmoothness ℝ 2) F (0, 0) := by
    simpa using hF.contDiffAt
  have hmixed := deriv_spatialFDeriv_apply (F := F) (x := (0 : ℝ)) (w := (1 : ℝ)) hFmin
  rw [hspaceFun, htimeFun, fderiv_apply_one_eq_deriv] at hmixed
  -- Transport the two one-variable derivatives back to manifold derivatives at `g`.
  have hLY := HasMFDerivAt.hasDerivAt_comp_mulInvariantExp_smul_mul_zero
    (LYf.contMDiff.mdifferentiable (by simp) g |>.hasMFDerivAt) X
  have hRX := HasMFDerivAt.hasDerivAt_comp_mul_mulInvariantExp_smul_zero
    (RXf.contMDiff.mdifferentiable (by simp) g |>.hasMFDerivAt) Y
  rw [hLY.deriv, hRX.deriv] at hmixed
  rw [mvfderiv_apply_eq_mfderiv_apply, mvfderiv_apply_eq_mfderiv_apply]
  exact hmixed

end Complete

variable [FiniteDimensional ℝ E]

/-- Right- and left-invariant vector fields commute everywhere. -/
@[simp]
theorem mlieBracket_mulRightInvariantVectorField_mulInvariantVectorField
    (X Y : GroupLieAlgebra I G) :
    mlieBracket I (mulRightInvariantVectorField X) (mulInvariantVectorField Y) = 0 := by
  let _ : T2Space G := t2Space_of_lieGroup (I := I) (n := ∞)
  funext g
  apply tangentToPointDerivation_injective (I := I) g
  rw [Pi.zero_apply, map_zero]
  ext f
  rw [Derivation.zero_apply]
  -- The pointed smooth-map argument is a different bundle from `ContMDiffMap`, so the public
  -- `tangentToPointDerivation_apply` lemma does not rewrite this coercion directly.
  change mvfderiv I f g
    (mlieBracket I (mulRightInvariantVectorField X) (mulInvariantVectorField Y) g) = 0
  rw [mvfderiv_mlieBracket
    (f := (f : G → ℝ))
    (V := mulRightInvariantVectorField X)
    (W := mulInvariantVectorField Y)
    (x := g)
    (f.contMDiff.contMDiffAt.of_le two_le_infinite_smoothness)
    (by simp)
    ((contMDiff_mulRightInvariantVectorField_infty X).mdifferentiable
      (by simp)).mdifferentiableAt
    ((contMDiff_mulInvariantVectorField_infty Y).mdifferentiable
      (by simp)).mdifferentiableAt]
  exact sub_eq_zero.mpr
    (mvfderiv_mulRightInvariantVectorField_mulInvariantVectorField_commute f g X Y)

/-- Left- and right-invariant vector fields commute everywhere, with the bracket arguments in the
opposite order. -/
@[simp]
theorem mlieBracket_mulInvariantVectorField_mulRightInvariantVectorField
    (X Y : GroupLieAlgebra I G) :
    mlieBracket I (mulInvariantVectorField X) (mulRightInvariantVectorField Y) = 0 := by
  rw [mlieBracket_swap, mlieBracket_mulRightInvariantVectorField_mulInvariantVectorField, neg_zero]

end TauCeti.Lie
