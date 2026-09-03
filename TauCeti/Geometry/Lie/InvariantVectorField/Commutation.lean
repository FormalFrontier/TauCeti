/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.ParametricFDeriv
public import TauCeti.Geometry.Lie.Exponential.Derivative.Basic
public import TauCeti.Geometry.Lie.RightInvariantVectorField
public import TauCeti.Geometry.Manifold.VectorField.LieBracket
public import TauCeti.Geometry.Lie.Interior

/-!
# Commutation of left- and right-invariant vector fields

This file proves that left- and right-invariant differentiation commute. The proof uses Clairaut
symmetry for a smooth scalar function evaluated on two multiplied exponential lines, then uses
the tangent-vector/point-derivation equivalence to identify the vector-field bracket.

This supplies a prerequisite for Deliverable A, Layer 1 of
`TauCetiRoadmap/RepresentationTheory/LieGroups/README.md`.

## Main results

* `contDiff_comp_mulInvariantExp_mul_mulInvariantExp`: a vector-valued function on two exponential
  lines multiplied around a fixed group element is smooth in both parameters.
* `spatialFDeriv_mulInvariantExp_mul_mulInvariantExp` and
  `timeFDeriv_mulInvariantExp_mul_mulInvariantExp`: identify its two partial derivatives with
  left- and right-invariant differentiation.
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

section Complete

variable [CompleteSpace E]
variable {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']

/-- A smooth vector-valued function evaluated on two exponential lines multiplied around a fixed
group element is smooth in both parameters. -/
theorem contDiff_comp_mulInvariantExp_mul_mulInvariantExp
    {f : G → F'} (hf : ContMDiff I 𝓘(ℝ, F') ∞ f) (g : G)
    (X Y : GroupLieAlgebra I G) :
    let _ : T2Space G := t2Space_of_lieGroup (I := I) (n := ∞)
    ContDiff ℝ ∞ (fun p : ℝ × ℝ =>
      f (mulInvariantExp (I := I) (G := G) (p.1 • X) * g *
        mulInvariantExp (I := I) (G := G) (p.2 • Y))) := by
  let _ : T2Space G := t2Space_of_lieGroup (I := I) (n := ∞)
  dsimp only
  exact (hf.comp (contMDiff_mulInvariantExp_smul_mul_mul_mulInvariantExp_smul g X Y)).contDiff

/-- Differentiating the second exponential parameter gives left-invariant differentiation by
`Y`. -/
theorem spatialFDeriv_mulInvariantExp_mul_mulInvariantExp
    (f : C^∞⟮I, G; 𝓘(ℝ, F'), F'⟯) (g : G)
    (X Y : GroupLieAlgebra I G) (s : ℝ) :
    let _ : T2Space G := t2Space_of_lieGroup (I := I) (n := ∞)
    spatialFDeriv (fun p : ℝ × ℝ =>
      f (mulInvariantExp (I := I) (G := G) (p.1 • X) * g *
        mulInvariantExp (I := I) (G := G) (p.2 • Y))) 0 s 1 =
      mvfderiv I f (mulInvariantExp (I := I) (G := G) (s • X) * g)
        (mulInvariantVectorField Y
          (mulInvariantExp (I := I) (G := G) (s • X) * g)) := by
  let _ : T2Space G := t2Space_of_lieGroup (I := I) (n := ∞)
  dsimp only
  let F : ℝ × ℝ → F' := fun p =>
    f (mulInvariantExp (I := I) (G := G) (p.1 • X) * g *
      mulInvariantExp (I := I) (G := G) (p.2 • Y))
  have hF : ContDiff ℝ 2 F :=
    (contDiff_comp_mulInvariantExp_mul_mulInvariantExp f.contMDiff g X Y).of_le
      (by simp)
  have hFdiff : DifferentiableAt ℝ F (s, 0) := hF.differentiable (by norm_num) (s, 0)
  have hpartial := (hasFDerivAt_timeSlice hFdiff).hasDerivAt
  have hfAt := f.contMDiff.mdifferentiable (by simp)
    (mulInvariantExp (I := I) (G := G) (s • X) * g) |>.hasMFDerivAt
  have hdirection := HasMFDerivAt.hasDerivAt_comp_mul_mulInvariantExp_smul_zero hfAt Y
  have hdirection' : HasDerivAt (fun t => F (s, t))
      ((mfderiv I 𝓘(ℝ, F') f (mulInvariantExp (I := I) (G := G) (s • X) * g))
        (mulInvariantVectorField Y
          (mulInvariantExp (I := I) (G := G) (s • X) * g))) 0 := by
    -- Naming the hypothesis makes the canonical real scalar-structure identification explicit.
    exact hdirection
  rw [mvfderiv_apply_eq_mfderiv_apply]
  exact hpartial.unique hdirection'

/-- Differentiating the first exponential parameter gives right-invariant differentiation by
`X`. -/
theorem timeFDeriv_mulInvariantExp_mul_mulInvariantExp
    (f : C^∞⟮I, G; 𝓘(ℝ, F'), F'⟯) (g : G)
    (X Y : GroupLieAlgebra I G) (t : ℝ) :
    let _ : T2Space G := t2Space_of_lieGroup (I := I) (n := ∞)
    timeFDeriv (fun p : ℝ × ℝ =>
      f (mulInvariantExp (I := I) (G := G) (p.1 • X) * g *
        mulInvariantExp (I := I) (G := G) (p.2 • Y))) 0 t =
      mvfderiv I f (g * mulInvariantExp (I := I) (G := G) (t • Y))
        (mulRightInvariantVectorField X
          (g * mulInvariantExp (I := I) (G := G) (t • Y))) := by
  let _ : T2Space G := t2Space_of_lieGroup (I := I) (n := ∞)
  dsimp only
  let F : ℝ × ℝ → F' := fun p =>
    f (mulInvariantExp (I := I) (G := G) (p.1 • X) * g *
      mulInvariantExp (I := I) (G := G) (p.2 • Y))
  have hF : ContDiff ℝ 2 F :=
    (contDiff_comp_mulInvariantExp_mul_mulInvariantExp f.contMDiff g X Y).of_le
      (by simp)
  have hFdiff : DifferentiableAt ℝ F (0, t) := hF.differentiable (by norm_num) (0, t)
  have hpartial := hasDerivAt_parameterCurve hFdiff
  have hfAt := f.contMDiff.mdifferentiable (by simp)
    (g * mulInvariantExp (I := I) (G := G) (t • Y)) |>.hasMFDerivAt
  have hdirection := HasMFDerivAt.hasDerivAt_comp_mulInvariantExp_smul_mul_zero hfAt X
  have hdirection' : HasDerivAt (fun s => F (s, t))
      ((mfderiv I 𝓘(ℝ, F') f (g * mulInvariantExp (I := I) (G := G) (t • Y)))
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

/-- Left- and right-invariant scalar differentiation commute at every group point. -/
theorem mvfderiv_mulRightInvariantVectorField_mulInvariantVectorField_commute
    (f : C^∞⟮I, G; ℝ⟯) (g : G) (X Y : GroupLieAlgebra I G) :
    mvfderiv I (tangentToLeftInvariantDerivation Y f) g
        (mulRightInvariantVectorField X g) =
      mvfderiv I (rightInvariantDerivative X f) g
        (mulInvariantVectorField Y g) := by
  let _ : T2Space G := t2Space_of_lieGroup (I := I) (n := ∞)
  let γX : ℝ → G := fun t => mulInvariantExp (I := I) (G := G) (t • X)
  let γY : ℝ → G := fun t => mulInvariantExp (I := I) (G := G) (t • Y)
  let F : ℝ × ℝ → ℝ := fun p => f (γX p.1 * g * γY p.2)
  let LYf := tangentToLeftInvariantDerivation (I := I) (G := G) Y f
  let RXf := rightInvariantDerivative (I := I) X f
  have hF : ContDiff ℝ 2 F :=
    (contDiff_comp_mulInvariantExp_mul_mulInvariantExp f.contMDiff g X Y).of_le
      (by simp)
  -- Identify the two partial derivatives with the invariant directional derivatives.
  have hspaceFun : (fun s => spatialFDeriv F 0 s 1) =
      fun s => LYf (γX s * g) := by
    funext s
    simpa only [LYf, tangentToLeftInvariantDerivation_apply] using
      spatialFDeriv_mulInvariantExp_mul_mulInvariantExp f g X Y s
  have htimeFun : timeFDeriv F 0 =
      fun t => RXf (g * γY t) := by
    funext t
    simpa only [RXf, rightInvariantDerivative_apply] using
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
    f.contMDiff.contMDiffAt
    (by simp)
    ((contMDiff_mulRightInvariantVectorField_infty X).mdifferentiable
      (by simp)).mdifferentiableAt
    ((contMDiff_mulInvariantVectorField_infty Y).mdifferentiable
      (by simp)).mdifferentiableAt]
  have hcomm :=
    mvfderiv_mulRightInvariantVectorField_mulInvariantVectorField_commute f g X Y
  have hLY : (fun y => mvfderiv I f y (mulInvariantVectorField Y y)) =
      tangentToLeftInvariantDerivation Y f := by
    funext y
    exact (tangentToLeftInvariantDerivation_apply Y f y).symm
  have hRX : (fun y => mvfderiv I f y (mulRightInvariantVectorField X y)) =
      rightInvariantDerivative X f := by
    funext y
    exact (rightInvariantDerivative_apply X f y).symm
  rw [hLY, hRX]
  exact sub_eq_zero.mpr hcomm

/-- Left- and right-invariant vector fields commute everywhere, with the bracket arguments in the
opposite order. -/
@[simp]
theorem mlieBracket_mulInvariantVectorField_mulRightInvariantVectorField
    (X Y : GroupLieAlgebra I G) :
    mlieBracket I (mulInvariantVectorField X) (mulRightInvariantVectorField Y) = 0 := by
  rw [mlieBracket_swap, mlieBracket_mulRightInvariantVectorField_mulInvariantVectorField, neg_zero]

end TauCeti.Lie
