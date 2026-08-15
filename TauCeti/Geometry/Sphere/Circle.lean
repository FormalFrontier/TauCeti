/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Instances.Complex
public import TauCeti.Geometry.Sphere.LinearIsometry

/-!
# Identification of the two-dimensional Euclidean sphere with the complex circle

The unit sphere `sphere (0 : EuclideanSpace ℝ (Fin 2)) 1` is homeomorphic to Mathlib's complex unit
circle `Circle = {z : ℂ | ‖z‖ = 1}` via the standard orthonormal basis isometry
`Complex.orthonormalBasisOneI`.

## Main declarations

* `TauCeti.EuclideanSpace.sphereHomeomorphCircle`: the homeomorphism between the 2D Euclidean unit
  sphere and `Circle`.
* `TauCeti.EuclideanSpace.coe_sphereHomeomorphCircle_apply`: forward evaluation of the
  homeomorphism on underlying points.
* `TauCeti.EuclideanSpace.coe_sphereHomeomorphCircle_symm_apply`: backward evaluation of the
  homeomorphism on underlying points.
-/

public section

namespace TauCeti

open Metric
open scoped EuclideanSpace

namespace EuclideanSpace

noncomputable section

/-- The unit sphere in two-dimensional real Euclidean space is homeomorphic to Mathlib's complex
unit circle `Circle`.

Note: `Circle` is by definition the unit sphere `sphere (0 : ℂ) 1` in `ℂ`
(via `Submonoid.unitSphere ℂ`), so the metric and topological instances agree definitionally
with those on `sphere (0 : ℂ) 1`. The type ascription `Circle` is therefore definitionally equal
to `sphere (0 : ℂ) 1`. -/
def sphereHomeomorphCircle :
    sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ≃ₜ Circle :=
  (LinearIsometryEquiv.unitSphereIsometryEquiv Complex.orthonormalBasisOneI.repr.symm).toHomeomorph

/-- The Euclidean-circle homeomorphism is the standard orthonormal-coordinate isometry on
underlying points. -/
@[simp]
lemma coe_sphereHomeomorphCircle_apply
    (x : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :
    (sphereHomeomorphCircle x : ℂ) = Complex.orthonormalBasisOneI.repr.symm x :=
  LinearIsometryEquiv.coe_unitSphereIsometryEquiv_apply Complex.orthonormalBasisOneI.repr.symm x

/-- The inverse Euclidean-circle homeomorphism is the standard coordinate representation on
underlying points. -/
@[simp]
lemma coe_sphereHomeomorphCircle_symm_apply (z : Circle) :
    (sphereHomeomorphCircle.symm z : EuclideanSpace ℝ (Fin 2)) =
      Complex.orthonormalBasisOneI.repr (z : ℂ) := by
  have h := congrArg (fun w : Circle => (w : ℂ)) (sphereHomeomorphCircle.apply_symm_apply z)
  rw [coe_sphereHomeomorphCircle_apply] at h
  have h' := congrArg Complex.orthonormalBasisOneI.repr h
  rw [LinearIsometryEquiv.apply_symm_apply] at h'
  exact h'

end

end EuclideanSpace

end TauCeti
