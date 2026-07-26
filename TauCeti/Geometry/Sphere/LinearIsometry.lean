/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Mathlib.Analysis.Normed.Module.Basic

/-!
# Linear isometries of the unit sphere

A linear isometry equivalence preserves norms, so it restricts to an equivalence of unit spheres.
This file develops that restriction independently of the manifold structure on spheres.

## Main definitions

* `TauCeti.LinearIsometryEquiv.unitSphereEquiv`: the equivalence of unit spheres obtained by
  restricting a linear isometry equivalence.

## Main results

* `TauCeti.LinearIsometryEquiv.isometry_unitSphereEquiv`: the restriction is an isometry.
* `TauCeti.LinearMap.eq_of_eqOn_unitSphere`: a real linear map is determined by its
  values on the unit sphere.
-/

public section

namespace TauCeti

open Metric Module

namespace LinearIsometryEquiv

section Seminormed

variable {R E F G : Type*} [Semiring R]
variable [SeminormedAddCommGroup E] [SeminormedAddCommGroup F] [SeminormedAddCommGroup G]
variable [Module R E] [Module R F] [Module R G]

/-- A linear isometry equivalence preserves the unit sphere: it maps unit vectors to unit vectors,
and nothing else to unit vectors. -/
theorem map_mem_unitSphere_iff (e : E ≃ₗᵢ[R] F) (x : E) :
    e x ∈ sphere (0 : F) 1 ↔ x ∈ sphere (0 : E) 1 := by
  simp

/-- A linear isometry equivalence restricts to an equivalence of the corresponding unit spheres. -/
def unitSphereEquiv (e : E ≃ₗᵢ[R] F) : sphere (0 : E) 1 ≃ sphere (0 : F) 1 :=
  e.toEquiv.subtypeEquiv fun x => (map_mem_unitSphere_iff e x).symm

@[simp]
theorem coe_unitSphereEquiv_apply (e : E ≃ₗᵢ[R] F) (x : sphere (0 : E) 1) :
    (unitSphereEquiv e x : F) = e x :=
  (rfl)

@[simp]
theorem unitSphereEquiv_symm (e : E ≃ₗᵢ[R] F) :
    (unitSphereEquiv e).symm = unitSphereEquiv e.symm :=
  (rfl)

@[simp]
theorem unitSphereEquiv_refl :
    unitSphereEquiv (_root_.LinearIsometryEquiv.refl R E) = Equiv.refl (sphere (0 : E) 1) :=
  (rfl)

@[simp]
theorem unitSphereEquiv_trans (e : E ≃ₗᵢ[R] F) (e' : F ≃ₗᵢ[R] G) :
    unitSphereEquiv (e.trans e') = (unitSphereEquiv e).trans (unitSphereEquiv e') :=
  (rfl)

/-- The restriction of a linear isometry equivalence to the unit sphere is an isometry for the
distance the sphere inherits from `E`: the action of `O(n + 1)` on `Sⁿ` is by isometries of the
round sphere. -/
theorem isometry_unitSphereEquiv (e : E ≃ₗᵢ[R] F) : Isometry (unitSphereEquiv e) :=
  Isometry.of_dist_eq fun x y => by simp [Subtype.dist_eq]

end Seminormed

end LinearIsometryEquiv

namespace LinearMap

section Normed

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A real linear map is determined by its values on the unit sphere, since every nonzero vector
is a positive multiple of a unit vector. -/
theorem eq_of_eqOn_unitSphere {f g : E →ₗ[ℝ] F} (h : Set.EqOn f g (sphere (0 : E) 1)) :
    f = g := by
  ext v
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  · have hnorm : ‖v‖ ≠ 0 := norm_ne_zero_iff.2 hv
    have hmem : ‖v‖⁻¹ • v ∈ sphere (0 : E) 1 := by
      simp [norm_smul, inv_mul_cancel₀ hnorm]
    have hsmul : ‖v‖⁻¹ • f v = ‖v‖⁻¹ • g v := by simpa using h hmem
    exact smul_right_injective F (inv_ne_zero hnorm) hsmul

end Normed

end LinearMap

end TauCeti
