/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Mathlib.Analysis.Normed.Module.Basic

/-!
# Linear isometries of the unit sphere

A linear isometry equivalence preserves norms, so it restricts to a self-equivalence of the unit
sphere. This file develops that restriction independently of the manifold structure on spheres.

## Main definitions

* `TauCeti.LinearIsometryEquiv.unitSphereEquiv`: the self-equivalence of the unit sphere
  obtained by restricting a linear isometry equivalence.

## Main results

* `TauCeti.LinearIsometryEquiv.isometry_unitSphereEquiv`: the restriction is an isometry.
* `TauCeti.LinearIsometryEquiv.eq_of_eqOn_unitSphere`: a real linear isometry equivalence is
  determined by its values on the unit sphere.
-/

public section

namespace TauCeti

open Metric Module

namespace LinearIsometryEquiv

section Seminormed

variable {R E : Type*} [Semiring R] [SeminormedAddCommGroup E] [Module R E]

/-- A linear isometry equivalence preserves the unit sphere: it maps unit vectors to unit vectors,
and nothing else to unit vectors. -/
theorem map_mem_unitSphere_iff (e : E ≃ₗᵢ[R] E) (x : E) :
    e x ∈ sphere (0 : E) 1 ↔ x ∈ sphere (0 : E) 1 := by
  simp

/-- A linear isometry equivalence of `E` restricts to a self-equivalence of the unit sphere. -/
@[expose] def unitSphereEquiv (e : E ≃ₗᵢ[R] E) : sphere (0 : E) 1 ≃ sphere (0 : E) 1 :=
  e.toEquiv.subtypeEquiv fun x => (map_mem_unitSphere_iff e x).symm

@[simp]
theorem coe_unitSphereEquiv_apply (e : E ≃ₗᵢ[R] E) (x : sphere (0 : E) 1) :
    (unitSphereEquiv e x : E) = e x :=
  (rfl)

@[simp]
theorem unitSphereEquiv_symm (e : E ≃ₗᵢ[R] E) :
    (unitSphereEquiv e).symm = unitSphereEquiv e.symm :=
  (rfl)

@[simp]
theorem unitSphereEquiv_refl :
    unitSphereEquiv (_root_.LinearIsometryEquiv.refl R E) = Equiv.refl (sphere (0 : E) 1) :=
  (rfl)

@[simp]
theorem unitSphereEquiv_trans (e e' : E ≃ₗᵢ[R] E) :
    unitSphereEquiv (e.trans e') = (unitSphereEquiv e).trans (unitSphereEquiv e') :=
  (rfl)

/-- The restriction of a linear isometry equivalence to the unit sphere is an isometry for the
distance the sphere inherits from `E`: the action of `O(n + 1)` on `Sⁿ` is by isometries of the
round sphere. -/
theorem isometry_unitSphereEquiv (e : E ≃ₗᵢ[R] E) : Isometry (unitSphereEquiv e) :=
  Isometry.of_dist_eq fun x y => by simp [Subtype.dist_eq]

end Seminormed

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A linear isometry equivalence is determined by its values on the unit sphere, since every
nonzero vector is a positive multiple of a unit vector. -/
theorem eq_of_eqOn_unitSphere {e e' : E ≃ₗᵢ[ℝ] E} (h : Set.EqOn e e' (sphere (0 : E) 1)) :
    e = e' := by
  ext v
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  · have hnorm : ‖v‖ ≠ 0 := norm_ne_zero_iff.2 hv
    have hmem : ‖v‖⁻¹ • v ∈ sphere (0 : E) 1 := by
      simp [norm_smul, inv_mul_cancel₀ hnorm]
    have hsmul : ‖v‖⁻¹ • e v = ‖v‖⁻¹ • e' v := by simpa using h hmem
    exact smul_right_injective E (inv_ne_zero hnorm) hsmul

end Normed

end LinearIsometryEquiv

end TauCeti
