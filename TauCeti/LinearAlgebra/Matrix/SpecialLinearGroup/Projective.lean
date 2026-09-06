/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic

/-!
# Extension of scalars for projective special linear groups

This file defines the map on projective special linear groups induced by a ring homomorphism
and proves its identity, composition, and representative formulas.

## Main declarations

* `TauCeti.SpecialLinear.projectiveMap`: extension of scalars on projective special linear
  groups.
* `TauCeti.SpecialLinear.projectiveMap_mk`: the action on quotient representatives.
-/

public section

namespace TauCeti

namespace SpecialLinear

universe u v w

variable (n : ℕ)
variable {R : Type v} [CommRing R] {S : Type w} [CommRing S]

/-- Entrywise application of a ring homomorphism carries the center of a special linear group
into the center of the target special linear group. -/
theorem map_center_le_comap_center (f : R →+* S) :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin n) R) ≤
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin n) S)).comap
        (Matrix.SpecialLinearGroup.map f) := by
  intro g hg
  rw [Subgroup.mem_comap, Matrix.SpecialLinearGroup.mem_center_iff]
  rw [Matrix.SpecialLinearGroup.mem_center_iff] at hg
  obtain ⟨r, hr, hrg⟩ := hg
  refine ⟨f r, ?_, ?_⟩
  · rw [← map_pow, hr, map_one]
  · rw [Matrix.SpecialLinearGroup.map_apply_coe, ← hrg]
    ext i j
    by_cases hij : i = j <;>
      simp [RingHom.mapMatrix_apply, Matrix.scalar_apply, hij]

/-- Extension of scalars on projective special linear groups. -/
noncomputable def projectiveMap (f : R →+* S) :
    Matrix.ProjectiveSpecialLinearGroup (Fin n) R →*
      Matrix.ProjectiveSpecialLinearGroup (Fin n) S :=
  QuotientGroup.map
    (Subgroup.center (Matrix.SpecialLinearGroup (Fin n) R))
    (Subgroup.center (Matrix.SpecialLinearGroup (Fin n) S))
    (Matrix.SpecialLinearGroup.map f) (map_center_le_comap_center n f)

/-- Extension of scalars on projective special linear groups is computed on representatives by
entrywise application of the ring homomorphism. -/
@[simp]
theorem projectiveMap_mk (f : R →+* S) (g : Matrix.SpecialLinearGroup (Fin n) R) :
    projectiveMap n f (QuotientGroup.mk g) =
      QuotientGroup.mk (Matrix.SpecialLinearGroup.map f g) := by
  exact QuotientGroup.map_mk _ _ _ _ g

/-- Extension of scalars by the identity is the identity on projective special linear groups. -/
@[simp]
theorem projectiveMap_id :
    projectiveMap n (RingHom.id R) = MonoidHom.id _ := by
  rw [projectiveMap]
  exact QuotientGroup.map_id _ _

/-- Successive extensions of scalars compose on projective special linear groups. -/
@[simp]
theorem projectiveMap_comp {T : Type u} [CommRing T] (f : R →+* S) (g : S →+* T) :
    (projectiveMap n g).comp (projectiveMap n f) = projectiveMap n (g.comp f) := by
  rw [projectiveMap, projectiveMap, projectiveMap]
  exact QuotientGroup.map_comp_map _ _ _ _ _ _ _ _

end SpecialLinear

end TauCeti
