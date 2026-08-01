/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.GroupWithZero.Units.Fintype
public import Mathlib.Analysis.Normed.Module.Ball.Action

/-!
# The integer-unit action on real spheres

The two units of the integers act on every sphere in a real normed space by the identity and the
antipodal map.  This file restricts Mathlib's scalar action on spheres to that action, proves its
basic coercion rules and continuity, and shows that the action on every nonzero-radius sphere is
free.

The scalar action on spheres and `ne_neg_of_mem_sphere` are from Mathlib's
`Analysis.Normed.Module.Ball.Action`, due to Yury Kudryashov and Heather Macbeth.

## Main declarations

* `TauCeti.Sphere.instMulActionIntUnitsSphere`: the action of `ℤˣ` on a real sphere.
* `TauCeti.Sphere.instContinuousConstSMulIntUnitsSphere`: continuity of the action.
* `TauCeti.Sphere.instIsCancelSMulIntUnitsSphere`: freeness on every nonzero-radius sphere.
-/

public section

namespace TauCeti

open Metric

noncomputable section

universe u

namespace Sphere

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The homomorphism that regards an integer unit as a real scalar of norm one. -/
def intUnitsToUnitSphere : ℤˣ →* sphere (0 : ℝ) 1 where
  toFun u := ⟨(u : ℤ), by
    obtain rfl | rfl := Int.units_eq_one_or u <;> simp⟩
  map_one' := Subtype.ext (by simp)
  map_mul' u v := Subtype.ext (by simp)

/-- The coercion of Mathlib's sphere action is scalar multiplication in the ambient space. -/
private theorem coe_sphere_smul {r : ℝ} (c : sphere (0 : ℝ) 1)
    (x : sphere (0 : E) r) :
    ((c • x : sphere (0 : E) r) : E) = (c : ℝ) • (x : E) :=
  (rfl)

/-- The two integer units act on every sphere centred at zero by the identity and the antipodal
map. -/
instance instMulActionIntUnitsSphere {r : ℝ} : MulAction ℤˣ (sphere (0 : E) r) where
  __ := MulAction.compHom _ intUnitsToUnitSphere

/-- The underlying vector of the integer-unit action is multiplication by the corresponding
integer. -/
@[simp]
theorem coe_intUnits_smul {r : ℝ} (u : ℤˣ) (x : sphere (0 : E) r) :
    ((u • x : sphere (0 : E) r) : E) = ((u : ℤ) : ℝ) • (x : E) :=
  by
    rw [MulAction.compHom_smul_def, coe_sphere_smul]
    rfl

/-- The restricted integer-unit action agrees with Mathlib's sphere-scalar action. -/
private theorem intUnits_smul_eq_sphere_smul {r : ℝ} (u : ℤˣ) (x : sphere (0 : E) r) :
    u • x = intUnitsToUnitSphere u • x := by
  apply Subtype.ext
  rw [coe_intUnits_smul, coe_sphere_smul]
  rfl

/-- The nontrivial integer unit acts on a sphere as the antipodal map. -/
@[simp]
theorem neg_one_smul (x : sphere (0 : E) r) : (-1 : ℤˣ) • x = -x := by
  apply Subtype.ext
  simp

/-- The integer-unit action on a sphere is continuous in the sphere variable. -/
instance instContinuousConstSMulIntUnitsSphere {r : ℝ} :
    ContinuousConstSMul ℤˣ (sphere (0 : E) r) where
  continuous_const_smul u := by
    simpa only [intUnits_smul_eq_sphere_smul] using
      (continuous_const_smul (intUnitsToUnitSphere u) :
        Continuous fun x : sphere (0 : E) r => intUnitsToUnitSphere u • x)

/-- The antipodal integer-unit action on every nonzero-radius sphere is free. -/
instance instIsCancelSMulIntUnitsSphere {r : ℝ} [NeZero r] :
    IsCancelSMul ℤˣ (sphere (0 : E) r) where
  right_cancel' u v x h := by
    obtain rfl | rfl := Int.units_eq_one_or u <;>
      obtain rfl | rfl := Int.units_eq_one_or v
    · rfl
    · exfalso
      exact (ne_neg_of_mem_sphere ℝ (NeZero.ne r) x) (by simpa using h)
    · exfalso
      exact (ne_neg_of_mem_sphere ℝ (NeZero.ne r) x) (by simpa using h.symm)
    · rfl

end Sphere

end

end TauCeti
