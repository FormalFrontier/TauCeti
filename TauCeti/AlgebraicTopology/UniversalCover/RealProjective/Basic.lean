/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.GroupWithZero.Units.Fintype
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Module.Ball.Action
public import Mathlib.Topology.Covering.Quotient

/-!
# Real projective space as an antipodal quotient

Real projective `n`-space is modelled as the quotient of the unit sphere in
`EuclideanSpace ℝ (Fin (n + 1))` by the antipodal action.  The acting group is `ℤˣ`, whose two
elements `1` and `-1` act respectively as the identity and negation.  This file defines the
quotient, characterizes equality of its representatives, and proves that the quotient map from
the sphere is a two-sheeted quotient covering map.

This is the quotient-cover prerequisite for the computation of `π₁(RPⁿ)` in
`TauCetiRoadmap/UniversalCovers/README.md`, Stage 4, item 13.  The covering argument uses
`isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul` from Mathlib's quotient-covering
API, due to Junyan Xu.  Finiteness of `ℤˣ` supplies proper discontinuity; the only additional
input is that the antipodal action on the unit sphere is free.  The scalar action on spheres and
`ne_neg_of_mem_unit_sphere` are from Mathlib's `Analysis.Normed.Module.Ball.Action`, due to Yury
Kudryashov and Heather Macbeth.

## Main declarations

* `TauCeti.RealProjectiveSpace`: real projective `n`-space as an antipodal quotient of `Sⁿ`.
* `TauCeti.RealProjectiveSpace.mk_eq_mk_iff`: two unit vectors define the same projective point
  exactly when they are equal or antipodal.
* `TauCeti.RealProjectiveSpace.isQuotientCoveringMap_mk`: the unit-sphere quotient is a quotient
  covering map with group `ℤˣ`.
* `TauCeti.RealProjectiveSpace.isCoveringMap_mk`: the underlying covering-map statement.
-/

public section

namespace TauCeti

open Metric
open Topology
open scoped EuclideanSpace

noncomputable section

universe u

namespace Sphere

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The two integer units, embedded as the two points of the real unit sphere. -/
def intUnitsToRealUnitSphere : ℤˣ →* sphere (0 : ℝ) 1 where
  toFun u := ⟨(u : ℤ), by
    obtain rfl | rfl := Int.units_eq_one_or u <;> simp⟩
  map_one' := Subtype.ext (by simp)
  map_mul' u v := Subtype.ext (by simp)

/-- The underlying real number of an integer unit regarded as a point of the real unit sphere. -/
@[simp]
theorem coe_intUnitsToRealUnitSphere (u : ℤˣ) :
    (intUnitsToRealUnitSphere u : ℝ) = (u : ℤ) :=
  (rfl)

/-- The two integer units act on every sphere centred at zero by the identity and the antipodal
map. -/
instance instMulActionIntUnitsSphere {r : ℝ} : MulAction ℤˣ (sphere (0 : E) r) where
  __ := MulAction.compHom _ intUnitsToRealUnitSphere

/-- The underlying vector of the integer-unit action is multiplication by the corresponding
integer. -/
@[simp]
theorem coe_intUnits_smul {r : ℝ} (u : ℤˣ) (x : sphere (0 : E) r) :
    ((u • x : sphere (0 : E) r) : E) = ((u : ℤ) : ℝ) • (x : E) :=
  by
    -- Unfold only the pulled-back sphere action; its scalar is then exposed to the public
    -- coercion lemma above.
    change (intUnitsToRealUnitSphere u : ℝ) • (x : E) = _
    rw [coe_intUnitsToRealUnitSphere]

/-- The nontrivial integer unit acts on a sphere as the antipodal map. -/
@[simp]
theorem negOne_smul (x : sphere (0 : E) r) : (-1 : ℤˣ) • x = -x := by
  apply Subtype.ext
  simp

/-- The integer-unit action on a sphere is continuous in the sphere variable. -/
instance instContinuousConstSMulIntUnitsSphere {r : ℝ} :
    ContinuousConstSMul ℤˣ (sphere (0 : E) r) where
  continuous_const_smul u := continuous_const_smul (intUnitsToRealUnitSphere u)

/-- The antipodal integer-unit action on the unit sphere is free. -/
instance instIsCancelSMulIntUnitsUnitSphere :
    IsCancelSMul ℤˣ (sphere (0 : E) 1) where
  right_cancel' u v x h := by
    obtain rfl | rfl := Int.units_eq_one_or u <;>
      obtain rfl | rfl := Int.units_eq_one_or v
    · rfl
    · exfalso
      exact (ne_neg_of_mem_unit_sphere ℝ x) (by simpa using h)
    · exfalso
      exact (ne_neg_of_mem_unit_sphere ℝ x) (by simpa using h.symm)
    · rfl

end Sphere

/-- Real projective `n`-space, modelled as the orbit quotient of the unit sphere `Sⁿ` under the
antipodal action of the two-element group `ℤˣ = {1, -1}`. -/
abbrev RealProjectiveSpace (n : ℕ) :=
  Quotient (MulAction.orbitRel ℤˣ
    (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))

namespace RealProjectiveSpace

variable (n : ℕ)

/-- The quotient map from the unit sphere to real projective space. -/
def mk : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 → RealProjectiveSpace n :=
  Quotient.mk
    (MulAction.orbitRel ℤˣ (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))

/-- The quotient map evaluates to the class of its representative. -/
theorem mk_apply (x : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    mk n x = Quotient.mk'' x :=
  (rfl)

/-- Every point of real projective space has a unit-vector representative. -/
theorem mk_surjective : Function.Surjective (mk n) :=
  Quotient.mk_surjective

/-- Two unit vectors define the same point of real projective space exactly when they are equal
or antipodal. -/
@[simp]
theorem mk_eq_mk_iff (x y : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    mk n x = mk n y ↔ x = y ∨ x = -y := by
  rw [mk_apply, mk_apply, Quotient.eq'', MulAction.orbitRel_apply]
  constructor
  · rintro ⟨u, rfl⟩
    obtain rfl | rfl := Int.units_eq_one_or u
    · exact Or.inl (one_smul ℤˣ y)
    · exact Or.inr (Sphere.negOne_smul y)
  · rintro (rfl | h)
    · exact ⟨1, by simp⟩
    · exact ⟨-1, by simpa using h.symm⟩

/-- Antipodal unit vectors have the same image in real projective space. -/
@[simp]
theorem mk_neg (x : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    Quotient.mk'' (-x) = mk n x :=
  (mk_eq_mk_iff n (-x) x).2 (Or.inr rfl)

/-- The unit sphere modulo the antipodal action is a quotient covering map.  Its fibres are the
two-element orbits `{x, -x}`. -/
theorem isQuotientCoveringMap_mk : IsQuotientCoveringMap (mk n) ℤˣ := by
  simpa only [mk, RealProjectiveSpace] using
    (isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul
      (G := ℤˣ) (E := sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))

/-- The unit-sphere projection onto real projective space is a quotient map. -/
theorem isQuotientMap_mk : IsQuotientMap (mk n) :=
  (isQuotientCoveringMap_mk n).toIsQuotientMap

/-- The unit-sphere projection onto real projective space is continuous. -/
theorem continuous_mk : Continuous (mk n) :=
  (isQuotientMap_mk n).continuous

/-- The unit-sphere projection onto real projective space is a covering map. -/
theorem isCoveringMap_mk : IsCoveringMap (mk n) :=
  (isQuotientCoveringMap_mk n).isCoveringMap

/-- The projection from the unit sphere onto real projective space is open. -/
theorem isOpenMap_mk : IsOpenMap (mk n) :=
  (isCoveringMap_mk n).isOpenMap

end RealProjectiveSpace

end


end TauCeti
