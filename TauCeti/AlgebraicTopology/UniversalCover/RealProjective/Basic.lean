/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.Covering.Quotient
public import TauCeti.Analysis.Normed.Module.Ball.IntUnitsAction

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
input is that the antipodal action on the unit sphere is free.  The integer-unit sphere action is
provided by `TauCeti.Analysis.Normed.Module.Ball.IntUnitsAction`.

## Main declarations

* `TauCeti.RealProjectiveSpace`: real projective `n`-space as an antipodal quotient of `Sⁿ`.
* `TauCeti.RealProjectiveSpace.inductionOn`, `TauCeti.RealProjectiveSpace.lift`, and
  `TauCeti.RealProjectiveSpace.lift_unique`: elimination principles for the antipodal quotient.
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

/-- Real projective `n`-space, modelled as the orbit quotient of the unit sphere `Sⁿ` under the
antipodal action of the two-element group `ℤˣ = {1, -1}`. -/
def RealProjectiveSpace (n : ℕ) :=
  Quotient (MulAction.orbitRel ℤˣ
    (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))

namespace RealProjectiveSpace

variable (n : ℕ)

/-- The quotient topology on real projective space. -/
instance instTopologicalSpace : TopologicalSpace (RealProjectiveSpace n) :=
  inferInstanceAs (TopologicalSpace (Quotient (MulAction.orbitRel ℤˣ
    (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))))

/-- The quotient map from the unit sphere to real projective space. -/
def mk : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 → RealProjectiveSpace n :=
  Quotient.mk
    (MulAction.orbitRel ℤˣ (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))

/-- Every point of real projective space has a unit-vector representative. -/
theorem mk_surjective : Function.Surjective (mk n) :=
  Quotient.mk_surjective

/-- To prove a property of every point of real projective space, it suffices to prove it on the
image of every unit vector. -/
@[elab_as_elim]
protected theorem inductionOn {motive : RealProjectiveSpace n → Prop}
    (x : RealProjectiveSpace n)
    (h : ∀ y : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1, motive (mk n y)) :
    motive x :=
  Quotient.inductionOn' x h

/-- An antipodal-invariant function on the unit sphere descends to real projective space. -/
protected def lift {α : Sort*}
    (f : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 → α)
    (h : ∀ x, f (-x) = f x) : RealProjectiveSpace n → α :=
  Quotient.lift f fun x y hxy => by
    obtain ⟨u, hu⟩ :=
      MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp hxy)
    rw [← hu]
    obtain rfl | rfl := Int.units_eq_one_or u
    · rw [one_smul]
    · simpa using h y

/-- Lifting an antipodal-invariant function and applying it to a representative recovers the
original function. -/
@[simp]
protected theorem lift_mk {α : Sort*}
    (f : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 → α)
    (h : ∀ x, f (-x) = f x)
    (x : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    RealProjectiveSpace.lift n f h (mk n x) = f x :=
  (rfl)

/-- A function out of real projective space agreeing with an antipodal-invariant function on
representatives is its lift. -/
protected theorem lift_unique {α : Sort*}
    (f : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 → α)
    (h : ∀ x, f (-x) = f x)
    (g : RealProjectiveSpace n → α)
    (hg : ∀ x, g (mk n x) = f x) :
    g = RealProjectiveSpace.lift n f h := by
  funext x
  exact RealProjectiveSpace.inductionOn n x fun y =>
    (hg y).trans (RealProjectiveSpace.lift_mk n f h y).symm

/-- Two unit vectors define the same point of real projective space exactly when they are equal
or antipodal. -/
@[simp]
theorem mk_eq_mk_iff (x y : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    mk n x = mk n y ↔ x = y ∨ x = -y := by
  unfold mk RealProjectiveSpace
  rw [Quotient.eq'', MulAction.orbitRel_apply]
  constructor
  · rintro ⟨u, rfl⟩
    obtain rfl | rfl := Int.units_eq_one_or u
    · exact Or.inl (one_smul ℤˣ y)
    · exact Or.inr (Sphere.neg_one_smul y)
  · rintro (rfl | h)
    · exact ⟨1, by simp⟩
    · exact ⟨-1, by simpa using h.symm⟩

/-- Antipodal unit vectors have the same image in real projective space. -/
@[simp]
theorem mk_neg (x : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    mk n (-x) = mk n x :=
  (mk_eq_mk_iff n (-x) x).2 (Or.inr rfl)

/-- The unit sphere modulo the antipodal action is a quotient covering map.  Its fibres are the
two-element orbits `{x, -x}`. -/
theorem isQuotientCoveringMap_mk : IsQuotientCoveringMap (mk n) ℤˣ := by
  convert
    (isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul
      (G := ℤˣ) (E := sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) using 1 <;>
    rfl

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
