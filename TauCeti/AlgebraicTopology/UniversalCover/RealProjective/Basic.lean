/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Module.Connected
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
* `TauCeti.RealProjectiveSpace.instNonemptySphere` and
  `TauCeti.RealProjectiveSpace.connectedSpace_sphere`: the covering sphere `Sⁿ` is nonempty, and
  connected once `1 ≤ n`.
* `TauCeti.RealProjectiveSpace.inductionOn`, `TauCeti.RealProjectiveSpace.lift`, and
  `TauCeti.RealProjectiveSpace.lift_unique`: elimination principles for the antipodal quotient.
* `TauCeti.RealProjectiveSpace.mk_eq_mk_iff`: two unit vectors define the same projective point
  exactly when they are equal or antipodal.
* `TauCeti.RealProjectiveSpace.isQuotientCoveringMap_mk`: the unit-sphere quotient is a quotient
  covering map with group `ℤˣ`.
* `TauCeti.RealProjectiveSpace.isCoveringMap_mk`: the underlying covering-map statement.
* `TauCeti.RealProjectiveSpace.subsingleton_zero`: `RP⁰` is a subsingleton.
* `TauCeti.RealProjectiveSpace.instPathConnectedSpace`: `RPⁿ` is path-connected for every `n`.
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

/-- The unit sphere of `EuclideanSpace ℝ (Fin (n + 1))` is nonempty. -/
instance instNonemptySphere :
    Nonempty (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
  (NormedSpace.sphere_nonempty.mpr zero_le_one).to_subtype

/-- The unit sphere of `EuclideanSpace ℝ (Fin (n + 1))` is connected once `1 ≤ n`, that is,
from the circle `S¹` on. This is the standing hypothesis behind the identification of the
deck group of the antipodal cover. -/
theorem connectedSpace_sphere (hn : 1 ≤ n) :
    ConnectedSpace (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) := by
  refine Subtype.connectedSpace (isConnected_sphere ?_ 0 zero_le_one)
  rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin, Nat.one_lt_cast]
  omega

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

/-- Real projective space is nonempty. -/
instance instNonempty : Nonempty (RealProjectiveSpace n) :=
  ⟨mk n (instNonemptySphere n).some⟩

/-- Real projective space of dimension 0, `RP⁰`, is a subsingleton consisting of a single point. -/
lemma subsingleton_zero : Subsingleton (RealProjectiveSpace 0) := by
  constructor
  intro a b
  induction a using RealProjectiveSpace.inductionOn
  induction b using RealProjectiveSpace.inductionOn
  rename_i u v
  rw [RealProjectiveSpace.mk_eq_mk_iff]
  have hu_norm : ‖(u : EuclideanSpace ℝ (Fin 1))‖ = 1 := by
    have := u.2
    rw [Metric.mem_sphere, dist_zero_right] at this
    exact this
  have hv_norm : ‖(v : EuclideanSpace ℝ (Fin 1))‖ = 1 := by
    have := v.2
    rw [Metric.mem_sphere, dist_zero_right] at this
    exact this
  have h_eval (w : EuclideanSpace ℝ (Fin 1)) : ‖w‖ = |w 0| := by
    have hsq : ‖w‖^2 = (w 0)^2 := by
      rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_one, Real.norm_eq_abs, sq_abs]
    have h2 : |w 0|^2 = (w 0)^2 := sq_abs (w 0)
    have h3 : ‖w‖^2 = |w 0|^2 := by rw [hsq, h2]
    have hpos1 : 0 ≤ ‖w‖ := norm_nonneg w
    have hpos2 : 0 ≤ |w 0| := abs_nonneg (w 0)
    nlinarith
  rw [h_eval] at hu_norm hv_norm
  have hu0 : u.1 0 = 1 ∨ u.1 0 = -1 := sq_eq_one_iff.mp (by
    have := sq_abs (u.1 0)
    rw [hu_norm] at this
    linarith)
  have hv0 : v.1 0 = 1 ∨ v.1 0 = -1 := sq_eq_one_iff.mp (by
    have := sq_abs (v.1 0)
    rw [hv_norm] at this
    linarith)
  have h_ext (x y : sphere (0 : EuclideanSpace ℝ (Fin 1)) 1)
      (h : x.1 0 = y.1 0) : x = y := by
    ext i
    fin_cases i
    exact h
  have h_ext_neg (x y : sphere (0 : EuclideanSpace ℝ (Fin 1)) 1)
      (h : x.1 0 = - y.1 0) : x = -y := by
    ext i
    fin_cases i
    exact h
  rcases hu0 with hu | hu <;> rcases hv0 with hv | hv
  · left; exact h_ext u v (by rw [hu, hv])
  · right; exact h_ext_neg u v (by rw [hu, hv, neg_neg])
  · right; exact h_ext_neg u v (by rw [hu, hv])
  · left; exact h_ext u v (by rw [hu, hv])

/-- Real projective space is path-connected for every `n`, as a nonempty subsingleton for `n = 0`
and as the continuous image of the path-connected unit sphere `Sⁿ` for `1 ≤ n`. -/
instance instPathConnectedSpace :
    PathConnectedSpace (RealProjectiveSpace n) := by
  rcases n with _ | n
  · have := subsingleton_zero
    exact ⟨inferInstance, fun x y => by
      have : x = y := Subsingleton.elim x y
      subst this
      exact Joined.refl x⟩
  · have hrank : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin (n + 1 + 1))) := by
      rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin, Nat.one_lt_cast]
      omega
    have hpc := isPathConnected_iff_pathConnectedSpace.mp
      (isPathConnected_sphere hrank (0 : EuclideanSpace ℝ (Fin (n + 1 + 1))) zero_le_one)
    have : PathConnectedSpace (sphere (0 : EuclideanSpace ℝ (Fin (n + 1 + 1))) 1) := hpc
    exact (mk_surjective (n + 1)).pathConnectedSpace (continuous_mk (n + 1))

/-- The unit-sphere projection onto real projective space is a covering map. -/
theorem isCoveringMap_mk : IsCoveringMap (mk n) :=
  (isQuotientCoveringMap_mk n).isCoveringMap

/-- The projection from the unit sphere onto real projective space is open. -/
theorem isOpenMap_mk : IsOpenMap (mk n) :=
  (isCoveringMap_mk n).isOpenMap

end RealProjectiveSpace

end


end TauCeti
