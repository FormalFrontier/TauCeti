/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Complex.Conformal.Hyperbolic.Triangle
public import TauCeti.Analysis.Complex.Conformal.UnitDisc.Automorphism.Basic
public import Mathlib.Topology.MetricSpace.Isometry

/-!
# The Poincaré metric space on the complex unit disc

The symmetry, nonnegativity, vanishing-on-the-diagonal and triangle-inequality lemmas already
proved for the hyperbolic (Poincaré) distance `hyperbolicDist` on the open unit disc
(`HyperbolicDistance.lean`, `HyperbolicTriangle.lean`) are exactly the metric-space axioms.
This file records them as an actual `MetricSpace` instance.

The instance cannot be attached to `Complex.UnitDisc`, which already carries the Euclidean
subspace metric. Following the standard Mathlib type-synonym idiom (as for `OrderDual`,
`Lex`, …), we introduce

* `PoincareDisc` — a type synonym for `Complex.UnitDisc`, with the reinterpretation maps
  `Complex.UnitDisc.toPoincare` and `PoincareDisc.toUnitDisc` (mutually inverse identity
  equivalences);
* `PoincareDisc.instMetricSpace` — the Poincaré `MetricSpace`, with
  `dist z w = hyperbolicDist z w` on the underlying disc points (`PoincareDisc.dist_eq`).

The disc automorphisms are then recorded as genuine self-isometries of this metric space,
validating that the Poincaré distance is the automorphism-invariant metric:

* `PoincareDisc.isometry_of_hyperbolicDist_eq` — a hyperbolic-distance-preserving self-map of
  the unit disc induces a self-isometry of the Poincaré disc;
* `PoincareDisc.isometry_unitDiscMoebius`,
  `PoincareDisc.isometry_unitDiscStandardAutomorphismEquiv` — the disc Moebius factors and the
  standard automorphisms as Poincaré isometries.

This completes the conformal-mapping roadmap's L2 target "the hyperbolic / Poincaré metric on
`𝔻`" (see `ConformalMapping/README.md`), discharging the `MetricSpace`-instance step that the
docstrings of `HyperbolicDistance.lean` and `HyperbolicTriangle.lean` deferred as future work.
It reuses Tau Ceti's hyperbolic-distance and disc-automorphism API. As with the rest of the
L0--L3 conformal-mapping material, it is coordinated with the upstream Mathlib RMT effort
leanprover-community/mathlib4#33505 and should be refactored to upstream API if that work lands
a human-curated Poincaré metric. Mathlib has the hyperbolic metric on the upper half-plane
(`Analysis/Complex/UpperHalfPlane`), but no Poincaré metric on the disc.
-/

public section

namespace TauCeti

open Complex Metric Set

/-- The complex open unit disc equipped with the hyperbolic (Poincaré) metric.

This is a type synonym for `Complex.UnitDisc`, introduced so that the Poincaré distance can be
registered as a `MetricSpace` instance without clashing with the Euclidean subspace metric that
`Complex.UnitDisc` already carries. Move between the two views with the identity equivalences
`Complex.UnitDisc.toPoincare` and `PoincareDisc.toUnitDisc`. -/
@[expose] def PoincareDisc : Type := Complex.UnitDisc

namespace PoincareDisc

/-- Reinterpret a point of the unit disc as a point of the Poincaré disc (the identity map). -/
@[expose] def _root_.Complex.UnitDisc.toPoincare : Complex.UnitDisc ≃ PoincareDisc := Equiv.refl _

/-- Reinterpret a point of the Poincaré disc as a point of the unit disc (the identity map). -/
@[expose] def toUnitDisc : PoincareDisc ≃ Complex.UnitDisc := Complex.UnitDisc.toPoincare.symm

@[simp]
lemma toUnitDisc_toPoincare (z : Complex.UnitDisc) :
    toUnitDisc (Complex.UnitDisc.toPoincare z) = z := rfl

@[simp]
lemma toPoincare_toUnitDisc (z : PoincareDisc) :
    Complex.UnitDisc.toPoincare (toUnitDisc z) = z := rfl

/-- Every point of the Poincaré disc lies in the open unit ball. -/
lemma coe_mem_ball (z : PoincareDisc) : (toUnitDisc z : ℂ) ∈ ball (0 : ℂ) 1 :=
  mem_ball_zero_iff.mpr (toUnitDisc z).norm_lt_one

/-- The Poincaré (hyperbolic) metric space on the complex open unit disc. Its distance is the
hyperbolic distance `hyperbolicDist` on the underlying disc points. -/
noncomputable instance instMetricSpace : MetricSpace PoincareDisc where
  dist z w := hyperbolicDist (toUnitDisc z : ℂ) (toUnitDisc w : ℂ)
  dist_self z := hyperbolicDist_self _
  dist_comm z w := hyperbolicDist_comm _ _
  dist_triangle z w u :=
    hyperbolicDist_triangle (coe_mem_ball z) (coe_mem_ball u) (coe_mem_ball w)
  eq_of_dist_eq_zero {z w} h :=
    toUnitDisc.injective <| Complex.UnitDisc.coe_injective <|
      (hyperbolicDist_eq_zero_iff_of_mem_ball (coe_mem_ball z) (coe_mem_ball w)).mp h

/-- The Poincaré distance between two disc points is their hyperbolic distance. -/
@[simp]
lemma dist_eq (z w : PoincareDisc) :
    dist z w = hyperbolicDist (toUnitDisc z : ℂ) (toUnitDisc w : ℂ) := rfl

/-- The Poincaré distance from a point to the origin has the closed form `artanh ‖z‖`. -/
lemma dist_toPoincare_zero_right (z : PoincareDisc) :
    dist z (Complex.UnitDisc.toPoincare 0) = Real.artanh ‖(toUnitDisc z : ℂ)‖ := by
  rw [dist_eq, toUnitDisc_toPoincare, Complex.UnitDisc.coe_zero, hyperbolicDist_zero_right]

/-- A hyperbolic-distance-preserving self-map of the unit disc induces a self-isometry of the
Poincaré disc (transported along the identification `Complex.UnitDisc.toPoincare`). -/
theorem isometry_of_hyperbolicDist_eq {g : Complex.UnitDisc → Complex.UnitDisc}
    (hg : ∀ z w : Complex.UnitDisc,
      hyperbolicDist (g z : ℂ) (g w : ℂ) = hyperbolicDist (z : ℂ) (w : ℂ)) :
    Isometry fun z : PoincareDisc => Complex.UnitDisc.toPoincare (g (toUnitDisc z)) :=
  Isometry.of_dist_eq fun z w => by
    simp only [dist_eq, toUnitDisc_toPoincare]
    exact hg _ _

/-- The disc Moebius factor `z ↦ (z - a) / (1 - conj a * z)` is a Poincaré self-isometry. -/
theorem isometry_unitDiscMoebius (a : Complex.UnitDisc) :
    Isometry fun z : PoincareDisc =>
      Complex.UnitDisc.toPoincare (unitDiscMoebius a (toUnitDisc z)) :=
  isometry_of_hyperbolicDist_eq fun z w => by
    rw [coe_unitDiscMoebius, coe_unitDiscMoebius, hyperbolicDist_unitDiscMoebius]

/-- Every standard disc automorphism `z ↦ u * (z - a) / (1 - conj a * z)` is a Poincaré
self-isometry. -/
theorem isometry_unitDiscStandardAutomorphismEquiv (u : Circle) (a : Complex.UnitDisc) :
    Isometry fun z : PoincareDisc =>
      Complex.UnitDisc.toPoincare (unitDiscStandardAutomorphismEquiv u a (toUnitDisc z)) :=
  isometry_of_hyperbolicDist_eq fun z w =>
    hyperbolicDist_unitDiscStandardAutomorphismEquiv u a z w

end PoincareDisc

end TauCeti
