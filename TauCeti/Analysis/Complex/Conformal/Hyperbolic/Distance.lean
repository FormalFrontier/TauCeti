/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Complex.Conformal.SchwarzPick.Basic
public import TauCeti.Analysis.Complex.Conformal.SchwarzPick.Isometry
public import Mathlib.Analysis.SpecialFunctions.Artanh

/-!
# The hyperbolic (Poincaré) distance on the unit disc

This file defines the hyperbolic (Poincaré) distance on the complex open unit disc,
`hyperbolicDist z w = Real.artanh p` where `p = pseudoHyperbolicExpr z w` is the
pseudo-hyperbolic expression `‖(z - w) / (1 - conj w * z)‖`.  The inverse hyperbolic tangent
`Real.artanh t = (1 / 2) * log ((1 + t) / (1 - t))` is the standard order isomorphism
`[0, 1) ≃ [0, ∞)`, so the hyperbolic distance is a strictly monotone reparametrisation of the
pseudo-hyperbolic expression by which the two record the same geometry additively.

The normalisation matches the infinitesimal Poincaré metric `|dz| / (1 - |z| ^ 2)` already
formalized in this area (`SchwarzPickDerivative.lean`): the geodesic distance from the origin
to a point at radius `r` under that metric is `∫₀ʳ dt / (1 - t ^ 2) = artanh r`, which is
exactly `hyperbolicDist z 0` for `‖z‖ = r`.

The main API mirrors the pseudo-hyperbolic layer:

* `hyperbolicDist_comm`, `hyperbolicDist_self`, `hyperbolicDist_nonneg`,
  `hyperbolicDist_eq_zero_iff_of_mem_ball` — the basic pseudo-metric properties;
* `hyperbolicDist_zero_right` — the closed form `artanh ‖z‖` from the origin;
* `hyperbolicDist_map_le` — the **Schwarz--Pick theorem** in its classical
  distance-decreasing form: a holomorphic self-map of the disc does not increase the
  hyperbolic distance;
* `hyperbolicDist_unitDiscMoebius`, `hyperbolicDist_unitDiscStandardAutomorphismEquiv` — the
  hyperbolic distance is invariant under the disc Moebius factors and the standard
  automorphisms, i.e. these are hyperbolic isometries.

The full metric-space structure (the triangle inequality, hence a `MetricSpace` instance on
`Complex.UnitDisc`) is deferred; it rests on the strengthened pseudo-hyperbolic triangle
inequality and is future work of the L2 layer.

This advances the conformal-mapping roadmap's L2 target "the hyperbolic / Poincaré metric on
`𝔻`" (see `ConformalMapping/README.md`).  It reuses Tau Ceti's pseudo-hyperbolic and
Schwarz--Pick API.  As with the rest of the L0--L3 conformal-mapping material, it is
coordinated with the upstream Mathlib RMT effort leanprover-community/mathlib4#33505.  Mathlib
already contains the preceding human-curated work in `Analysis/Complex/RiemannMapping.lean` and
`Analysis/Complex/BranchLogRoot.lean`; none of it is duplicated here, and should that work land
a human-curated Poincaré metric this file should be refactored onto it.  Mathlib has the
hyperbolic metric on the upper half-plane (`Analysis/Complex/UpperHalfPlane`), but no
hyperbolic distance on the disc.
-/

public section

namespace TauCeti

open Complex Metric Set
open scoped ComplexConjugate

/-- The hyperbolic (Poincaré) distance on the complex unit disc, written as a total
real-valued function `Real.artanh p` of the pseudo-hyperbolic expression
`p = pseudoHyperbolicExpr z w`.

On the open unit disc this is the hyperbolic distance, normalised to agree with the
infinitesimal Poincaré metric `|dz| / (1 - |z| ^ 2)`.  Outside the disc, where `p` may reach
or exceed one, the formula remains a total Lean expression with no geometric meaning. -/
noncomputable def hyperbolicDist (z w : ℂ) : ℝ :=
  Real.artanh (pseudoHyperbolicExpr z w)

/-- The defining formula for the hyperbolic distance. -/
lemma hyperbolicDist_def (z w : ℂ) :
    hyperbolicDist z w = Real.artanh (pseudoHyperbolicExpr z w) := by
  rw [hyperbolicDist]

/-- The hyperbolic distance is symmetric. -/
lemma hyperbolicDist_comm (z w : ℂ) : hyperbolicDist z w = hyperbolicDist w z := by
  rw [hyperbolicDist_def, hyperbolicDist_def, pseudoHyperbolicExpr_comm]

/-- The hyperbolic distance from a point to itself is zero. -/
@[simp]
lemma hyperbolicDist_self (z : ℂ) : hyperbolicDist z z = 0 := by
  simp [hyperbolicDist_def]

/-- The hyperbolic distance from a point of the disc to the origin has the closed form
`artanh ‖z‖`. -/
lemma hyperbolicDist_zero_right (z : ℂ) :
    hyperbolicDist z 0 = Real.artanh ‖z‖ := by
  rw [hyperbolicDist_def, pseudoHyperbolicExpr_zero_right]

/-- The hyperbolic distance is nonnegative. -/
lemma hyperbolicDist_nonneg (z w : ℂ) : 0 ≤ hyperbolicDist z w := by
  rw [hyperbolicDist_def]
  exact Real.artanh_nonneg (pseudoHyperbolicExpr_nonneg z w)

/-- On the open unit disc the hyperbolic distance vanishes exactly on the diagonal. -/
lemma hyperbolicDist_eq_zero_iff_of_mem_ball {z w : ℂ}
    (hz : z ∈ ball (0 : ℂ) 1) (hw : w ∈ ball (0 : ℂ) 1) :
    hyperbolicDist z w = 0 ↔ z = w := by
  have hlt : pseudoHyperbolicExpr z w < 1 := pseudoHyperbolicExpr_lt_one_of_mem_ball hz hw
  have hge : 0 ≤ pseudoHyperbolicExpr z w := pseudoHyperbolicExpr_nonneg z w
  rw [hyperbolicDist_def, Real.artanh_eq_zero_iff,
    ← pseudoHyperbolicExpr_eq_zero_iff_of_mem_ball hz hw]
  constructor
  · rintro (h | h | h)
    · linarith
    · exact h
    · linarith
  · exact fun h => Or.inr (Or.inl h)

/-- On the open unit disc the hyperbolic distance and the pseudo-hyperbolic expression carry
the same information: `Real.artanh` is injective on `(-1, 1)`, and the pseudo-hyperbolic
expression of a pair of disc points lies in `[0, 1)`. -/
lemma pseudoHyperbolicExpr_eq_iff_hyperbolicDist_eq {z w z' w' : ℂ}
    (hz : z ∈ ball (0 : ℂ) 1) (hw : w ∈ ball (0 : ℂ) 1)
    (hz' : z' ∈ ball (0 : ℂ) 1) (hw' : w' ∈ ball (0 : ℂ) 1) :
    pseudoHyperbolicExpr z w = pseudoHyperbolicExpr z' w' ↔
      hyperbolicDist z w = hyperbolicDist z' w' := by
  have hmem : pseudoHyperbolicExpr z w ∈ Ioo (-1 : ℝ) 1 :=
    ⟨by linarith [pseudoHyperbolicExpr_nonneg z w], pseudoHyperbolicExpr_lt_one_of_mem_ball hz hw⟩
  have hmem' : pseudoHyperbolicExpr z' w' ∈ Ioo (-1 : ℝ) 1 :=
    ⟨by linarith [pseudoHyperbolicExpr_nonneg z' w'],
      pseudoHyperbolicExpr_lt_one_of_mem_ball hz' hw'⟩
  rw [hyperbolicDist_def, hyperbolicDist_def]
  exact ⟨fun h => by rw [h], fun h => Real.artanh_injOn hmem hmem' h⟩

/-- **Schwarz--Pick, distance form.** A holomorphic self-map of the complex unit disc does not
increase the hyperbolic distance. -/
theorem hyperbolicDist_map_le {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (hmaps : MapsTo f (ball (0 : ℂ) 1) (ball (0 : ℂ) 1))
    {z w : ℂ} (hz : z ∈ ball (0 : ℂ) 1) (hw : w ∈ ball (0 : ℂ) 1) :
    hyperbolicDist (f z) (f w) ≤ hyperbolicDist z w := by
  have hp : pseudoHyperbolicExpr (f z) (f w) ≤ pseudoHyperbolicExpr z w :=
    pseudoHyperbolicExpr_map_le hf hmaps hz hw
  have hq : pseudoHyperbolicExpr z w < 1 := pseudoHyperbolicExpr_lt_one_of_mem_ball hz hw
  have hge : 0 ≤ pseudoHyperbolicExpr (f z) (f w) := pseudoHyperbolicExpr_nonneg _ _
  rw [hyperbolicDist_def, hyperbolicDist_def]
  exact Real.artanh_le_artanh (by linarith) hq hp

/-- Bundled unit-disc form of Schwarz--Pick in distance form. -/
theorem hyperbolicDist_map_le_unitDisc {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (hmaps : MapsTo f (ball (0 : ℂ) 1) (ball (0 : ℂ) 1))
    (z w : Complex.UnitDisc) :
    hyperbolicDist (f z) (f w) ≤ hyperbolicDist (z : ℂ) (w : ℂ) :=
  hyperbolicDist_map_le hf hmaps z.property w.property

/-- The disc Moebius factor `z ↦ (z - a) / (1 - conj a * z)` is a hyperbolic isometry. -/
theorem hyperbolicDist_unitDiscMoebius (a z w : Complex.UnitDisc) :
    hyperbolicDist (((z : ℂ) - (a : ℂ)) / (1 - (starRingEnd ℂ) (a : ℂ) * (z : ℂ)))
        (((w : ℂ) - (a : ℂ)) / (1 - (starRingEnd ℂ) (a : ℂ) * (w : ℂ)))
      = hyperbolicDist (z : ℂ) (w : ℂ) := by
  rw [hyperbolicDist_def, hyperbolicDist_def, pseudoHyperbolicExpr_unitDiscMoebius]

/-- Every standard disc automorphism `z ↦ u * (z - a) / (1 - conj a * z)` is a hyperbolic
isometry. -/
theorem hyperbolicDist_unitDiscStandardAutomorphismEquiv
    (u : Circle) (a z w : Complex.UnitDisc) :
    hyperbolicDist (unitDiscStandardAutomorphismEquiv u a z : ℂ)
        (unitDiscStandardAutomorphismEquiv u a w : ℂ)
      = hyperbolicDist (z : ℂ) (w : ℂ) := by
  rw [hyperbolicDist_def, hyperbolicDist_def,
    pseudoHyperbolicExpr_unitDiscStandardAutomorphismEquiv]

end TauCeti
