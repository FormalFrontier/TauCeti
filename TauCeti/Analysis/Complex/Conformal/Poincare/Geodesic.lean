/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Complex.Conformal.Poincare.Isometry.Equiv

/-!
# The Poincaré disc is a geodesic metric space

`Poincare/MetricSpace.lean` makes the complex open unit disc a metric space `TauCeti.PoincareDisc`
for the hyperbolic distance `TauCeti.hyperbolicDist`, and `Poincare/Topology.lean` shows the
resulting metric is proper. This file adds the remaining basic geometric fact about that metric:
it is **geodesic**, the Euclidean diameters being unit-speed geodesic lines through the origin.
(The converse classification — that *every* geodesic through the origin is a Euclidean diameter —
is a uniqueness statement, and is not proved here.)

The computation behind everything is that along a fixed Euclidean diameter `{u * a | a : ℝ}` of
the disc, with `‖u‖ = 1`, the hyperbolic distance is the difference of the inverse hyperbolic
tangents of the signed radii:
`hyperbolicDist (u * a) (u * b) = |artanh a - artanh b|`
(`TauCeti.hyperbolicDist_mul_ofReal_of_norm_eq_one`). Indeed the Moebius denominator
`1 - conj (u * b) * (u * a)` collapses to the real number `1 - a * b`, so the pseudo-hyperbolic
expression is `|a - b| / |1 - a * b|`, and the subtraction formula for `Real.artanh` — the
mirror image of the addition formula `TauCeti.artanh_add` proved for the triangle inequality —
turns that into `|artanh a - artanh b|`. Reparametrising the diameter by `a = Real.tanh t` makes
it a unit-speed line: `TauCeti.PoincareDisc.radialGeodesic u` is an isometric embedding of `ℝ`.

Every point of the disc lies on such a line through the origin, and the disc automorphisms act
transitively by isometries, so transporting a radial line names the geodesic line through an
*arbitrary* point: carrying the radial geodesic in direction `u` back by
`(unitDiscMoebiusIsometryEquiv (toUnitDisc a)).symm` — the inverse of the Moebius isometry that
sends `a` to the origin — gives `TauCeti.PoincareDisc.geodesicLine a u`, which starts at `a` and
repeats the radial API (`geodesicLine_zero`, `isometry_geodesicLine`, `dist_geodesicLine_self`,
`geodesicLine_injective`) at that base point. No hyperbolic computation is redone: each of those
statements is its radial counterpart read through an isometry.

Those lines are what makes the disc a geodesic space: through any two prescribed points there
passes one of them.

## Main declarations

* `TauCeti.hyperbolicDist_mul_ofReal_of_norm_eq_one` — the hyperbolic distance along a Euclidean
  diameter, in terms of `Real.artanh` of the signed radii.
* `TauCeti.PoincareDisc.radialGeodesic` — the unit-speed geodesic line through the origin in
  direction `u : Circle`, namely `t ↦ u * Real.tanh t`, together with
  `TauCeti.PoincareDisc.isometry_radialGeodesic` saying it is an isometric embedding of `ℝ`.
* `TauCeti.PoincareDisc.exists_radialGeodesic_eq` — every point of the disc is reached by the
  radial geodesic in its own direction, at time its distance to the origin.
* `TauCeti.PoincareDisc.geodesicLine` — the same line based at an arbitrary point `a` instead of
  the origin, with `TauCeti.PoincareDisc.isometry_geodesicLine`,
  `TauCeti.PoincareDisc.geodesicLine_zero` and `TauCeti.PoincareDisc.geodesicLine_injective`.
* `TauCeti.PoincareDisc.exists_isometry_apply_zero_apply_dist` — **the Poincaré disc is a
  geodesic space**: through any two points there is a unit-speed geodesic line `γ : ℝ → 𝔻`, with
  `γ 0` the first point and `γ (dist z w)` the second.
* `TauCeti.PoincareDisc.exists_dist_eq_of_mem_Icc`,
  `TauCeti.PoincareDisc.exists_dist_eq_half_dist` — the consequences usually packaged as Menger
  convexity: every intermediate distance, and in particular a midpoint, is realised.
* `TauCeti.hyperbolicDist_zero_add_hyperbolicDist_ofReal_mul` — the Euclidean radius from the
  origin to a disc point is a hyperbolic geodesic segment: the hyperbolic distance adds along it.

This advances the conformal-mapping roadmap's L2 target "the hyperbolic / Poincaré metric on `𝔻`"
(see `ConformalMapping/README.md`), which the preceding files carried as far as the metric-space
instance and its topology; being geodesic is a further basic property of that metric, the one
that makes hyperbolic lines and segments available in this model. (It is not by itself a
characterisation of the hyperbolic plane: many unrelated metric spaces are geodesic.) It reuses
Tau Ceti's pseudo-hyperbolic, hyperbolic-distance and disc-automorphism API. As with the rest of
the L0--L3 conformal-mapping material, it is coordinated with the upstream Mathlib
Riemann-mapping effort leanprover-community/mathlib4#33505, whose preceding human-curated work in
`Analysis/Complex/RiemannMapping.lean` and `Analysis/Complex/BranchLogRoot.lean` this file
duplicates nothing of; should a human-curated Poincaré-disc metric land upstream, this material
should be refactored onto it. Mathlib has the hyperbolic metric on the upper half-plane
(`Analysis/Complex/UpperHalfPlane`), but no Poincaré metric on the disc and no geodesics for it.
-/

public section

namespace TauCeti

open _root_.Complex Metric Set

/-! ### Inverse hyperbolic tangent helpers -/

/-- `Real.artanh` is odd on `(-1, 1)`.

Mathlib's `Analysis/SpecialFunctions/Artanh.lean` records the monotonicity, sign and inversion
properties of `Real.artanh` but not this one (the name `Real.artanh_neg` is taken there by the
sign lemma). This is a local proof helper for the geodesic computation, kept private so that a
general real-analysis fact is not exported from a file about the Poincaré disc. -/
private lemma artanh_neg_eq {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    Real.artanh (-x) = -Real.artanh x := by
  have h1 : (0 : ℝ) < 1 + x := by linarith [hx.1]
  have h2 : (0 : ℝ) < 1 - x := by linarith [hx.2]
  rw [Real.artanh_eq_half_log ⟨by linarith [hx.2], by linarith [hx.1]⟩,
    Real.artanh_eq_half_log (Ioo_subset_Icc_self hx), ← sub_eq_add_neg, sub_neg_eq_add,
    ← inv_div (1 + x) (1 - x), Real.log_inv]
  ring

/-- The absolute value passes through `Real.artanh` on `(-1, 1)`. -/
private lemma artanh_abs {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    Real.artanh |x| = |Real.artanh x| := by
  rcases le_or_gt 0 x with hx0 | hx0
  · rw [abs_of_nonneg hx0, abs_of_nonneg (Real.artanh_nonneg hx0)]
  · rw [abs_of_neg hx0, artanh_neg_eq hx, abs_of_nonpos (Real.artanh_nonpos hx0.le)]

/-- **Subtraction formula for the inverse hyperbolic tangent.** For `a, b ∈ (-1, 1)`,
`artanh a - artanh b = artanh ((a - b) / (1 - a * b))`. This is the addition formula
`TauCeti.artanh_add`, which underlies the hyperbolic triangle inequality, with `b` negated. -/
private lemma artanh_sub {a b : ℝ} (ha : a ∈ Ioo (-1 : ℝ) 1) (hb : b ∈ Ioo (-1 : ℝ) 1) :
    Real.artanh a - Real.artanh b = Real.artanh ((a - b) / (1 - a * b)) := by
  have hb' : -b ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hb.2], by linarith [hb.1]⟩
  have h := artanh_add ha hb'
  rw [artanh_neg_eq hb] at h
  rw [sub_eq_add_neg a b, sub_eq_add_neg 1 (a * b), ← mul_neg, ← h]
  ring

/-! ### The hyperbolic distance along a Euclidean diameter -/

/-- The pseudo-hyperbolic expression of two points `u * a`, `u * b` of the same real line
through the origin (`‖u‖ = 1`, `a` and `b` real) is `|a - b| / |1 - a * b|`: the rotation by
`u` is invisible (`TauCeti.pseudoHyperbolicExpr_const_mul`), and on the real axis the Moebius
denominator is the real number `1 - a * b`.

Like `TauCeti.pseudoHyperbolicExpr` itself this is a total algebraic identity, needing no
disc-membership hypothesis on `a` and `b`. For points of the disc the denominator is positive,
so `|1 - a * b|` may be read as `1 - a * b`. -/
theorem pseudoHyperbolicExpr_mul_ofReal_of_norm_eq_one {u : ℂ} (hu : ‖u‖ = 1) (a b : ℝ) :
    pseudoHyperbolicExpr (u * a) (u * b) = |a - b| / |1 - a * b| := by
  have hcast : ((a : ℂ) - (b : ℂ)) / (1 - (b : ℂ) * (a : ℂ)) =
      (((a - b) / (1 - a * b) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [pseudoHyperbolicExpr_const_mul hu, pseudoHyperbolicExpr_def, Complex.conj_ofReal, hcast,
    Complex.norm_real, Real.norm_eq_abs, abs_div]

/-- **The hyperbolic distance along a Euclidean diameter.** For `‖u‖ = 1` and real `a, b` of
absolute value less than one, the hyperbolic distance between the disc points `u * a` and
`u * b` is `|artanh a - artanh b|`: the map `a ↦ u * a` sends `Real.artanh`-arclength on
`(-1, 1)` to hyperbolic distance. -/
theorem hyperbolicDist_mul_ofReal_of_norm_eq_one {u : ℂ} (hu : ‖u‖ = 1) {a b : ℝ}
    (ha : |a| < 1) (hb : |b| < 1) :
    hyperbolicDist (u * a) (u * b) = |Real.artanh a - Real.artanh b| := by
  have ha' := abs_lt.1 ha
  have hb' := abs_lt.1 hb
  have hab : (0 : ℝ) < 1 - a * b := by nlinarith [ha'.1, ha'.2, hb'.1, hb'.2]
  have hquot : (a - b) / (1 - a * b) ∈ Ioo (-1 : ℝ) 1 := by
    refine mem_Ioo.2 (abs_lt.1 ?_)
    rw [abs_div, abs_of_pos hab, div_lt_one hab, abs_lt]
    have h₁ : (0 : ℝ) < (1 + a) * (1 - b) :=
      mul_pos (by linarith [ha'.1]) (by linarith [hb'.2])
    have h₂ : (0 : ℝ) < (1 - a) * (1 + b) :=
      mul_pos (by linarith [ha'.2]) (by linarith [hb'.1])
    constructor <;> nlinarith [h₁, h₂]
  rw [hyperbolicDist_def, pseudoHyperbolicExpr_mul_ofReal_of_norm_eq_one hu a b,
    ← abs_div, artanh_abs hquot, ← artanh_sub ⟨ha'.1, ha'.2⟩ ⟨hb'.1, hb'.2⟩]

/-- Reparametrising a Euclidean diameter by `Real.tanh` makes it unit speed: the hyperbolic
distance between `u * Real.tanh s` and `u * Real.tanh t` is `|s - t|`. -/
theorem hyperbolicDist_mul_tanh_of_norm_eq_one {u : ℂ} (hu : ‖u‖ = 1) (s t : ℝ) :
    hyperbolicDist (u * Real.tanh s) (u * Real.tanh t) = |s - t| := by
  have habs : ∀ r : ℝ, |Real.tanh r| < 1 := fun r =>
    abs_lt.2 ⟨Real.neg_one_lt_tanh r, Real.tanh_lt_one r⟩
  rw [hyperbolicDist_mul_ofReal_of_norm_eq_one hu (habs s) (habs t), Real.artanh_tanh,
    Real.artanh_tanh]

namespace PoincareDisc

/-! ### Geodesic lines through the origin -/

/-- The unit-speed geodesic line of the Poincaré disc through the origin in the direction
`u : Circle`, that is, the Euclidean diameter in direction `u` parametrised by hyperbolic
arclength: `radialGeodesic u t` is the disc point `u * Real.tanh t`. -/
noncomputable def radialGeodesic (u : Circle) (t : ℝ) : PoincareDisc :=
  Complex.UnitDisc.toPoincare (u • Complex.UnitDisc.mk (Real.tanh t) (by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact abs_lt.2 ⟨Real.neg_one_lt_tanh t, Real.tanh_lt_one t⟩))

/-- The point `radialGeodesic u t` of the Poincaré disc is the complex number
`u * Real.tanh t`. -/
@[simp]
lemma coe_radialGeodesic (u : Circle) (t : ℝ) :
    ((toUnitDisc (radialGeodesic u t) : Complex.UnitDisc) : ℂ) = (u : ℂ) * Real.tanh t := by
  simp only [radialGeodesic, toUnitDisc_toPoincare, Complex.UnitDisc.coe_circle_smul,
    Complex.UnitDisc.coe_mk]

/-- Every radial geodesic starts at the origin. -/
@[simp]
lemma radialGeodesic_zero (u : Circle) :
    radialGeodesic u 0 = Complex.UnitDisc.toPoincare 0 :=
  toUnitDisc.injective <| Complex.UnitDisc.coe_injective <| by simp

/-- **The radial geodesics are unit-speed geodesic lines**: `t ↦ u * Real.tanh t` is an
isometric embedding of the real line into the Poincaré disc. -/
theorem isometry_radialGeodesic (u : Circle) : Isometry (radialGeodesic u) :=
  Isometry.of_dist_eq fun s t => by
    rw [dist_eq, coe_radialGeodesic, coe_radialGeodesic,
      hyperbolicDist_mul_tanh_of_norm_eq_one (Circle.norm_coe u), Real.dist_eq]

/-- The radial geodesic in direction `u` is at hyperbolic distance `|t|` from the origin at
time `t`.

Not a `simp` lemma: `dist_eq` and `coe_radialGeodesic` already rewrite its left-hand side to a
`hyperbolicDist` of complex numbers. -/
lemma dist_radialGeodesic_zero (u : Circle) (t : ℝ) :
    dist (radialGeodesic u t) (Complex.UnitDisc.toPoincare 0) = |t| := by
  rw [← radialGeodesic_zero u, (isometry_radialGeodesic u).dist_eq, Real.dist_eq, sub_zero]

/-- Distinct directions give distinct radial geodesics. -/
theorem radialGeodesic_injective : Function.Injective radialGeodesic := by
  intro u v huv
  -- Evaluate at time `1`, where the two geodesics read `u * Real.tanh 1` and `v * Real.tanh 1`.
  have htanh : (Real.tanh 1 : ℂ) ≠ 0 := by
    refine Complex.ofReal_ne_zero.mpr fun hzero => one_ne_zero (α := ℝ) ?_
    exact Real.tanh_injective (hzero.trans Real.tanh_zero.symm)
  refine Circle.ext (mul_right_cancel₀ htanh ?_)
  have hcoe := congrArg (fun p : PoincareDisc => (toUnitDisc p : ℂ)) (congrFun huv 1)
  simpa only [coe_radialGeodesic] using hcoe

/-- **Every point of the Poincaré disc lies on a geodesic through the origin**, namely the
Euclidean diameter through it, and it is reached at time its distance to the origin. -/
theorem exists_radialGeodesic_eq (z : PoincareDisc) :
    ∃ u : Circle, radialGeodesic u (dist z (Complex.UnitDisc.toPoincare 0)) = z := by
  have hcnorm : ‖(toUnitDisc z : ℂ)‖ < 1 := (toUnitDisc z).norm_lt_one
  have hdist : dist z (Complex.UnitDisc.toPoincare 0) = Real.artanh ‖(toUnitDisc z : ℂ)‖ :=
    dist_toPoincare_zero_right z
  have htanh : Real.tanh (dist z (Complex.UnitDisc.toPoincare 0)) = ‖(toUnitDisc z : ℂ)‖ := by
    rw [hdist]
    exact Real.tanh_artanh ⟨by linarith [norm_nonneg (toUnitDisc z : ℂ)], hcnorm⟩
  rcases eq_or_ne (toUnitDisc z : ℂ) 0 with hc0 | hc0
  · refine ⟨1, ?_⟩
    have hz : z = Complex.UnitDisc.toPoincare 0 :=
      toUnitDisc.injective <| Complex.UnitDisc.coe_injective <| by
        rw [toUnitDisc_toPoincare, Complex.UnitDisc.coe_zero]; exact hc0
    have hzero : dist z (Complex.UnitDisc.toPoincare 0) = 0 := by rw [hz, dist_self]
    rw [hzero, radialGeodesic_zero, hz]
  · have hne : (‖(toUnitDisc z : ℂ)‖ : ℂ) ≠ 0 := by
      simpa using norm_ne_zero_iff.2 hc0
    have hnorm : ‖(toUnitDisc z : ℂ) / (‖(toUnitDisc z : ℂ)‖ : ℂ)‖ = 1 := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
        div_self (norm_ne_zero_iff.2 hc0)]
    -- Name the direction of `z` as an element of `Circle`, rather than leaving the anonymous
    -- constructor in the goal, where its `Metric.sphere`/`Submonoid.unitSphere` membership proof
    -- would block rewriting under `radialGeodesic`.
    obtain ⟨u, hu⟩ : ∃ u : Circle, (u : ℂ) = (toUnitDisc z : ℂ) / (‖(toUnitDisc z : ℂ)‖ : ℂ) :=
      ⟨⟨_, mem_sphere_zero_iff_norm.2 hnorm⟩, rfl⟩
    refine ⟨u, toUnitDisc.injective <| Complex.UnitDisc.coe_injective ?_⟩
    rw [coe_radialGeodesic, htanh, hu]
    field_simp

/-! ### Geodesic lines through an arbitrary point -/

/-- The unit-speed geodesic line of the Poincaré disc through `a` in the direction `u : Circle`:
the radial geodesic `TauCeti.PoincareDisc.radialGeodesic u` carried back to `a` by
`(unitDiscMoebiusIsometryEquiv (toUnitDisc a)).symm`, the *inverse* of the Moebius isometry that
sends `a` to the origin. Based at the origin it is `radialGeodesic u` itself
(`TauCeti.PoincareDisc.geodesicLine_toPoincare_zero`). -/
noncomputable def geodesicLine (a : PoincareDisc) (u : Circle) (t : ℝ) : PoincareDisc :=
  (unitDiscMoebiusIsometryEquiv (toUnitDisc a)).symm (radialGeodesic u t)

/-- The defining formula for `TauCeti.PoincareDisc.geodesicLine`; its body is not `@[expose]`d, so
this is how the definition is unfolded downstream. -/
lemma geodesicLine_def (a : PoincareDisc) (u : Circle) (t : ℝ) :
    geodesicLine a u t =
      (unitDiscMoebiusIsometryEquiv (toUnitDisc a)).symm (radialGeodesic u t) := by
  rw [geodesicLine]

/-- The Moebius isometry that sends `a` to the origin straightens the geodesic line through `a`
into the radial geodesic in the same direction. This is `TauCeti.PoincareDisc.geodesicLine_def`
read forwards, and it is how a statement about `geodesicLine` is transported to the origin.

Not a `simp` lemma: `unitDiscMoebiusIsometryEquiv_apply` is itself `simp`, so the left-hand side
here is not in simp-normal form — it rewrites to
`Complex.UnitDisc.toPoincare (unitDiscMoebius (toUnitDisc a) (toUnitDisc (geodesicLine a u t)))`,
which the `simpNF` linter rejects. -/
lemma unitDiscMoebiusIsometryEquiv_geodesicLine (a : PoincareDisc) (u : Circle) (t : ℝ) :
    unitDiscMoebiusIsometryEquiv (toUnitDisc a) (geodesicLine a u t) = radialGeodesic u t := by
  rw [geodesicLine_def, IsometryEquiv.apply_symm_apply]

/-- Every geodesic line through `a` starts at `a`: the generalisation of
`TauCeti.PoincareDisc.radialGeodesic_zero` off the origin. -/
@[simp]
lemma geodesicLine_zero (a : PoincareDisc) (u : Circle) : geodesicLine a u 0 = a := by
  have ha : unitDiscMoebiusIsometryEquiv (toUnitDisc a) a = Complex.UnitDisc.toPoincare 0 := by
    rw [unitDiscMoebiusIsometryEquiv_apply, unitDiscMoebius_self]
  rw [geodesicLine_def, radialGeodesic_zero, ← ha, IsometryEquiv.symm_apply_apply]

/-- Based at the origin, the geodesic lines are exactly the radial ones: the Moebius isometry
centred at the origin is the identity. -/
@[simp]
lemma geodesicLine_toPoincare_zero (u : Circle) :
    geodesicLine (Complex.UnitDisc.toPoincare 0) u = radialGeodesic u := by
  funext t
  rw [geodesicLine_def, toUnitDisc_toPoincare, IsometryEquiv.symm_apply_eq]
  simp

/-- **The geodesic lines are unit-speed geodesic lines**: `geodesicLine a u` is an isometric
embedding of the real line into the Poincaré disc, being `TauCeti.PoincareDisc.radialGeodesic u`
composed with an isometry. -/
theorem isometry_geodesicLine (a : PoincareDisc) (u : Circle) : Isometry (geodesicLine a u) := by
  have h : geodesicLine a u =
      (unitDiscMoebiusIsometryEquiv (toUnitDisc a)).symm ∘ radialGeodesic u :=
    funext (geodesicLine_def a u)
  rw [h]
  exact (unitDiscMoebiusIsometryEquiv (toUnitDisc a)).symm.isometry.comp
    (isometry_radialGeodesic u)

/-- The geodesic line through `a` is at hyperbolic distance `|t|` from `a` at time `t`: the
generalisation of `TauCeti.PoincareDisc.dist_radialGeodesic_zero` off the origin. -/
lemma dist_geodesicLine_self (a : PoincareDisc) (u : Circle) (t : ℝ) :
    dist (geodesicLine a u t) a = |t| := by
  have h := (isometry_geodesicLine a u).dist_eq t 0
  rwa [geodesicLine_zero, Real.dist_eq, sub_zero] at h

/-- Distinct directions give distinct geodesic lines through a common point: the generalisation of
`TauCeti.PoincareDisc.radialGeodesic_injective` off the origin. -/
theorem geodesicLine_injective (a : PoincareDisc) : Function.Injective (geodesicLine a) := by
  intro u v huv
  refine radialGeodesic_injective (funext fun t => ?_)
  have h := congrArg (unitDiscMoebiusIsometryEquiv (toUnitDisc a)) (congrFun huv t)
  rwa [unitDiscMoebiusIsometryEquiv_geodesicLine,
    unitDiscMoebiusIsometryEquiv_geodesicLine] at h

/-! ### The Poincaré disc is a geodesic space -/

/-- **The Poincaré disc is a geodesic metric space.** Through any two of its points there is a
unit-speed geodesic line `γ : ℝ → PoincareDisc` — an isometric embedding of the whole real line
— that starts at `z` at time `0` and passes through `w` at time `dist z w`.

The line is `TauCeti.PoincareDisc.geodesicLine z u`, for `u` the direction in which the Moebius
isometry sending `z` to the origin sees `w` (`TauCeti.PoincareDisc.exists_radialGeodesic_eq`). -/
theorem exists_isometry_apply_zero_apply_dist (z w : PoincareDisc) :
    ∃ γ : ℝ → PoincareDisc, Isometry γ ∧ γ 0 = z ∧ γ (dist z w) = w := by
  obtain ⟨u, hu⟩ := exists_radialGeodesic_eq (unitDiscMoebiusIsometryEquiv (toUnitDisc z) w)
  refine ⟨geodesicLine z u, isometry_geodesicLine z u, geodesicLine_zero z u, ?_⟩
  have hgz : unitDiscMoebiusIsometryEquiv (toUnitDisc z) z = Complex.UnitDisc.toPoincare 0 := by
    rw [unitDiscMoebiusIsometryEquiv_apply, unitDiscMoebius_self]
  have hdist : dist (unitDiscMoebiusIsometryEquiv (toUnitDisc z) w)
      (Complex.UnitDisc.toPoincare 0) = dist z w := by
    rw [← hgz, (unitDiscMoebiusIsometryEquiv (toUnitDisc z)).dist_eq, dist_comm]
  rw [geodesicLine_def, ← hdist, hu, IsometryEquiv.symm_apply_apply]

/-- Every intermediate distance along a geodesic is realised: for `0 ≤ r ≤ dist z w` there is a
point at hyperbolic distance `r` from `z` and `dist z w - r` from `w`. -/
theorem exists_dist_eq_of_mem_Icc (z w : PoincareDisc) {r : ℝ} (hr : r ∈ Icc 0 (dist z w)) :
    ∃ m : PoincareDisc, dist z m = r ∧ dist m w = dist z w - r := by
  obtain ⟨γ, hγ, h0, hd⟩ := exists_isometry_apply_zero_apply_dist z w
  refine ⟨γ r, ?_, ?_⟩
  · have hzr : dist z (γ r) = dist (0 : ℝ) r := by rw [← h0, hγ.dist_eq]
    rw [hzr, Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg hr.1]
  · have hrw : dist (γ r) w = dist r (dist z w) := by
      conv_lhs => rw [← hd]
      rw [hγ.dist_eq]
    rw [hrw, Real.dist_eq, abs_of_nonpos (sub_nonpos.2 hr.2), neg_sub]

/-- **Midpoints exist in the Poincaré disc**: any two points have a point halfway between them
for the hyperbolic distance. -/
theorem exists_dist_eq_half_dist (z w : PoincareDisc) :
    ∃ m : PoincareDisc, dist z m = dist z w / 2 ∧ dist m w = dist z w / 2 := by
  obtain ⟨m, hm₁, hm₂⟩ :=
    exists_dist_eq_of_mem_Icc z w (r := dist z w / 2)
      ⟨by linarith [dist_nonneg (x := z) (y := w)],
        by linarith [dist_nonneg (x := z) (y := w)]⟩
  exact ⟨m, hm₁, by rw [hm₂]; ring⟩

end PoincareDisc

/-- **The Euclidean radius is a hyperbolic geodesic segment.** For `z` in the open unit disc and
`t ∈ [0, 1]`, the point `t * z` of the Euclidean segment from the origin to `z` splits the
hyperbolic distance additively. Together with `TauCeti.PoincareDisc.exists_radialGeodesic_eq`
this exhibits each Euclidean diameter as a hyperbolic geodesic through the origin, and every
point of the disc as lying on one of them. -/
theorem hyperbolicDist_zero_add_hyperbolicDist_ofReal_mul {z : ℂ} (hz : ‖z‖ < 1) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    hyperbolicDist 0 ((t : ℂ) * z) + hyperbolicDist ((t : ℂ) * z) z = hyperbolicDist 0 z := by
  rcases eq_or_ne z 0 with hz0 | hz0
  · simp [hz0]
  set r : ℝ := ‖z‖ with hr
  have hr0 : 0 < r := norm_pos_iff.2 hz0
  set u : ℂ := z / (r : ℂ) with hu_def
  have hrne : (r : ℂ) ≠ 0 := by simpa using hr0.ne'
  have hu : ‖u‖ = 1 := by
    rw [hu_def, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0, ← hr,
      div_self hr0.ne']
  have hzu : z = u * (r : ℂ) := by
    rw [hu_def, div_mul_cancel₀ _ hrne]
  have habsr : |r| < 1 := by rwa [abs_of_pos hr0]
  have htr : |t * r| < 1 := by
    rw [abs_of_nonneg (mul_nonneg ht.1 hr0.le)]
    nlinarith [ht.1, ht.2, hr0]
  have hle : Real.artanh (t * r) ≤ Real.artanh r := by
    refine Real.artanh_le_artanh (by linarith [abs_lt.1 htr]) (by linarith) ?_
    nlinarith [ht.2, hr0]
  -- Both distances to the origin are given by the closed form `hyperbolicDist_zero_right`.
  have h0 : hyperbolicDist 0 ((t : ℂ) * z) = Real.artanh (t * r) := by
    rw [hyperbolicDist_comm, hyperbolicDist_zero_right, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg ht.1, ← hr]
  have h2 : hyperbolicDist 0 z = Real.artanh r := by
    rw [hyperbolicDist_comm, hyperbolicDist_zero_right, ← hr]
  -- The remaining distance is between two points of the diameter in direction `u`.
  have htz : (t : ℂ) * z = u * ((t * r : ℝ) : ℂ) := by
    rw [hzu]
    push_cast
    ring
  have h1 : hyperbolicDist ((t : ℂ) * z) z = Real.artanh r - Real.artanh (t * r) := by
    rw [htz, hzu, hyperbolicDist_mul_ofReal_of_norm_eq_one hu htr habsr,
      abs_of_nonpos (sub_nonpos.2 hle), neg_sub]
  rw [h0, h1, h2]
  ring

end TauCeti
