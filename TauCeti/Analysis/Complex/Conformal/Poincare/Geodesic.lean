/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Complex.Conformal.Poincare.IsometryEquiv

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
expression is `|a - b| / (1 - a * b)`, and the subtraction formula for `Real.artanh` — the
mirror image of the addition formula `TauCeti.artanh_add` proved for the triangle inequality —
turns that into `|artanh a - artanh b|`. Reparametrising the diameter by `a = Real.tanh t` makes
it a unit-speed line: `TauCeti.PoincareDisc.radialGeodesic u` is an isometric embedding of `ℝ`.

Every point of the disc lies on such a line through the origin, and the disc automorphisms act
transitively by isometries, so transporting a radial line gives a geodesic through any two
prescribed points.

## Main declarations

* `TauCeti.hyperbolicDist_mul_ofReal_of_norm_eq_one` — the hyperbolic distance along a Euclidean
  diameter, in terms of `Real.artanh` of the signed radii.
* `TauCeti.PoincareDisc.radialGeodesic` — the unit-speed geodesic line through the origin in
  direction `u : Circle`, namely `t ↦ u * Real.tanh t`, together with
  `TauCeti.PoincareDisc.isometry_radialGeodesic` saying it is an isometric embedding of `ℝ`.
* `TauCeti.PoincareDisc.exists_radialGeodesic_eq` — every point of the disc is reached by the
  radial geodesic in its own direction, at time its distance to the origin.
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

open Complex Metric Set

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
    Real.artanh_eq_half_log (Ioo_subset_Icc_self hx),
    show (1 + -x) / (1 - -x) = ((1 + x) / (1 - x))⁻¹ by rw [inv_div]; ring_nf, Real.log_inv]
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
  rw [show (a - b) / (1 - a * b) = (a + -b) / (1 + a * -b) by ring_nf, ← h]
  ring

/-! ### The hyperbolic distance along a Euclidean diameter -/

/-- The pseudo-hyperbolic expression of two points `u * a`, `u * b` of the same Euclidean
diameter of the disc (`‖u‖ = 1`, `a` and `b` real) is `|a - b| / (1 - a * b)`: the rotation by
`u` is invisible (`TauCeti.pseudoHyperbolicExpr_const_mul`), and on the real axis the Moebius
denominator is the real number `1 - a * b`. -/
theorem pseudoHyperbolicExpr_mul_ofReal_of_norm_eq_one {u : ℂ} (hu : ‖u‖ = 1) {a b : ℝ}
    (ha : |a| < 1) (hb : |b| < 1) :
    pseudoHyperbolicExpr (u * a) (u * b) = |a - b| / (1 - a * b) := by
  have ha' := abs_lt.1 ha
  have hb' := abs_lt.1 hb
  have hab : (0 : ℝ) < 1 - a * b := by nlinarith [ha'.1, ha'.2, hb'.1, hb'.2]
  rw [pseudoHyperbolicExpr_const_mul hu, pseudoHyperbolicExpr_def, Complex.conj_ofReal,
    show ((a : ℂ) - (b : ℂ)) / (1 - (b : ℂ) * (a : ℂ)) = (((a - b) / (1 - a * b) : ℝ) : ℂ) by
      push_cast; ring,
    Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hab]

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
  rw [hyperbolicDist_def, pseudoHyperbolicExpr_mul_ofReal_of_norm_eq_one hu ha hb,
    show |a - b| / (1 - a * b) = |(a - b) / (1 - a * b)| by rw [abs_div, abs_of_pos hab],
    artanh_abs hquot, ← artanh_sub ⟨ha'.1, ha'.2⟩ ⟨hb'.1, hb'.2⟩]

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
  · refine ⟨⟨(toUnitDisc z : ℂ) / (‖(toUnitDisc z : ℂ)‖ : ℂ), mem_sphere_zero_iff_norm.2 ?_⟩, ?_⟩
    · rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
        div_self (norm_ne_zero_iff.2 hc0)]
    · refine toUnitDisc.injective <| Complex.UnitDisc.coe_injective ?_
      rw [coe_radialGeodesic, htanh]
      have hne : (‖(toUnitDisc z : ℂ)‖ : ℂ) ≠ 0 := by
        simpa using norm_ne_zero_iff.2 hc0
      field_simp

/-! ### The Poincaré disc is a geodesic space -/

/-- **The Poincaré disc is a geodesic metric space.** Through any two of its points there is a
unit-speed geodesic line `γ : ℝ → PoincareDisc` — an isometric embedding of the whole real line
— that starts at `z` at time `0` and passes through `w` at time `dist z w`.

The line is obtained by transporting a geodesic through the origin (`exists_radialGeodesic_eq`)
by the disc automorphism that moves `z` to the origin, which is a hyperbolic isometry. -/
theorem exists_isometry_apply_zero_apply_dist (z w : PoincareDisc) :
    ∃ γ : ℝ → PoincareDisc, Isometry γ ∧ γ 0 = z ∧ γ (dist z w) = w := by
  set g := unitDiscMoebiusIsometryEquiv (toUnitDisc z) with hg
  have hgz : g z = Complex.UnitDisc.toPoincare 0 := by
    rw [hg, unitDiscMoebiusIsometryEquiv_apply, unitDiscMoebius_self]
  obtain ⟨u, hu⟩ := exists_radialGeodesic_eq (g w)
  have hdist : dist (g w) (Complex.UnitDisc.toPoincare 0) = dist z w := by
    rw [← hgz, g.dist_eq, dist_comm]
  refine ⟨g.symm ∘ radialGeodesic u,
    g.symm.isometry.comp (isometry_radialGeodesic u), ?_, ?_⟩
  · rw [Function.comp_apply, radialGeodesic_zero, ← hgz, g.symm_apply_apply]
  · rw [Function.comp_apply, ← hdist, hu, g.symm_apply_apply]

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
  have habs0 : |(0 : ℝ)| < 1 := by norm_num
  have habsr : |r| < 1 := by rwa [abs_of_pos hr0]
  have htr : |t * r| < 1 := by
    rw [abs_of_nonneg (mul_nonneg ht.1 hr0.le)]
    nlinarith [ht.1, ht.2, hr0]
  have hle : Real.artanh (t * r) ≤ Real.artanh r := by
    refine Real.artanh_le_artanh (by linarith [abs_lt.1 htr]) (by linarith) ?_
    nlinarith [ht.2, hr0]
  have h0 : hyperbolicDist 0 ((t : ℂ) * z) = Real.artanh (t * r) := by
    rw [show (t : ℂ) * z = u * ((t * r : ℝ) : ℂ) by rw [hzu]; push_cast; ring,
      show (0 : ℂ) = u * ((0 : ℝ) : ℂ) by simp,
      hyperbolicDist_mul_ofReal_of_norm_eq_one hu habs0 htr, Real.artanh_zero, zero_sub, abs_neg,
      abs_of_nonneg (Real.artanh_nonneg (mul_nonneg ht.1 hr0.le))]
  have h1 : hyperbolicDist ((t : ℂ) * z) z = Real.artanh r - Real.artanh (t * r) := by
    rw [show (t : ℂ) * z = u * ((t * r : ℝ) : ℂ) by rw [hzu]; push_cast; ring,
      show z = u * ((r : ℝ) : ℂ) from hzu,
      hyperbolicDist_mul_ofReal_of_norm_eq_one hu htr habsr,
      abs_of_nonpos (sub_nonpos.2 hle), neg_sub]
  have h2 : hyperbolicDist 0 z = Real.artanh r := by
    rw [show z = u * ((r : ℝ) : ℂ) from hzu, show (0 : ℂ) = u * ((0 : ℝ) : ℂ) by simp,
      hyperbolicDist_mul_ofReal_of_norm_eq_one hu habs0 habsr, Real.artanh_zero, zero_sub,
      abs_neg, abs_of_nonneg (Real.artanh_nonneg hr0.le)]
  rw [h0, h1, h2]
  ring

end TauCeti
