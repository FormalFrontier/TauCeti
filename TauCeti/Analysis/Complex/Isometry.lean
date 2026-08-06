/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Isometry
import Mathlib.Analysis.InnerProductSpace.TwoDim

/-!
# Distance-preserving maps of a disc about the origin

Mathlib's `Mathlib/Analysis/Complex/Isometry.lean` classifies the **linear** isometries of the
plane: `linear_isometry_complex` says that every `f : ℂ ≃ₗᵢ[ℝ] ℂ` is `rotation a` or
`conjLIE.trans (rotation a)`. That statement asks for a map defined on all of `ℂ`, and asks it to
be both `ℝ`-linear and surjective. This file drops all three hypotheses at once: for a map `g`
defined on a disc `ball 0 r` about the origin, fixing the origin and merely preserving distances
between points of that disc, the *restriction of `g` to that disc* is the restriction of
`z ↦ u * z`, or of `z ↦ u * conj z`, for a single unit `u`. The alternative is not chosen point by
point — that single choice is the content of the theorem.

Linearity and surjectivity are dropped as hypotheses; they are not put back as conclusions.
Nothing is claimed about `g` off the disc, so `g` itself need be neither linear nor surjective, and
the theorem says only that on `ball 0 r` it agrees with a map that is.

The proof is the classical orthonormal-frame argument. `TauCeti/Analysis/InnerProductSpace/
Isometry.lean` turns the distance hypothesis into preservation of the real inner product that `ℂ`
carries (`Complex.inner : ⟪w, z⟫_ℝ = (z * conj w).re`). The two probe points `r / 2` and `I * r / 2`
of the disc then have images whose doublings-by-`2 / r` are an orthonormal pair `e`, `f`, and
`⟪e, g z⟫_ℝ`, `⟪f, g z⟫_ℝ` read off the real and imaginary parts of `z` — the second through
Mathlib's two-dimensional orientation API, whose area form `Complex.areaForm` is `(conj x * y).im`
and whose quarter turn `Complex.rightAngleRotation` is multiplication by `I`. Orthogonality of two
unit complex numbers means a quarter turn, `f = e * I` or `f = -(e * I)`
(`TauCeti.eq_mul_I_or_eq_neg_mul_I_of_real_inner_eq_zero`), and the two cases give
`conj e * g z = z` and `conj e * g z = conj z` respectively — the alternative being fixed once, by
`f`, and not per point.

That argument is adapted from the proof of
`TauCeti.exists_norm_eq_one_eqOn_ball_const_mul_or_const_mul_conj` and its `private` scaffolding
(`real_inner_eq`, `im_conj_mul`, `exists_orthonormal_pair_real_inner_map_eq`,
`eq_mul_I_or_eq_neg_mul_I`) in
`TauCeti/Analysis/Complex/Conformal/Poincare/Isometry/Classification.lean`, as merged in
TauCeti#1502; here the unit radius is relaxed to an arbitrary `r > 0` and the hyperbolic
hypothesis is replaced by the Euclidean one the argument actually used.

## Main results

* `TauCeti.real_inner_eq_zero_iff_exists_eq_real_mul_mul_I` — the orthogonal complement of a
  nonzero `z` in the Euclidean plane `ℂ` is the real line through the quarter turn `z * I`, and
  `TauCeti.eq_mul_I_or_eq_neg_mul_I_of_real_inner_eq_zero` — its unit-vector reading.
* `TauCeti.exists_norm_eq_one_eqOn_ball_const_mul_or_const_mul_conj_of_dist_map_eq` — **the
  classification**: a distance-preserving self-map of `ball 0 r` fixing `0` is a rotation or a
  rotated conjugation there, and
  `TauCeti.exists_norm_eq_one_eqOn_ball_const_mul_or_const_mul_conj_iff` — the converse packaged
  with it, the rotations and rotated conjugations being exactly the maps in question.

The consumer is `TauCeti/Analysis/Complex/Conformal/Poincare/Isometry/Classification.lean`, which
classifies the isometries of the Poincaré disc: an isometry of the hyperbolic metric fixing the
origin is a Euclidean isometry of the disc fixing the origin, so the hyperbolic classification is
this Euclidean one together with the Moebius factor that moves the base point. This supports the
hyperbolic-metric layer L2 of the conformal-mapping roadmap
(`TauCetiRoadmap/ConformalMapping/README.md`) without adding to it.
-/

public section

namespace TauCeti

open Metric Set
open scoped ComplexConjugate RealInnerProductSpace

open _root_.Complex (I)

-- Mathlib's two-dimensional orientation API is stated for a space of `finrank ℝ` equal to `2`,
-- and, as in `Mathlib/Analysis/InnerProductSpace/TwoDim.lean` itself, the witness for `ℂ` is a
-- local instance rather than a global one.
attribute [local instance] _root_.Complex.finrank_real_complex_fact

/-! ### The real inner product of `ℂ` in real coordinates

`ℂ` carries the real inner product `⟪w, z⟫_ℝ = (z * conj w).re` (`Complex.inner`); its two readings
in terms of `conj x * y` are Mathlib's as well, the real part being `Complex.inner` up to
`mul_comm` and the imaginary part being the area form `Complex.areaForm` of `Complex.orientation`
paired with the quarter turn `Complex.rightAngleRotation` through
`Orientation.inner_rightAngleRotation_left`. The one reading Mathlib does not carry is in the real
coordinates `Complex.re`, `Complex.im`, and the private lemma below expands `Complex.inner` into
them. -/

/-- The real inner product of `ℂ` in the real coordinates `Complex.re`, `Complex.im`. -/
private lemma real_inner_eq_re_mul_re_add_im_mul_im (x y : ℂ) :
    ⟪x, y⟫ = x.re * y.re + x.im * y.im := by
  simp only [_root_.Complex.inner, _root_.Complex.mul_re, _root_.Complex.conj_re,
    _root_.Complex.conj_im]
  ring

/-! ### Orthogonality in the Euclidean plane -/

/-- **The orthogonal complement of a line in the plane is the perpendicular line.** For `z ≠ 0`,
the complex numbers `w` with `⟪z, w⟫_ℝ = 0` are exactly the real multiples of the quarter turn
`z * I`.

The hypothesis `z ≠ 0` is needed only for `→`: at `z = 0` every `w` is orthogonal to `z` while the
right-hand side forces `w = 0`. -/
theorem real_inner_eq_zero_iff_exists_eq_real_mul_mul_I {z w : ℂ} (hz : z ≠ 0) :
    ⟪z, w⟫ = 0 ↔ ∃ t : ℝ, w = (t : ℂ) * (z * I) := by
  have hns : _root_.Complex.normSq z ≠ 0 := fun h => hz (_root_.Complex.normSq_eq_zero.mp h)
  have hnsC : ((_root_.Complex.normSq z : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hns
  have hzc : conj z * z = ((_root_.Complex.normSq z : ℝ) : ℂ) := by
    rw [mul_comm, _root_.Complex.mul_conj]
  rw [_root_.Complex.inner]
  constructor
  · intro h
    -- `w * conj z` is purely imaginary, so dividing by `z * conj z = normSq z` leaves a real
    -- multiple of `I * z`.
    set s : ℝ := (w * conj z).im with hs_def
    refine ⟨s / _root_.Complex.normSq z, ?_⟩
    have hwc : w * conj z = (s : ℂ) * I := by
      apply _root_.Complex.ext <;> simp [h, hs_def]
    push_cast
    rw [div_mul_eq_mul_div, eq_div_iff hnsC]
    calc w * ((_root_.Complex.normSq z : ℝ) : ℂ) = w * conj z * z := by rw [← hzc]; ring
      _ = (s : ℂ) * I * z := by rw [hwc]
      _ = (s : ℂ) * (z * I) := by ring
  · rintro ⟨t, rfl⟩
    have h : (t : ℂ) * (z * I) * conj z = ((t * _root_.Complex.normSq z : ℝ) : ℂ) * I :=
      calc (t : ℂ) * (z * I) * conj z = (t : ℂ) * I * (z * conj z) := by ring
        _ = (t : ℂ) * I * ((_root_.Complex.normSq z : ℝ) : ℂ) := by rw [_root_.Complex.mul_conj]
        _ = ((t * _root_.Complex.normSq z : ℝ) : ℂ) * I := by push_cast; ring
    rw [h]
    simp

/-- **Two orthogonal unit vectors of the plane differ by a quarter turn.** The unit-vector reading
of `TauCeti.real_inner_eq_zero_iff_exists_eq_real_mul_mul_I`: the real multiple it produces has
absolute value `1`, so it is `1` or `-1`. -/
theorem eq_mul_I_or_eq_neg_mul_I_of_real_inner_eq_zero {z w : ℂ} (hz : ‖z‖ = 1) (hw : ‖w‖ = 1)
    (h : ⟪z, w⟫ = 0) : w = z * I ∨ w = -(z * I) := by
  have hz0 : z ≠ 0 := by
    rw [← norm_ne_zero_iff, hz]
    norm_num
  obtain ⟨t, rfl⟩ := (real_inner_eq_zero_iff_exists_eq_real_mul_mul_I hz0).mp h
  have habs : |t| = 1 := by
    rwa [norm_mul, norm_mul, _root_.Complex.norm_real, Real.norm_eq_abs, hz,
      _root_.Complex.norm_I, mul_one, mul_one] at hw
  rcases (abs_eq zero_le_one).mp habs with ht | ht <;> rw [ht]
  · exact Or.inl (by push_cast; ring)
  · exact Or.inr (by push_cast; ring)

/-! ### The classification -/

variable {r : ℝ} {g : ℂ → ℂ}

/-- **Distance-preserving self-maps of a disc fixing its centre are rotations and rotated
conjugations.** A map of `ball 0 r` that fixes `0` and preserves the distance between any two of
its points agrees on that disc with `z ↦ u * z`, or with `z ↦ u * conj z`, for a single unit `u`.

No linearity and no surjectivity are assumed, and the map is only constrained on the disc; this is
what separates the statement from Mathlib's `linear_isometry_complex`, which classifies the
elements of `ℂ ≃ₗᵢ[ℝ] ℂ`. The single `u`, and the single choice between the two alternatives, are
the content: a priori each point of the disc could be reflected or not independently. -/
theorem exists_norm_eq_one_eqOn_ball_const_mul_or_const_mul_conj_of_dist_map_eq (hr : 0 < r)
    (h0 : g 0 = 0) (hg : ∀ z ∈ ball (0 : ℂ) r, ∀ w ∈ ball (0 : ℂ) r, dist (g z) (g w) = dist z w) :
    ∃ u : ℂ, ‖u‖ = 1 ∧
      (EqOn g (fun z => u * z) (ball (0 : ℂ) r) ∨
        EqOn g (fun z => u * conj z) (ball (0 : ℂ) r)) := by
  have hzero : (0 : ℂ) ∈ ball (0 : ℂ) r := mem_ball_self hr
  have hip : ∀ z ∈ ball (0 : ℂ) r, ∀ w ∈ ball (0 : ℂ) r, ⟪g z, g w⟫ = ⟪z, w⟫ :=
    fun _ hz _ hw => real_inner_map_map_of_dist_map_eq hzero h0 hg hz hw
  -- The two probe points, at half the radius along the two axes.
  set p : ℂ := ((r / 2 : ℝ) : ℂ) with hp_def
  set q : ℂ := I * p with hq_def
  have hnp : ‖p‖ = r / 2 := by
    rw [hp_def, _root_.Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  have hnq : ‖q‖ = r / 2 := by rw [hq_def, norm_mul, _root_.Complex.norm_I, one_mul, hnp]
  have hpm : p ∈ ball (0 : ℂ) r := by
    rw [mem_ball_zero_iff, hnp]
    linarith
  have hqm : q ∈ ball (0 : ℂ) r := by
    rw [mem_ball_zero_iff, hnq]
    linarith
  -- Their images, rescaled to unit length, are an orthonormal frame.
  set c : ℝ := 2 / r with hc_def
  have hcp : 0 < c := by
    rw [hc_def]
    positivity
  set e : ℂ := c • g p with he_def
  set f : ℂ := c • g q with hf_def
  have hne : ‖e‖ = 1 := by
    rw [he_def, norm_smul, Real.norm_eq_abs, abs_of_pos hcp,
      norm_map_of_dist_map_eq hzero h0 hg hpm, hnp, hc_def]
    field_simp
  have hnf : ‖f‖ = 1 := by
    rw [hf_def, norm_smul, Real.norm_eq_abs, abs_of_pos hcp,
      norm_map_of_dist_map_eq hzero h0 hg hqm, hnq, hc_def]
    field_simp
  -- The frame is orthogonal, and reads off the coordinates of every point of the disc.
  have hpre : p.re = r / 2 := by rw [hp_def, _root_.Complex.ofReal_re]
  have hpim : p.im = 0 := by rw [hp_def, _root_.Complex.ofReal_im]
  have hqre : q.re = 0 := by
    rw [hq_def, _root_.Complex.mul_re, _root_.Complex.I_re, _root_.Complex.I_im, hpre, hpim]
    ring
  have hqim : q.im = r / 2 := by
    rw [hq_def, _root_.Complex.mul_im, _root_.Complex.I_re, _root_.Complex.I_im, hpre, hpim]
    ring
  have hpq : ⟪p, q⟫ = 0 := by
    rw [real_inner_eq_re_mul_re_add_im_mul_im, hpre, hpim, hqre, hqim]
    ring
  have horth : ⟪e, f⟫ = 0 := by
    rw [he_def, hf_def, real_inner_smul_left, real_inner_smul_right, hip p hpm q hqm, hpq]
    ring
  have hre : ∀ z ∈ ball (0 : ℂ) r, ⟪e, g z⟫ = z.re := fun z hz => by
    rw [he_def, real_inner_smul_left, hip p hpm z hz, real_inner_eq_re_mul_re_add_im_mul_im, hpre,
      hpim, hc_def]
    field_simp
    ring
  have him : ∀ z ∈ ball (0 : ℂ) r, ⟪f, g z⟫ = z.im := fun z hz => by
    rw [hf_def, real_inner_smul_left, hip q hqm z hz, real_inner_eq_re_mul_re_add_im_mul_im, hqre,
      hqim, hc_def]
    field_simp
    ring
  -- `e * conj e = 1` lets the frame reading be undone.
  have hmul : e * conj e = 1 := by
    rw [_root_.Complex.mul_conj', hne]
    norm_num
  have hcoordre : ∀ z ∈ ball (0 : ℂ) r, (conj e * g z).re = z.re := fun z hz => by
    -- The real part of `conj e * g z` is `⟪e, g z⟫_ℝ` (`Complex.inner`, up to `mul_comm`).
    rw [mul_comm, ← _root_.Complex.inner]
    exact hre z hz
  refine ⟨e, hne, ?_⟩
  rcases eq_mul_I_or_eq_neg_mul_I_of_real_inner_eq_zero hne hnf horth with hcase | hcase
  · -- The frame is positively oriented: `g` is the rotation by `e`.
    refine Or.inl fun z hz => ?_
    have hcoordim : (conj e * g z).im = z.im := by
      -- The imaginary part of `conj e * g z` is the area form, which pairs the quarter turn
      -- `e * I = f` against `g z`.
      rw [← _root_.Complex.areaForm, ← Orientation.inner_rightAngleRotation_left,
        _root_.Complex.rightAngleRotation, mul_comm, ← hcase]
      exact him z hz
    have hxi : conj e * g z = z := _root_.Complex.ext (hcoordre z hz) hcoordim
    calc g z = e * (conj e * g z) := by rw [← mul_assoc, hmul, one_mul]
      _ = e * z := by rw [hxi]
  · -- The frame is negatively oriented: `g` is that rotation composed with the conjugation.
    refine Or.inr fun z hz => ?_
    have hcoordim : (conj e * g z).im = -z.im := by
      -- Same reading of the imaginary part, with `f = -(e * I)` now contributing the sign.
      rw [← _root_.Complex.areaForm, ← Orientation.inner_rightAngleRotation_left,
        _root_.Complex.rightAngleRotation, mul_comm, ← neg_neg (e * I), ← hcase, inner_neg_left]
      exact congrArg Neg.neg (him z hz)
    have hxi : conj e * g z = conj z := by
      refine _root_.Complex.ext ?_ ?_
      · rw [_root_.Complex.conj_re]
        exact hcoordre z hz
      · rw [_root_.Complex.conj_im]
        exact hcoordim
    calc g z = e * (conj e * g z) := by rw [← mul_assoc, hmul, one_mul]
      _ = e * conj z := by rw [hxi]

/-- **The distance-preserving self-maps of a disc fixing its centre are exactly the rotations and
the rotated conjugations.** The converse half is immediate — multiplication by a unit and
conjugation are both isometries of `ℂ`, and both fix `0` — so
`TauCeti.exists_norm_eq_one_eqOn_ball_const_mul_or_const_mul_conj_of_dist_map_eq` closes the
description into an equivalence. -/
theorem exists_norm_eq_one_eqOn_ball_const_mul_or_const_mul_conj_iff (hr : 0 < r) :
    (g 0 = 0 ∧ ∀ z ∈ ball (0 : ℂ) r, ∀ w ∈ ball (0 : ℂ) r, dist (g z) (g w) = dist z w) ↔
      ∃ u : ℂ, ‖u‖ = 1 ∧
        (EqOn g (fun z => u * z) (ball (0 : ℂ) r) ∨
          EqOn g (fun z => u * conj z) (ball (0 : ℂ) r)) := by
  constructor
  · rintro ⟨h0, hg⟩
    exact exists_norm_eq_one_eqOn_ball_const_mul_or_const_mul_conj_of_dist_map_eq hr h0 hg
  · rintro ⟨u, hu, hcase⟩
    have hzero : (0 : ℂ) ∈ ball (0 : ℂ) r := mem_ball_self hr
    rcases hcase with hcase | hcase
    · refine ⟨by simpa using hcase hzero, fun z hz w hw => ?_⟩
      rw [_root_.Complex.dist_eq, _root_.Complex.dist_eq, hcase hz, hcase hw, ← mul_sub, norm_mul,
        hu, one_mul]
    · refine ⟨by simpa using hcase hzero, fun z hz w hw => ?_⟩
      rw [_root_.Complex.dist_eq, _root_.Complex.dist_eq, hcase hz, hcase hw, ← mul_sub,
        ← map_sub, norm_mul, hu, one_mul, _root_.Complex.norm_conj]

end TauCeti
