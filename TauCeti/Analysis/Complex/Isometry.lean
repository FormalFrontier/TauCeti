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
`⟪e, g z⟫_ℝ`, `⟪f, g z⟫_ℝ` read off the real and imaginary parts of `z`. Orthogonality of two unit
complex numbers means a quarter turn, `f = e * I` or `f = -(e * I)`
(`TauCeti.eq_mul_I_or_eq_neg_mul_I_of_real_inner_eq_zero`, where Mathlib's two-dimensional
orientation API enters, its quarter turn `Complex.rightAngleRotation` being multiplication by
`I`), and pairing `g z` against `e` and against `e * I` recovers `g z` as `e * z` in the first case
and as `e * conj z` in the second — the alternative being fixed once, by `f`, and not per point.

That argument is adapted from the proof of
`TauCeti.exists_norm_eq_one_eqOn_ball_const_mul_or_const_mul_conj` and its `private` scaffolding
(`real_inner_eq`, `im_conj_mul`, `exists_orthonormal_pair_real_inner_map_eq`,
`eq_mul_I_or_eq_neg_mul_I`) in
`TauCeti/Analysis/Complex/Conformal/Poincare/Isometry/Classification.lean`, as merged in
TauCeti#1502; here the unit radius is relaxed to an arbitrary `r > 0` and the hyperbolic
hypothesis is replaced by the Euclidean one the argument actually used.

## Main results

* `TauCeti.eq_mul_I_or_eq_neg_mul_I_of_real_inner_eq_zero` — two orthogonal unit vectors of the
  Euclidean plane `ℂ` differ by the quarter turn `z ↦ z * I`.
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

/-! ### Orthogonality in the Euclidean plane -/

/-- **Two orthogonal unit vectors of the plane differ by a quarter turn.** For unit complex
numbers `z` and `w` with `⟪z, w⟫_ℝ = 0`, either `w = z * I` or `w = -(z * I)`.

The plane being two-dimensional, the orthogonal complement of a nonzero `z` is the real line
through the quarter turn `z * I`; that is Mathlib's
`Submodule.mem_span_singleton_of_inner_eq_zero_of_inner_eq_zero`, the quarter turn being
`Complex.orientation.rightAngleRotation` (`Complex.rightAngleRotation`). Being a unit vector, the
real multiple it produces is `1` or `-1`. -/
theorem eq_mul_I_or_eq_neg_mul_I_of_real_inner_eq_zero {z w : ℂ} (hz : ‖z‖ = 1) (hw : ‖w‖ = 1)
    (h : ⟪z, w⟫ = 0) : w = z * I ∨ w = -(z * I) := by
  have hz0 : z ≠ 0 := by
    rw [← norm_ne_zero_iff, hz]
    norm_num
  have hzI0 : z * I ≠ 0 := mul_ne_zero hz0 _root_.Complex.I_ne_zero
  -- The quarter turn of `z` is orthogonal to `z`, so it spans the orthogonal complement.
  have hperp : ⟪z, z * I⟫ = 0 := by
    rw [mul_comm, ← _root_.Complex.rightAngleRotation, real_inner_comm,
      Orientation.inner_rightAngleRotation_self]
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp
    (Submodule.mem_span_singleton_of_inner_eq_zero_of_inner_eq_zero hz0 hzI0 h hperp)
  have hnzI : ‖z * I‖ = 1 := by rw [norm_mul, _root_.Complex.norm_I, hz, mul_one]
  have habs : |t| = 1 := by
    rwa [← ht, norm_smul, Real.norm_eq_abs, hnzI, mul_one] at hw
  rcases (abs_eq zero_le_one).mp habs with hteq | hteq <;> rw [← ht, hteq]
  · exact Or.inl (one_smul _ _)
  · exact Or.inr (by rw [neg_smul, one_smul])

/-- **A unit vector and its quarter turn recover a point of the plane from two inner products.**
If `⟪e, w⟫_ℝ` is the real part of `v` and `⟪e * I, w⟫_ℝ` is its imaginary part, for a unit `e`,
then `w = e * v`.

Read at `v` and at `conj v`, this is what turns the two orientations of the frame `e`, `e * I`
into the two alternatives of the classification below. -/
private theorem eq_mul_of_real_inner_eq_re_of_real_inner_mul_I_eq_im {e w v : ℂ} (he : ‖e‖ = 1)
    (hre : ⟪e, w⟫ = v.re) (him : ⟪e * I, w⟫ = v.im) : w = e * v := by
  -- pairing `w` against `e` and against `e * I` reads off the two parts of `w * conj e`
  have him' : (w * conj e).im = ⟪e * I, w⟫ := by
    simp only [_root_.Complex.inner, map_mul, _root_.Complex.conj_I, _root_.Complex.mul_re,
      _root_.Complex.mul_im, _root_.Complex.neg_re, _root_.Complex.neg_im, _root_.Complex.I_re,
      _root_.Complex.I_im]
    ring
  have hmul : e * conj e = 1 := by rw [_root_.Complex.mul_conj', he]; norm_num
  have hv : w * conj e = v :=
    _root_.Complex.ext (by rw [← _root_.Complex.inner]; exact hre) (by rw [him']; exact him)
  calc w = e * (w * conj e) := by rw [← mul_assoc, mul_comm e w, mul_assoc, hmul, mul_one]
    _ = e * v := by rw [hv]

/-! ### The classification -/

variable {r : ℝ} {g : ℂ → ℂ}

/-- **The values on a disc of a distance-preserving map fixing its centre are read by a single
orthonormal frame.** There are orthogonal unit vectors `e`, `f` for which `⟪e, g z⟫_ℝ` and
`⟪f, g z⟫_ℝ` are the real and imaginary parts of `z`, for every `z` of the disc. The one frame
serves every point; that is what later fixes a single `u` in the classification. -/
private theorem exists_orthonormal_pair_real_inner_map_eq_of_dist_map_eq (hr : 0 < r) (h0 : g 0 = 0)
    (hg : ∀ z ∈ ball (0 : ℂ) r, ∀ w ∈ ball (0 : ℂ) r, dist (g z) (g w) = dist z w) :
    ∃ e f : ℂ, ‖e‖ = 1 ∧ ‖f‖ = 1 ∧ ⟪e, f⟫ = 0 ∧
      (∀ z ∈ ball (0 : ℂ) r, ⟪e, g z⟫ = z.re) ∧ ∀ z ∈ ball (0 : ℂ) r, ⟪f, g z⟫ = z.im := by
  have hzero : (0 : ℂ) ∈ ball (0 : ℂ) r := mem_ball_self hr
  -- the probe point in a unit direction `a`, at half the radius
  have hnorm : ∀ a : ℂ, ‖a‖ = 1 → ‖((r / 2 : ℝ) • a : ℂ)‖ = r / 2 := fun a ha => by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith), ha, mul_one]
  have hmem : ∀ a : ℂ, ‖a‖ = 1 → ((r / 2 : ℝ) • a : ℂ) ∈ ball (0 : ℂ) r := fun a ha => by
    rw [mem_ball_zero_iff, hnorm a ha]
    linarith
  -- its image, doubled by `2 / r`, is a unit vector pairing as `a` itself does
  have key : ∀ a : ℂ, ‖a‖ = 1 → ‖(2 / r : ℝ) • g ((r / 2 : ℝ) • a)‖ = 1 ∧
      ∀ z ∈ ball (0 : ℂ) r, ⟪(2 / r : ℝ) • g ((r / 2 : ℝ) • a), g z⟫ = ⟪a, z⟫ := fun a ha => by
    refine ⟨?_, fun z hz => ?_⟩
    · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos two_pos hr),
        norm_map_of_dist_map_eq hzero h0 hg (hmem a ha), hnorm a ha]
      field_simp
    · rw [real_inner_smul_left, real_inner_map_map_of_dist_map_eq hzero h0 hg (hmem a ha) hz,
        real_inner_smul_left]
      field_simp
  obtain ⟨hne, hre⟩ := key 1 norm_one
  obtain ⟨hnf, him⟩ := key I _root_.Complex.norm_I
  refine ⟨_, _, hne, hnf, ?_, fun z hz => by simpa using hre z hz,
    fun z hz => by simpa using him z hz⟩
  rw [real_inner_smul_right, hre _ (hmem I _root_.Complex.norm_I)]
  simp

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
  obtain ⟨e, f, hne, hnf, horth, hre, him⟩ :=
    exists_orthonormal_pair_real_inner_map_eq_of_dist_map_eq hr h0 hg
  refine ⟨e, hne, ?_⟩
  rcases eq_mul_I_or_eq_neg_mul_I_of_real_inner_eq_zero hne hnf horth with hcase | hcase
  · -- The frame is positively oriented: `g` is the rotation by `e`.
    exact Or.inl fun z hz => eq_mul_of_real_inner_eq_re_of_real_inner_mul_I_eq_im hne (hre z hz)
      (by rw [← hcase]; exact him z hz)
  · -- The frame is negatively oriented: `g` is that rotation composed with the conjugation.
    refine Or.inr fun z hz => eq_mul_of_real_inner_eq_re_of_real_inner_mul_I_eq_im (v := conj z)
      hne (by rw [_root_.Complex.conj_re]; exact hre z hz) ?_
    rw [_root_.Complex.conj_im, ← neg_eq_iff_eq_neg, ← inner_neg_left, ← hcase]
    exact him z hz

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
