/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.Poincare.Betweenness

/-!
# Poincaré geodesics are Euclidean circles orthogonal to the unit circle

`Conformal/Poincare/Geodesic.lean` builds the unit-speed geodesic lines of the Poincaré disc,
`TauCeti.PoincareDisc.geodesicLine a u`, as the radial geodesics `t ↦ u * Real.tanh t` carried
off the origin by a Moebius isometry, and `Conformal/Poincare/Betweenness.lean` shows that these
are *all* the geodesic lines. What neither says is what a geodesic looks like in the *Euclidean*
plane away from the origin: through the origin it is a diameter, and off the origin it is the
classical arc of a circle meeting the unit circle at right angles. This file proves that.

The route is to read "lies on the geodesic through `a` in direction `u`" as an equation. Applying
the Moebius isometry that sends `a` to the origin turns it into "lies on a diameter", which is
the reality of `conj u * z`; pulling that back through `z ↦ (z - a) / (1 - conj a * z)` and
clearing the denominator gives the equation

`Im (conj u * (z - a) * (1 - a * conj z)) = 0`,

and `TauCeti.im_conj_mul_sub_mul_one_sub_mul_conj` rearranges it into the shape of a Euclidean
circle equation, `Im (B * z) = A * (‖z‖ ^ 2 + 1)` with `A = Im (conj u * a)` and
`B = conj u - u * conj a ^ 2`. The coefficient of `‖z‖ ^ 2` and the constant term are *equal*,
and that is exactly orthogonality to the unit circle: completing the square in that equation
gives a circle of centre `c` and radius `R` with `‖c‖ ^ 2 = R ^ 2 + 1`, the Pythagorean relation
saying that the tangent length from `c` to the unit circle is `R`. The radius is positive because
of the identity

`‖B‖ ^ 2 - 4 * A ^ 2 = (1 - ‖a‖ ^ 2) ^ 2`

(`TauCeti.normSq_sub_mul_conj_sq_sub_four_mul_sq_im`), which is where `‖u‖ = 1` and `‖a‖ < 1`
enter. The degenerate case `A = 0` is exactly the case in which the geodesic passes through the
origin, and then the equation collapses to the Euclidean diameter `Im (conj u * z) = 0`.

## Main results

* `TauCeti.PoincareDisc.mem_range_radialGeodesic_iff` — a point of the Poincaré disc lies on the
  radial geodesic in direction `u` exactly when `conj u * z` is real.
* `TauCeti.PoincareDisc.mem_range_geodesicLine_iff` — the equation of the geodesic line through
  `a` in direction `u`.
* `TauCeti.PoincareDisc.range_coe_radialGeodesic_eq` — a geodesic through the origin traces the
  Euclidean diameter in its direction.
* `TauCeti.PoincareDisc.exists_range_coe_geodesicLine_eq_ball_inter_sphere` — a geodesic line
  missing the origin traces `ball 0 1 ∩ sphere c R` for a Euclidean circle **orthogonal to the
  unit circle**, `‖c‖ ^ 2 = R ^ 2 + 1`.
* `TauCeti.PoincareDisc.range_coe_geodesicLine_eq_ball_inter_or` — the two cases together: every
  geodesic line of the Poincaré disc traces the intersection of the disc with a Euclidean line
  through the origin or with a Euclidean circle orthogonal to the unit circle.
* `TauCeti.PoincareDisc.range_coe_eq_ball_inter_or_of_isometry` — the same for an arbitrary
  isometric embedding of the real line, which is the parametrisation-free classification.

## Generality

In accordance with the generality bar of `ConformalMapping/README.md`, which fixes scalar `ℂ`
for layers L0--L6, everything is stated for the complex unit disc. The plane-geometry lemmas of
the first section ask nothing of `a` beyond `‖a‖ < 1` and nothing of `u` beyond `‖u‖ = 1`, and
are stated for bare complex numbers so that they can be reused off the `PoincareDisc` synonym.

## Coordination with upstream Mathlib

This is L2 material, "the hyperbolic / Poincaré metric on `𝔻`" of
`TauCetiRoadmap/ConformalMapping/README.md`, and as such falls under that roadmap's coordination
clause for the in-progress human-curated Riemann-mapping effort
[mathlib4#33505](https://github.com/leanprover-community/mathlib4/pull/33505): it should be
refactored onto upstream API if that work lands a Poincaré-disc geometry. The pinned Mathlib has
the hyperbolic metric on the upper half-plane (`Analysis/Complex/UpperHalfPlane`) but no
Poincaré metric on the disc and no description of its geodesics; nothing is vendored here.

## References

* L. V. Ahlfors, *Conformal Invariants*, Ch. 1 (the hyperbolic metric of the disc).
* J. B. Conway, *Functions of One Complex Variable I* (GTM 11), Ch. III (Moebius transformations
  and circles).
-/

public section

namespace TauCeti

open _root_.Complex Metric Set
open scoped ComplexConjugate

/-! ## The equation of a hyperbolic line in the plane -/

/-- **The geodesic equation is a Euclidean circle equation.** The quantity
`Im (conj u * (z - a) * (1 - a * conj z))`, which cuts out the hyperbolic line through `a` in
direction `u`, is `Im (B * z) - A * (‖z‖ ^ 2 + 1)` for `A = Im (conj u * a)` and
`B = conj u - u * conj a ^ 2`.

The point of the rearrangement is that the coefficient of `‖z‖ ^ 2` and the constant term are the
same number `A`; a circle equation `A * ‖z‖ ^ 2 - Im (B * z) + C = 0` describes a circle
orthogonal to the unit circle exactly when `A = C`, so the geodesic equation *is* the equation of
such a circle. No hypothesis is needed: this is an identity of real numbers. -/
theorem im_conj_mul_sub_mul_one_sub_mul_conj (u a z : ℂ) :
    (conj u * (z - a) * (1 - a * conj z)).im
      = ((conj u - u * conj a ^ 2) * z).im - (conj u * a).im * (normSq z + 1) := by
  simp only [Complex.mul_im, Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.one_re,
    Complex.one_im, Complex.conj_re, Complex.conj_im, Complex.normSq_apply, pow_two]
  ring

/-- **The discriminant identity behind the radius.** For `‖u‖ = 1`, the linear coefficient `B` and
the quadratic coefficient `A` of the geodesic equation
(`TauCeti.im_conj_mul_sub_mul_one_sub_mul_conj`) satisfy `‖B‖ ^ 2 - 4 * A ^ 2 = (1 - ‖a‖ ^ 2) ^ 2`.

Completing the square turns the geodesic equation into `‖z - c‖ ^ 2 = ‖c‖ ^ 2 - 1` with
`‖c‖ ^ 2 = ‖B‖ ^ 2 / (4 * A ^ 2)`, so this identity is what makes the radius
`(1 - ‖a‖ ^ 2) / (2 * |A|)` positive when `‖a‖ < 1`: the circle is a genuine circle and not a
point or the empty set. -/
theorem normSq_sub_mul_conj_sq_sub_four_mul_sq_im {u : ℂ} (hu : ‖u‖ = 1) (a : ℂ) :
    normSq (conj u - u * conj a ^ 2) - 4 * (conj u * a).im ^ 2 = (1 - normSq a) ^ 2 := by
  have hu' : u.re * u.re + u.im * u.im = 1 := by
    rw [← Complex.normSq_apply, Complex.normSq_eq_norm_sq, hu]
    norm_num
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.conj_re, Complex.conj_im, pow_two]
  linear_combination (1 - (a.re * a.re + a.im * a.im)) ^ 2 * hu'

/-- Completing the square: with `c` the centre determined by `conj c = -I * B / (2 * A)` and `R`
a radius satisfying the orthogonality relation `‖c‖ ^ 2 = R ^ 2 + 1`, the squared distance to `c`
is the geodesic equation divided by `-A`. -/
private lemma mul_normSq_sub_sub_sq {A R : ℝ} {B c : ℂ} (hA : A ≠ 0)
    (hc : conj c = -I * B / ((2 * A : ℝ) : ℂ)) (h1 : normSq c = R ^ 2 + 1) (z : ℂ) :
    A * (normSq (z - c) - R ^ 2) = A * (normSq z + 1) - (B * z).im := by
  have h2A : (2 : ℝ) * A ≠ 0 := mul_ne_zero two_ne_zero hA
  have hcc : (z * conj c).re = (B * z).im / (2 * A) := by
    rw [hc, ← mul_div_assoc, Complex.div_ofReal_re]
    congr 1
    simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.I_re,
      Complex.I_im]
    ring
  rw [Complex.normSq_sub, hcc, h1]
  field_simp
  ring

/-- **A hyperbolic line off the origin is an arc of a Euclidean circle orthogonal to the unit
circle.** If `‖u‖ = 1`, `‖a‖ < 1` and the geodesic through `a` in direction `u` misses the origin
— which is exactly `Im (conj u * a) ≠ 0` — then its plane equation cuts out `ball 0 1 ∩ sphere c R`
for a centre `c` and a radius `R > 0` with `‖c‖ ^ 2 = R ^ 2 + 1`.

The relation `‖c‖ ^ 2 = R ^ 2 + 1` is Pythagoras for the right triangle whose legs are the radius
of the unit circle and the radius `R`: it says precisely that the two circles meet at right
angles. The witnesses are `c = I * conj B / (2 * A)` and `R = (1 - ‖a‖ ^ 2) / (2 * |A|)`, with
`A` and `B` as in `TauCeti.im_conj_mul_sub_mul_one_sub_mul_conj`. -/
theorem exists_setOf_im_eq_ball_inter_sphere {u a : ℂ} (hu : ‖u‖ = 1) (ha : ‖a‖ < 1)
    (hA : (conj u * a).im ≠ 0) :
    ∃ c : ℂ, ∃ R : ℝ, 0 < R ∧ ‖c‖ ^ 2 = R ^ 2 + 1 ∧
      {z : ℂ | ‖z‖ < 1 ∧ (conj u * (z - a) * (1 - a * conj z)).im = 0}
        = ball 0 1 ∩ sphere c R := by
  have hna : normSq a < 1 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg a]
  have hkey := normSq_sub_mul_conj_sq_sub_four_mul_sq_im hu a
  have habs : 0 < |(conj u * a).im| := abs_pos.mpr hA
  set A : ℝ := (conj u * a).im with hAdef
  set B : ℂ := conj u - u * conj a ^ 2 with hBdef
  set R : ℝ := (1 - normSq a) / (2 * |A|) with hRdef
  set c : ℂ := I * conj B / ((2 * A : ℝ) : ℂ) with hcdef
  have hRpos : 0 < R := by
    rw [hRdef]
    have : 0 < 1 - normSq a := by linarith
    positivity
  have hnc : normSq c = R ^ 2 + 1 := by
    rw [hcdef, hRdef, Complex.normSq_div, Complex.normSq_mul, Complex.normSq_I,
      Complex.normSq_conj, Complex.normSq_ofReal, div_pow, mul_pow, sq_abs]
    have h4 : (0 : ℝ) < 4 * A ^ 2 := by positivity
    field_simp
    linarith [hkey]
  have hconjc : conj c = -I * B / ((2 * A : ℝ) : ℂ) := by
    rw [hcdef, map_div₀, map_mul, Complex.conj_I, Complex.conj_conj, Complex.conj_ofReal]
  refine ⟨c, R, hRpos, by rw [← Complex.normSq_eq_norm_sq]; exact hnc, ?_⟩
  ext z
  have hid := mul_normSq_sub_sub_sq hA hconjc hnc z
  have heq : (conj u * (z - a) * (1 - a * conj z)).im = (B * z).im - A * (normSq z + 1) := by
    rw [hBdef, hAdef]
    exact im_conj_mul_sub_mul_one_sub_mul_conj u a z
  have hlink : A * (normSq (z - c) - R ^ 2) = -(conj u * (z - a) * (1 - a * conj z)).im := by
    rw [heq, hid]
    ring
  simp only [Set.mem_ofPred_eq, mem_inter_iff, mem_ball_zero_iff, mem_sphere_iff_norm]
  refine and_congr_right fun _ => ?_
  constructor
  · intro him
    have hzero : normSq (z - c) - R ^ 2 = 0 := by
      have := hlink
      rw [him, neg_zero] at this
      exact (mul_eq_zero.mp this).resolve_left hA
    have hsq : ‖z - c‖ ^ 2 = R ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq]
      linarith
    have := congrArg Real.sqrt hsq
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hRpos.le] at this
  · intro hdist
    have hsq : normSq (z - c) = R ^ 2 := by
      rw [Complex.normSq_eq_norm_sq, hdist]
    rw [hsq, sub_self, mul_zero] at hlink
    linarith [hlink]

/-- **A hyperbolic line through the origin is a Euclidean diameter.** If `Im (conj u * a) = 0` —
the case excluded in `TauCeti.exists_setOf_im_eq_ball_inter_sphere` — then `a` is a real multiple
of `u`, so the geodesic through `a` in direction `u` is the one through the origin, and its plane
equation collapses to the reality of `conj u * z`. -/
theorem setOf_im_eq_ball_inter_setOf_im {u a : ℂ} (hu : ‖u‖ = 1) (ha : ‖a‖ < 1)
    (hA : (conj u * a).im = 0) :
    {z : ℂ | ‖z‖ < 1 ∧ (conj u * (z - a) * (1 - a * conj z)).im = 0}
      = ball 0 1 ∩ {z : ℂ | (conj u * z).im = 0} := by
  set s : ℝ := (conj u * a).re with hs
  have hua : conj u * a = (s : ℂ) := Complex.ext rfl (by simpa using hA)
  have huu : u * conj u = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hu]
    norm_num
  have hasu : a = u * (s : ℂ) := by
    calc a = u * conj u * a := by rw [huu, one_mul]
      _ = u * (conj u * a) := by ring
      _ = u * (s : ℂ) := by rw [hua]
  have hsn : |s| = ‖a‖ := by
    rw [← Real.norm_eq_abs, ← Complex.norm_real, ← hua, norm_mul, norm_conj, hu, one_mul]
  have hs1 : s ^ 2 < 1 := by
    rw [← sq_abs, hsn]
    nlinarith [norm_nonneg a]
  have hB : conj u - u * conj a ^ 2 = conj u * ((1 - s ^ 2 : ℝ) : ℂ) := by
    rw [hasu, map_mul, Complex.conj_ofReal]
    have hexp : u * (conj u * (s : ℂ)) ^ 2 = (u * conj u) * (conj u * (s : ℂ) ^ 2) := by ring
    rw [hexp, huu, one_mul]
    push_cast
    ring
  ext z
  simp only [Set.mem_ofPred_eq, mem_inter_iff, mem_ball_zero_iff]
  refine and_congr_right fun _ => ?_
  rw [im_conj_mul_sub_mul_one_sub_mul_conj, hA, zero_mul, sub_zero, hB]
  have hmul : conj u * ((1 - s ^ 2 : ℝ) : ℂ) * z = ((1 - s ^ 2 : ℝ) : ℂ) * (conj u * z) := by
    ring
  rw [hmul, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
    mul_eq_zero]
  constructor
  · rintro (h | h)
    · exact absurd h (by nlinarith)
    · exact h
  · exact fun h => Or.inr h

/-! ## The geodesics of the Poincaré disc -/

namespace PoincareDisc

/-- The imaginary part of a quotient vanishes exactly when it does after clearing the
denominator. -/
private lemma im_div_eq_zero_iff {w v : ℂ} (hv : v ≠ 0) :
    (w / v).im = 0 ↔ (w * conj v).im = 0 := by
  have h : w / v = w * conj v * (((normSq v)⁻¹ : ℝ) : ℂ) := by
    rw [div_eq_mul_inv, Complex.inv_def, ← mul_assoc]
  rw [h, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add,
    mul_eq_zero, inv_eq_zero, Complex.normSq_eq_zero]
  simp [hv]

/-- **The equation of a geodesic through the origin.** A point `z` of the Poincaré disc lies on
the radial geodesic in direction `u` exactly when `conj u * z` is real, that is, when `z` lies on
the Euclidean diameter in direction `u`. -/
theorem mem_range_radialGeodesic_iff (u : Circle) (z : PoincareDisc) :
    z ∈ Set.range (radialGeodesic u) ↔ (conj (u : ℂ) * (toUnitDisc z : ℂ)).im = 0 := by
  have huu : (u : ℂ) * conj (u : ℂ) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Circle.norm_coe]
    norm_num
  constructor
  · rintro ⟨t, rfl⟩
    rw [coe_radialGeodesic]
    have h : conj (u : ℂ) * ((u : ℂ) * (Real.tanh t : ℂ)) = ((Real.tanh t : ℝ) : ℂ) := by
      calc conj (u : ℂ) * ((u : ℂ) * (Real.tanh t : ℂ))
          = ((u : ℂ) * conj (u : ℂ)) * (Real.tanh t : ℂ) := by ring
        _ = ((Real.tanh t : ℝ) : ℂ) := by rw [huu, one_mul]
    rw [h, Complex.ofReal_im]
  · intro h
    set s : ℝ := (conj (u : ℂ) * (toUnitDisc z : ℂ)).re with hsdef
    have hus : conj (u : ℂ) * (toUnitDisc z : ℂ) = (s : ℂ) := Complex.ext rfl (by simpa using h)
    have hzu : (toUnitDisc z : ℂ) = (u : ℂ) * (s : ℂ) := by
      calc (toUnitDisc z : ℂ) = (u : ℂ) * conj (u : ℂ) * (toUnitDisc z : ℂ) := by
            rw [huu, one_mul]
        _ = (u : ℂ) * (conj (u : ℂ) * (toUnitDisc z : ℂ)) := by ring
        _ = (u : ℂ) * (s : ℂ) := by rw [hus]
    have hsn : |s| = ‖(toUnitDisc z : ℂ)‖ := by
      rw [← Real.norm_eq_abs, ← Complex.norm_real, ← hus, norm_mul, norm_conj, Circle.norm_coe,
        one_mul]
    have hs1 : |s| < 1 := hsn ▸ (toUnitDisc z).norm_lt_one
    obtain ⟨hs_lo, hs_hi⟩ := abs_lt.mp hs1
    refine ⟨Real.artanh s, toUnitDisc.injective (Complex.UnitDisc.coe_injective ?_)⟩
    rw [coe_radialGeodesic, Real.tanh_artanh ⟨hs_lo, hs_hi⟩, hzu]

/-- **The equation of a geodesic line.** A point `z` of the Poincaré disc lies on the geodesic
line through `a` in direction `u` exactly when
`Im (conj u * (z - a) * (1 - a * conj z)) = 0`.

The Moebius isometry sending `a` to the origin straightens the geodesic into the radial one
(`TauCeti.PoincareDisc.unitDiscMoebiusIsometryEquiv_geodesicLine`), where
`TauCeti.PoincareDisc.mem_range_radialGeodesic_iff` applies; clearing the Moebius denominator,
which is nonzero on the disc, gives the polynomial form. -/
theorem mem_range_geodesicLine_iff (a : PoincareDisc) (u : Circle) (z : PoincareDisc) :
    z ∈ Set.range (geodesicLine a u) ↔
      (conj (u : ℂ) * ((toUnitDisc z : ℂ) - (toUnitDisc a : ℂ)) *
        (1 - (toUnitDisc a : ℂ) * conj (toUnitDisc z : ℂ))).im = 0 := by
  have hmem : z ∈ Set.range (geodesicLine a u) ↔
      unitDiscMoebiusIsometryEquiv (toUnitDisc a) z ∈ Set.range (radialGeodesic u) := by
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨t, by rw [unitDiscMoebiusIsometryEquiv_geodesicLine]⟩
    · rintro ⟨t, ht⟩
      exact ⟨t, by rw [geodesicLine_def, ht, IsometryEquiv.symm_apply_apply]⟩
  have hne : 1 - conj (toUnitDisc a : ℂ) * (toUnitDisc z : ℂ) ≠ 0 := by
    intro hzero
    have h1 : ‖conj (toUnitDisc a : ℂ) * (toUnitDisc z : ℂ)‖ = 1 := by
      rw [← sub_eq_zero.mp hzero]
      exact norm_one
    rw [norm_mul, norm_conj] at h1
    nlinarith [(toUnitDisc a).norm_lt_one, (toUnitDisc z).norm_lt_one,
      norm_nonneg (toUnitDisc a : ℂ), norm_nonneg (toUnitDisc z : ℂ)]
  have hconj : conj (1 - conj (toUnitDisc a : ℂ) * (toUnitDisc z : ℂ))
      = 1 - (toUnitDisc a : ℂ) * conj (toUnitDisc z : ℂ) := by
    rw [map_sub, map_one, map_mul, Complex.conj_conj]
  rw [hmem, mem_range_radialGeodesic_iff, unitDiscMoebiusIsometryEquiv_apply,
    toUnitDisc_toPoincare, coe_unitDiscMoebius, ← mul_div_assoc, im_div_eq_zero_iff hne, hconj]

/-- **A geodesic through the origin traces a Euclidean diameter.** The radial geodesic in
direction `u` sweeps out exactly the intersection of the open unit disc with the Euclidean line
through the origin in direction `u`. -/
theorem range_coe_radialGeodesic_eq (u : Circle) :
    Set.range (fun t : ℝ => ((toUnitDisc (radialGeodesic u t) : Complex.UnitDisc) : ℂ))
      = ball 0 1 ∩ {z : ℂ | (conj (u : ℂ) * z).im = 0} := by
  ext z
  simp only [Set.mem_range, Set.mem_ofPred_eq, mem_inter_iff, mem_ball_zero_iff]
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨(toUnitDisc (radialGeodesic u t)).norm_lt_one,
      (mem_range_radialGeodesic_iff u (radialGeodesic u t)).mp ⟨t, rfl⟩⟩
  · rintro ⟨hz, him⟩
    obtain ⟨t, ht⟩ := (mem_range_radialGeodesic_iff u
      (Complex.UnitDisc.toPoincare (Complex.UnitDisc.mk z hz))).mpr (by simpa using him)
    refine ⟨t, ?_⟩
    show ((toUnitDisc (radialGeodesic u t) : Complex.UnitDisc) : ℂ) = z
    rw [ht]
    simp

/-- The plane description of the geodesic line through `a` in direction `u`: it traces the set of
points of the open unit disc satisfying the geodesic equation. -/
theorem range_coe_geodesicLine_eq (a : PoincareDisc) (u : Circle) :
    Set.range (fun t : ℝ => ((toUnitDisc (geodesicLine a u t) : Complex.UnitDisc) : ℂ))
      = {z : ℂ | ‖z‖ < 1 ∧ (conj (u : ℂ) * (z - (toUnitDisc a : ℂ)) *
          (1 - (toUnitDisc a : ℂ) * conj z)).im = 0} := by
  ext z
  simp only [Set.mem_range, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨(toUnitDisc (geodesicLine a u t)).norm_lt_one,
      (mem_range_geodesicLine_iff a u (geodesicLine a u t)).mp ⟨t, rfl⟩⟩
  · rintro ⟨hz, him⟩
    obtain ⟨t, ht⟩ := (mem_range_geodesicLine_iff a u
      (Complex.UnitDisc.toPoincare (Complex.UnitDisc.mk z hz))).mpr (by simpa using him)
    refine ⟨t, ?_⟩
    show ((toUnitDisc (geodesicLine a u t) : Complex.UnitDisc) : ℂ) = z
    rw [ht]
    simp

/-- **A geodesic line missing the origin traces an arc of a Euclidean circle orthogonal to the
unit circle.** If `Im (conj u * a) ≠ 0`, the geodesic line of the Poincaré disc through `a` in
direction `u` sweeps out `ball 0 1 ∩ sphere c R` for a Euclidean circle whose centre and radius
satisfy `‖c‖ ^ 2 = R ^ 2 + 1`, the Pythagorean relation expressing that it meets the unit circle
at right angles.

This is the classical picture of the Poincaré disc, and it is
`TauCeti.exists_setOf_im_eq_ball_inter_sphere` read through
`TauCeti.PoincareDisc.range_coe_geodesicLine_eq`. -/
theorem exists_range_coe_geodesicLine_eq_ball_inter_sphere (a : PoincareDisc) (u : Circle)
    (hA : (conj (u : ℂ) * (toUnitDisc a : ℂ)).im ≠ 0) :
    ∃ c : ℂ, ∃ R : ℝ, 0 < R ∧ ‖c‖ ^ 2 = R ^ 2 + 1 ∧
      Set.range (fun t : ℝ => ((toUnitDisc (geodesicLine a u t) : Complex.UnitDisc) : ℂ))
        = ball 0 1 ∩ sphere c R := by
  obtain ⟨c, R, hR, horth, hset⟩ :=
    exists_setOf_im_eq_ball_inter_sphere (Circle.norm_coe u) (toUnitDisc a).norm_lt_one hA
  exact ⟨c, R, hR, horth, by rw [range_coe_geodesicLine_eq, hset]⟩

/-- **A geodesic line through the origin traces a Euclidean diameter.** The complementary case of
`TauCeti.PoincareDisc.exists_range_coe_geodesicLine_eq_ball_inter_sphere`: when
`Im (conj u * a) = 0` the base point `a` is a real multiple of the direction `u`, so the geodesic
line through `a` is the radial one and traces the Euclidean diameter in direction `u`. -/
theorem range_coe_geodesicLine_eq_ball_inter_setOf (a : PoincareDisc) (u : Circle)
    (hA : (conj (u : ℂ) * (toUnitDisc a : ℂ)).im = 0) :
    Set.range (fun t : ℝ => ((toUnitDisc (geodesicLine a u t) : Complex.UnitDisc) : ℂ))
      = ball 0 1 ∩ {z : ℂ | (conj (u : ℂ) * z).im = 0} := by
  rw [range_coe_geodesicLine_eq,
    setOf_im_eq_ball_inter_setOf_im (Circle.norm_coe u) (toUnitDisc a).norm_lt_one hA]

/-- **The geodesics of the Poincaré disc, in Euclidean terms.** Every geodesic line of the
Poincaré disc traces either the intersection of the open unit disc with a Euclidean line through
the origin, or its intersection with a Euclidean circle orthogonal to the unit circle
(`‖c‖ ^ 2 = R ^ 2 + 1`). Which of the two happens is decided by whether the line passes through
the origin.

This is the two cases
`TauCeti.PoincareDisc.range_coe_geodesicLine_eq_ball_inter_setOf` and
`TauCeti.PoincareDisc.exists_range_coe_geodesicLine_eq_ball_inter_sphere` put together; the
individual statements say which case occurs and, in the circular case, what the centre and radius
are. -/
theorem range_coe_geodesicLine_eq_ball_inter_or (a : PoincareDisc) (u : Circle) :
    (∃ v : ℂ, ‖v‖ = 1 ∧
        Set.range (fun t : ℝ => ((toUnitDisc (geodesicLine a u t) : Complex.UnitDisc) : ℂ))
          = ball 0 1 ∩ {z : ℂ | (v * z).im = 0}) ∨
      ∃ c : ℂ, ∃ R : ℝ, 0 < R ∧ ‖c‖ ^ 2 = R ^ 2 + 1 ∧
        Set.range (fun t : ℝ => ((toUnitDisc (geodesicLine a u t) : Complex.UnitDisc) : ℂ))
          = ball 0 1 ∩ sphere c R := by
  rcases eq_or_ne (conj (u : ℂ) * (toUnitDisc a : ℂ)).im 0 with hA | hA
  · exact Or.inl ⟨conj (u : ℂ), by rw [norm_conj, Circle.norm_coe],
      range_coe_geodesicLine_eq_ball_inter_setOf a u hA⟩
  · exact Or.inr (exists_range_coe_geodesicLine_eq_ball_inter_sphere a u hA)

/-- **The geodesics of the Poincaré disc are exactly its Euclidean diameters and the arcs of
Euclidean circles orthogonal to the unit circle.** Any isometric embedding `γ : ℝ → PoincareDisc`
— which by `TauCeti.PoincareDisc.existsUnique_eq_geodesicLine` is a
`TauCeti.PoincareDisc.geodesicLine`, with no hypothesis on where it starts — traces either the
intersection of the open unit disc with a Euclidean line through the origin, or its intersection
with a Euclidean circle satisfying the orthogonality relation `‖c‖ ^ 2 = R ^ 2 + 1`.

This is the classical picture of the Poincaré disc, and it is
`TauCeti.PoincareDisc.range_coe_geodesicLine_eq_ball_inter_or` freed of the parametrisation:
nothing here refers to `geodesicLine`, only to being a geodesic line. -/
theorem range_coe_eq_ball_inter_or_of_isometry {γ : ℝ → PoincareDisc} (hγ : Isometry γ) :
    (∃ v : ℂ, ‖v‖ = 1 ∧
        Set.range (fun t : ℝ => ((toUnitDisc (γ t) : Complex.UnitDisc) : ℂ))
          = ball 0 1 ∩ {z : ℂ | (v * z).im = 0}) ∨
      ∃ c : ℂ, ∃ R : ℝ, 0 < R ∧ ‖c‖ ^ 2 = R ^ 2 + 1 ∧
        Set.range (fun t : ℝ => ((toUnitDisc (γ t) : Complex.UnitDisc) : ℂ))
          = ball 0 1 ∩ sphere c R := by
  obtain ⟨u, hu, -⟩ := existsUnique_eq_geodesicLine hγ
  rw [hu]
  exact range_coe_geodesicLine_eq_ball_inter_or (γ 0) u

end PoincareDisc

end TauCeti
