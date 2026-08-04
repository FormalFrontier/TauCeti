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
gives the circle of centre `c = TauCeti.orthogonalCircleCenter u a` and radius
`R = TauCeti.orthogonalCircleRadius u a`, which satisfy `‖c‖ ^ 2 = R ^ 2 + 1`, the Pythagorean
relation saying that the tangent length from `c` to the unit circle is `R`. That relation, and
the positivity of the radius, come from the identity

`‖B‖ ^ 2 - 4 * A ^ 2 = ‖u‖ ^ 2 * (1 - ‖a‖ ^ 2) ^ 2`

(`TauCeti.normSq_sub_mul_conj_sq_sub_four_mul_sq_im`); reading it at `‖u‖ = 1`, together with
`‖a‖ < 1`, is where those two hypotheses enter. The degenerate case `A = 0` is exactly the case in
which the geodesic passes through the origin, and then the equation collapses to the Euclidean
diameter `Im (conj u * z) = 0`.

## Main results

* `TauCeti.PoincareDisc.mem_range_radialGeodesic_iff` — a point of the Poincaré disc lies on the
  radial geodesic in direction `u` exactly when `conj u * z` is real.
* `TauCeti.PoincareDisc.mem_range_geodesicLine_iff` — the equation of the geodesic line through
  `a` in direction `u`, and
  `TauCeti.PoincareDisc.toPoincare_zero_mem_range_geodesicLine_iff` — that equation at the origin,
  which is what makes `Im (conj u * a)` the geometric discriminator of the case split below.
* `TauCeti.orthogonalCircleCenter` and `TauCeti.orthogonalCircleRadius` — the centre and radius
  parameters read off by completing the square, which for `‖u‖ = 1`, `‖a‖ < 1` and
  `Im (conj u * a) ≠ 0` are the centre and radius of the Euclidean circle traced by a hyperbolic
  line missing the origin, together with `TauCeti.orthogonalCircleRadius_pos` and the
  orthogonality relation `TauCeti.norm_orthogonalCircleCenter_sq`.
* `TauCeti.PoincareDisc.range_coe_toUnitDisc_geodesicLine_eq_ball_inter_sphere` — a geodesic line
  missing the origin traces `ball 0 1 ∩ sphere c R` for that Euclidean circle, which is
  **orthogonal to the unit circle**, `‖c‖ ^ 2 = R ^ 2 + 1`, and the complementary case
  `TauCeti.PoincareDisc.range_coe_toUnitDisc_geodesicLine_eq_ball_inter_setOf_im` — a geodesic
  line through the origin traces the Euclidean diameter in its direction, of which
  `TauCeti.PoincareDisc.range_coe_toUnitDisc_radialGeodesic_eq` is the reading at the base
  point `0`.
* `TauCeti.PoincareDisc.range_coe_toUnitDisc_geodesicLine_eq_ball_inter_or` — the two cases
  together: every geodesic line of the Poincaré disc traces the intersection of the disc with a
  Euclidean line through the origin or with a Euclidean circle orthogonal to the unit circle.
* `TauCeti.PoincareDisc.range_coe_toUnitDisc_eq_ball_inter_or_of_isometry` — the same for an
  arbitrary isometric embedding of the real line, which is the parametrisation-free form of that
  description.

Everything here runs in one direction, from a geodesic to the Euclidean set it traces. The
converse — that every diameter of the disc and every arc `ball 0 1 ∩ sphere c R` with
`‖c‖ ^ 2 = R ^ 2 + 1` is traced by a geodesic — is not proved below, and only the diameters are
covered, by `TauCeti.PoincareDisc.range_coe_toUnitDisc_radialGeodesic_eq`, which is an equality of
sets and so runs both ways.

## Generality

In accordance with the generality bar of `ConformalMapping/README.md`, which fixes scalar `ℂ`
for layers L0--L6, everything is stated for the complex unit disc. The plane-geometry lemmas of
the first section ask nothing of `a` beyond `‖a‖ < 1` and nothing of `u` beyond `‖u‖ = 1` — and
several of them ask less: the discriminant identity is homogeneous in `u` and needs no hypothesis
at all, and the degenerate case needs only `‖a‖ ≠ 1`. They are stated for bare complex numbers so
that they can be reused off the `PoincareDisc` synonym.

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
same number `A`. For `A ≠ 0` an equation `A * ‖z‖ ^ 2 - Im (B * z) + C = 0` describes a circle,
and that circle is orthogonal to the unit circle exactly when `A = C`, so for `A ≠ 0` the geodesic
equation *is* the equation of such a circle (`TauCeti.setOf_im_eq_ball_inter_sphere`). For `A = 0`
it is not a circle equation at all: it is linear, and describes a Euclidean line through the
origin (`TauCeti.setOf_im_eq_ball_inter_setOf_im`). No hypothesis is needed for the rearrangement
itself: this is an identity of real numbers. -/
theorem im_conj_mul_sub_mul_one_sub_mul_conj (u a z : ℂ) :
    (conj u * (z - a) * (1 - a * conj z)).im
      = ((conj u - u * conj a ^ 2) * z).im - (conj u * a).im * (normSq z + 1) := by
  simp only [Complex.mul_im, Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.one_re,
    Complex.one_im, Complex.conj_re, Complex.conj_im, Complex.normSq_apply, pow_two]
  ring

/-- **The discriminant identity behind the radius.** The linear coefficient `B` and the quadratic
coefficient `A` of the geodesic equation (`TauCeti.im_conj_mul_sub_mul_one_sub_mul_conj`) satisfy
`‖B‖ ^ 2 - 4 * A ^ 2 = ‖u‖ ^ 2 * (1 - ‖a‖ ^ 2) ^ 2`. Both sides are homogeneous of degree two in
`u`, so no normalisation of `u` is needed; at `‖u‖ = 1` the right-hand side is `(1 - ‖a‖ ^ 2) ^ 2`.

Completing the square turns the geodesic equation into `‖z - c‖ ^ 2 = ‖c‖ ^ 2 - 1` with
`‖c‖ ^ 2 = ‖B‖ ^ 2 / (4 * A ^ 2)`, so this identity is what makes the radius
`(1 - ‖a‖ ^ 2) / (2 * |A|)` positive when `‖u‖ = 1` and `‖a‖ < 1`: the circle is a genuine circle
and not a point or the empty set. -/
theorem normSq_sub_mul_conj_sq_sub_four_mul_sq_im (u a : ℂ) :
    normSq (conj u - u * conj a ^ 2) - 4 * (conj u * a).im ^ 2
      = normSq u * (1 - normSq a) ^ 2 := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.conj_re, Complex.conj_im, pow_two]
  ring

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

/-! ### The centre and radius of the orthogonal circle -/

/-- The centre parameter `c = I * conj B / (2 * A)`, with `A = Im (conj u * a)` and
`B = conj u - u * conj a ^ 2`, read off by completing the square in the geodesic equation
`Im (B * z) = A * (‖z‖ ^ 2 + 1)` of `TauCeti.im_conj_mul_sub_mul_one_sub_mul_conj`.

Nothing is asked of `u` or `a` here, so on its own this is an algebraic parameter: at `A = 0` the
division is by zero and the value is `0`, and `A ≠ 0` alone does not make it the centre of a
genuine circle, since the companion radius `TauCeti.orthogonalCircleRadius u a` vanishes at
`‖a‖ = 1` and is negative beyond. It is the centre of the Euclidean circle traced by the
hyperbolic line through `a` in direction `u` under the hypotheses `‖u‖ = 1`, `‖a‖ < 1` and
`A ≠ 0` of `TauCeti.setOf_im_eq_ball_inter_sphere`, the last of which says that that line misses
the origin. -/
noncomputable def orthogonalCircleCenter (u a : ℂ) : ℂ :=
  I * conj (conj u - u * conj a ^ 2) / ((2 * (conj u * a).im : ℝ) : ℂ)

/-- The quantity `R = (1 - ‖a‖ ^ 2) / (2 * |A|)`, with `A = Im (conj u * a)`, read off by
completing the square as in `TauCeti.orthogonalCircleCenter`.

Nothing is asked of `u` or `a` here, so this is a signed algebraic parameter: at `A = 0` the
division is by zero and the value is `0`, and for `A ≠ 0` it is negative for `‖a‖ > 1` (at
`u = 1` and `a = 2 * I` it is `-3/4`). Under `‖a‖ < 1` and `A ≠ 0` it is positive
(`TauCeti.orthogonalCircleRadius_pos`), but it is the radius of the Euclidean circle traced by the
hyperbolic line through `a` in direction `u` only once `‖u‖ = 1` as well
(`TauCeti.setOf_im_eq_ball_inter_sphere`): unlike the centre, `R` is not invariant under
rescaling `u`, because `A` scales with `u` while the numerator does not. -/
noncomputable def orthogonalCircleRadius (u a : ℂ) : ℝ :=
  (1 - ‖a‖ ^ 2) / (2 * |(conj u * a).im|)

/-- The defining formula for `TauCeti.orthogonalCircleCenter`, so that the advertised expression
is available without unfolding the definition. -/
lemma orthogonalCircleCenter_def (u a : ℂ) :
    orthogonalCircleCenter u a
      = I * conj (conj u - u * conj a ^ 2) / ((2 * (conj u * a).im : ℝ) : ℂ) := by
  rw [orthogonalCircleCenter]

/-- The defining formula for `TauCeti.orthogonalCircleRadius`, so that the advertised expression
is available without unfolding the definition. -/
lemma orthogonalCircleRadius_def (u a : ℂ) :
    orthogonalCircleRadius u a = (1 - ‖a‖ ^ 2) / (2 * |(conj u * a).im|) := by
  rw [orthogonalCircleRadius]

/-- **The radius parameter is positive on the disc, away from the origin.** `‖a‖ < 1` makes the
numerator positive and `Im (conj u * a) ≠ 0` makes the denominator positive; no unit direction is
needed for that. At `‖u‖ = 1` the second hypothesis says that the hyperbolic line through `a` in
direction `u` misses the origin, and positivity is then what makes the Euclidean set that line
traces a genuine circle rather than a point or the empty set
(`TauCeti.setOf_im_eq_ball_inter_sphere`). -/
lemma orthogonalCircleRadius_pos {u a : ℂ} (ha : ‖a‖ < 1) (hA : (conj u * a).im ≠ 0) :
    0 < orthogonalCircleRadius u a := by
  rw [orthogonalCircleRadius_def]
  have hnum : 0 < 1 - ‖a‖ ^ 2 := by nlinarith [norm_nonneg a]
  have hden : 0 < |(conj u * a).im| := abs_pos.mpr hA
  exact div_pos hnum (by linarith)

/-- **The circle of a hyperbolic line is orthogonal to the unit circle.** The centre
`c = TauCeti.orthogonalCircleCenter u a` and the parameter `R = TauCeti.orthogonalCircleRadius u a`
satisfy `‖c‖ ^ 2 = R ^ 2 + 1`. This is
`TauCeti.normSq_sub_mul_conj_sq_sub_four_mul_sq_im` at `‖u‖ = 1`, and as an identity it needs no
bound on `‖a‖`.

Once `‖a‖ < 1` makes `R` positive (`TauCeti.orthogonalCircleRadius_pos`), so that the circle of
centre `c` and radius `R` is a genuine circle, the relation is Pythagoras for the right triangle
whose legs are the radius `1` of the unit circle and the radius `R`, and it then says precisely
that the two circles meet at right angles. -/
lemma norm_orthogonalCircleCenter_sq {u a : ℂ} (hu : ‖u‖ = 1) (hA : (conj u * a).im ≠ 0) :
    ‖orthogonalCircleCenter u a‖ ^ 2 = orthogonalCircleRadius u a ^ 2 + 1 := by
  have hnu : normSq u = 1 := by rw [Complex.normSq_eq_norm_sq, hu]; norm_num
  have hkey := normSq_sub_mul_conj_sq_sub_four_mul_sq_im u a
  rw [hnu, one_mul] at hkey
  have hR : orthogonalCircleRadius u a = (1 - normSq a) / (2 * |(conj u * a).im|) := by
    rw [orthogonalCircleRadius_def, Complex.normSq_eq_norm_sq]
  have h4 : (0 : ℝ) < 4 * (conj u * a).im ^ 2 := by positivity
  rw [orthogonalCircleCenter_def, hR, ← Complex.normSq_eq_norm_sq, Complex.normSq_div,
    Complex.normSq_mul, Complex.normSq_I, Complex.normSq_conj, Complex.normSq_ofReal, div_pow,
    mul_pow, sq_abs]
  field_simp
  linarith [hkey]

/-- **A hyperbolic line off the origin is an arc of a Euclidean circle orthogonal to the unit
circle.** If `‖u‖ = 1`, `‖a‖ < 1` and the geodesic through `a` in direction `u` misses the origin
— which is exactly `Im (conj u * a) ≠ 0` — then its plane equation cuts out
`ball 0 1 ∩ sphere c R` for the centre `c = TauCeti.orthogonalCircleCenter u a` and the radius
`R = TauCeti.orthogonalCircleRadius u a`.

That this is a genuine circle, and that it meets the unit circle at right angles, are
`TauCeti.orthogonalCircleRadius_pos` and `TauCeti.norm_orthogonalCircleCenter_sq`. -/
theorem setOf_im_eq_ball_inter_sphere {u a : ℂ} (hu : ‖u‖ = 1) (ha : ‖a‖ < 1)
    (hA : (conj u * a).im ≠ 0) :
    {z : ℂ | ‖z‖ < 1 ∧ (conj u * (z - a) * (1 - a * conj z)).im = 0}
      = ball 0 1 ∩ sphere (orthogonalCircleCenter u a) (orthogonalCircleRadius u a) := by
  have hRpos : 0 < orthogonalCircleRadius u a := orthogonalCircleRadius_pos ha hA
  have hnc : normSq (orthogonalCircleCenter u a) = orthogonalCircleRadius u a ^ 2 + 1 := by
    rw [Complex.normSq_eq_norm_sq]
    exact norm_orthogonalCircleCenter_sq hu hA
  have hconjc : conj (orthogonalCircleCenter u a)
      = -I * (conj u - u * conj a ^ 2) / ((2 * (conj u * a).im : ℝ) : ℂ) := by
    rw [orthogonalCircleCenter_def, map_div₀, map_mul, Complex.conj_I, Complex.conj_conj,
      Complex.conj_ofReal]
  ext z
  have hid := mul_normSq_sub_sub_sq hA hconjc hnc z
  have hlink : (conj u * a).im *
      (normSq (z - orthogonalCircleCenter u a) - orthogonalCircleRadius u a ^ 2)
        = -(conj u * (z - a) * (1 - a * conj z)).im := by
    rw [im_conj_mul_sub_mul_one_sub_mul_conj u a z, hid]
    ring
  simp only [Set.mem_ofPred_eq, mem_inter_iff, mem_ball_zero_iff, mem_sphere_iff_norm]
  refine and_congr_right fun _ => ?_
  constructor
  · intro him
    have hzero :
        normSq (z - orthogonalCircleCenter u a) - orthogonalCircleRadius u a ^ 2 = 0 := by
      rw [him, neg_zero] at hlink
      exact (mul_eq_zero.mp hlink).resolve_left hA
    have hsq : ‖z - orthogonalCircleCenter u a‖ ^ 2 = orthogonalCircleRadius u a ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq]
      linarith
    have := congrArg Real.sqrt hsq
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hRpos.le] at this
  · intro hdist
    have hsq : normSq (z - orthogonalCircleCenter u a) = orthogonalCircleRadius u a ^ 2 := by
      rw [Complex.normSq_eq_norm_sq, hdist]
    rw [hsq, sub_self, mul_zero] at hlink
    linarith [hlink]

/-- **A hyperbolic line through the origin is a Euclidean diameter.** As an equality of sets: if
`Im (conj u * a) = 0` — the case excluded in `TauCeti.setOf_im_eq_ball_inter_sphere` — then the
equation cutting out the line through `a` in direction `u` collapses to the reality of
`conj u * z`. The two equations differ by the scalar factor `1 - ‖a‖ ^ 2`, so of `a` only
`‖a‖ ≠ 1` is asked, and of `u` nothing at all.

The geometric reading needs `u ≠ 0`, which holds for the unit direction `u` of a geodesic: then
the hypothesis says that `a` is a real multiple of `u`, so that the geodesic through `a` in
direction `u` is the one through the origin, and the right-hand side is the Euclidean diameter in
direction `u`. -/
theorem setOf_im_eq_ball_inter_setOf_im {u a : ℂ} (ha : ‖a‖ ≠ 1) (hA : (conj u * a).im = 0) :
    {z : ℂ | ‖z‖ < 1 ∧ (conj u * (z - a) * (1 - a * conj z)).im = 0}
      = ball 0 1 ∩ {z : ℂ | (conj u * z).im = 0} := by
  have hna : (1 : ℝ) - normSq a ≠ 0 := by
    rw [sub_ne_zero, Complex.normSq_eq_norm_sq]
    intro h
    rcases mul_eq_zero.mp (by linear_combination -h : (‖a‖ - 1) * (‖a‖ + 1) = 0) with h1 | h1
    · exact ha (by linarith)
    · linarith [norm_nonneg a]
  -- `conj u * a` is real, so it is its own conjugate `u * conj a`.
  have hsymm : u * conj a = conj u * a := by
    simpa only [map_mul, Complex.conj_conj] using Complex.conj_eq_iff_im.mpr hA
  have hB : conj u - u * conj a ^ 2 = conj u * ((1 - normSq a : ℝ) : ℂ) := by
    have hexp : u * conj a ^ 2 = conj u * (a * conj a) := by
      rw [sq, ← mul_assoc, hsymm, mul_assoc]
    rw [hexp, Complex.mul_conj]
    push_cast
    ring
  ext z
  simp only [Set.mem_ofPred_eq, mem_inter_iff, mem_ball_zero_iff]
  refine and_congr_right fun _ => ?_
  rw [im_conj_mul_sub_mul_one_sub_mul_conj, hA, zero_mul, sub_zero, hB]
  have hmul : conj u * ((1 - normSq a : ℝ) : ℂ) * z
      = ((1 - normSq a : ℝ) : ℂ) * (conj u * z) := by ring
  rw [hmul, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
    mul_eq_zero]
  constructor
  · rintro (h | h)
    · exact absurd h hna
    · exact h
  · exact fun h => Or.inr h

/-! ## The geodesics of the Poincaré disc -/

namespace PoincareDisc

/-- The imaginary part of a quotient vanishes exactly when it does after clearing the
denominator. -/
private lemma im_div_eq_zero_iff {w v : ℂ} (hv : v ≠ 0) :
    (w / v).im = 0 ↔ (w * conj v).im = 0 := by
  have hnv : normSq v ≠ 0 := fun h => hv (Complex.normSq_eq_zero.mp h)
  have h : (w / v).im = (w * conj v).im / normSq v := by
    rw [Complex.div_im, Complex.mul_im, Complex.conj_re, Complex.conj_im]
    ring
  rw [h, div_eq_zero_iff]
  simp [hnv]

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
    obtain ⟨t, -, ht⟩ := Real.tanh_surjOn (Set.mem_Ioo.mpr (abs_lt.mp hs1))
    refine ⟨t, toUnitDisc.injective (Complex.UnitDisc.coe_injective ?_)⟩
    rw [coe_radialGeodesic, ht, hzu]

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
  have hne : 1 - conj (toUnitDisc a : ℂ) * (toUnitDisc z : ℂ) ≠ 0 :=
    one_sub_conj_mul_ne_zero_unitDisc (toUnitDisc z) (toUnitDisc a)
  have hconj : conj (1 - conj (toUnitDisc a : ℂ) * (toUnitDisc z : ℂ))
      = 1 - (toUnitDisc a : ℂ) * conj (toUnitDisc z : ℂ) := by
    rw [map_sub, map_one, map_mul, Complex.conj_conj]
  rw [hmem, mem_range_radialGeodesic_iff, unitDiscMoebiusIsometryEquiv_apply,
    toUnitDisc_toPoincare, coe_unitDiscMoebius, ← mul_div_assoc, im_div_eq_zero_iff hne, hconj]

/-- **The geodesic line through `a` in direction `u` passes through the origin exactly when
`Im (conj u * a) = 0`.** This is `TauCeti.PoincareDisc.mem_range_geodesicLine_iff` read at the
origin, and it is what makes `Im (conj u * a)` the geometric discriminator of the case split
below: the vanishing of that number is not an algebraic accident but says that the geodesic
contains the origin, which is exactly when it traces a Euclidean diameter rather than an arc of a
circle. -/
theorem toPoincare_zero_mem_range_geodesicLine_iff (a : PoincareDisc) (u : Circle) :
    Complex.UnitDisc.toPoincare 0 ∈ Set.range (geodesicLine a u) ↔
      (conj (u : ℂ) * (toUnitDisc a : ℂ)).im = 0 := by
  rw [mem_range_geodesicLine_iff, toUnitDisc_toPoincare, Complex.UnitDisc.coe_zero, zero_sub,
    map_zero, mul_zero, sub_zero, mul_one, mul_neg, Complex.neg_im, neg_eq_zero]

/-- The plane description of the geodesic line through `a` in direction `u`: it traces the set of
points of the open unit disc satisfying the geodesic equation. -/
theorem range_coe_toUnitDisc_geodesicLine_eq (a : PoincareDisc) (u : Circle) :
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
    exact ⟨t, by simp [ht]⟩

/-- **A geodesic line missing the origin traces an arc of a Euclidean circle orthogonal to the
unit circle.** If `Im (conj u * a) ≠ 0` — which by
`TauCeti.PoincareDisc.toPoincare_zero_mem_range_geodesicLine_iff` says that the line misses the
origin — the geodesic line of the Poincaré disc through `a` in direction `u` sweeps out
`ball 0 1 ∩ sphere c R` for the Euclidean circle of centre
`TauCeti.orthogonalCircleCenter` and radius `TauCeti.orthogonalCircleRadius`, whose radius is
positive (`TauCeti.orthogonalCircleRadius_pos`) and which satisfies `‖c‖ ^ 2 = R ^ 2 + 1`
(`TauCeti.norm_orthogonalCircleCenter_sq`), the Pythagorean relation expressing that it meets the
unit circle at right angles.

This is the classical picture of the Poincaré disc, and it is
`TauCeti.setOf_im_eq_ball_inter_sphere` read through
`TauCeti.PoincareDisc.range_coe_toUnitDisc_geodesicLine_eq`. -/
theorem range_coe_toUnitDisc_geodesicLine_eq_ball_inter_sphere (a : PoincareDisc) (u : Circle)
    (hA : (conj (u : ℂ) * (toUnitDisc a : ℂ)).im ≠ 0) :
    Set.range (fun t : ℝ => ((toUnitDisc (geodesicLine a u t) : Complex.UnitDisc) : ℂ))
      = ball 0 1 ∩ sphere (orthogonalCircleCenter (u : ℂ) (toUnitDisc a : ℂ))
          (orthogonalCircleRadius (u : ℂ) (toUnitDisc a : ℂ)) := by
  rw [range_coe_toUnitDisc_geodesicLine_eq,
    setOf_im_eq_ball_inter_sphere (Circle.norm_coe u) (toUnitDisc a).norm_lt_one hA]

/-- **A geodesic line through the origin traces a Euclidean diameter.** The complementary case of
`TauCeti.PoincareDisc.range_coe_toUnitDisc_geodesicLine_eq_ball_inter_sphere`: when
`Im (conj u * a) = 0` — which by
`TauCeti.PoincareDisc.toPoincare_zero_mem_range_geodesicLine_iff` says that the line passes
through the origin — the base point `a` is a real multiple of the direction `u`, so the geodesic
line through `a` is the radial one and traces the Euclidean diameter in direction `u`. -/
theorem range_coe_toUnitDisc_geodesicLine_eq_ball_inter_setOf_im (a : PoincareDisc) (u : Circle)
    (hA : (conj (u : ℂ) * (toUnitDisc a : ℂ)).im = 0) :
    Set.range (fun t : ℝ => ((toUnitDisc (geodesicLine a u t) : Complex.UnitDisc) : ℂ))
      = ball 0 1 ∩ {z : ℂ | (conj (u : ℂ) * z).im = 0} := by
  rw [range_coe_toUnitDisc_geodesicLine_eq,
    setOf_im_eq_ball_inter_setOf_im (toUnitDisc a).norm_lt_one.ne hA]

/-- **A geodesic through the origin traces a Euclidean diameter.** The radial geodesic in
direction `u` sweeps out exactly the intersection of the open unit disc with the Euclidean line
through the origin in direction `u`.

This is `TauCeti.PoincareDisc.range_coe_toUnitDisc_geodesicLine_eq_ball_inter_setOf_im` at the
base point `0`, where the geodesic line is the radial one
(`TauCeti.PoincareDisc.geodesicLine_toPoincare_zero`). -/
theorem range_coe_toUnitDisc_radialGeodesic_eq (u : Circle) :
    Set.range (fun t : ℝ => ((toUnitDisc (radialGeodesic u t) : Complex.UnitDisc) : ℂ))
      = ball 0 1 ∩ {z : ℂ | (conj (u : ℂ) * z).im = 0} := by
  rw [← geodesicLine_toPoincare_zero u]
  exact range_coe_toUnitDisc_geodesicLine_eq_ball_inter_setOf_im _ u (by simp)

/-- **The geodesics of the Poincaré disc, in Euclidean terms.** Every geodesic line of the
Poincaré disc traces either the intersection of the open unit disc with a Euclidean line through
the origin, or its intersection with a Euclidean circle orthogonal to the unit circle
(`‖c‖ ^ 2 = R ^ 2 + 1`). Which of the two happens is decided by whether the line passes through
the origin, that being the content of
`TauCeti.PoincareDisc.toPoincare_zero_mem_range_geodesicLine_iff` for the discriminator
`Im (conj u * a)` of the case split.

This is the two cases
`TauCeti.PoincareDisc.range_coe_toUnitDisc_geodesicLine_eq_ball_inter_setOf_im` and
`TauCeti.PoincareDisc.range_coe_toUnitDisc_geodesicLine_eq_ball_inter_sphere` put together; the
individual statements say which case occurs and, in the circular case, what the centre and radius
are. As there, the implication runs from the geodesic to the Euclidean set it traces, and not
back. -/
theorem range_coe_toUnitDisc_geodesicLine_eq_ball_inter_or (a : PoincareDisc) (u : Circle) :
    (∃ v : ℂ, ‖v‖ = 1 ∧
        Set.range (fun t : ℝ => ((toUnitDisc (geodesicLine a u t) : Complex.UnitDisc) : ℂ))
          = ball 0 1 ∩ {z : ℂ | (v * z).im = 0}) ∨
      ∃ c : ℂ, ∃ R : ℝ, 0 < R ∧ ‖c‖ ^ 2 = R ^ 2 + 1 ∧
        Set.range (fun t : ℝ => ((toUnitDisc (geodesicLine a u t) : Complex.UnitDisc) : ℂ))
          = ball 0 1 ∩ sphere c R := by
  rcases eq_or_ne (conj (u : ℂ) * (toUnitDisc a : ℂ)).im 0 with hA | hA
  · exact Or.inl ⟨conj (u : ℂ), by rw [norm_conj, Circle.norm_coe],
      range_coe_toUnitDisc_geodesicLine_eq_ball_inter_setOf_im a u hA⟩
  · exact Or.inr ⟨_, _, orthogonalCircleRadius_pos (toUnitDisc a).norm_lt_one hA,
      norm_orthogonalCircleCenter_sq (Circle.norm_coe u) hA,
      range_coe_toUnitDisc_geodesicLine_eq_ball_inter_sphere a u hA⟩

/-- **Every geodesic of the Poincaré disc is a Euclidean diameter or an arc of a Euclidean circle
orthogonal to the unit circle.** Any isometric embedding `γ : ℝ → PoincareDisc` — which by
`TauCeti.PoincareDisc.existsUnique_eq_geodesicLine` is a `TauCeti.PoincareDisc.geodesicLine`, with
no hypothesis on where it starts — traces either the intersection of the open unit disc with a
Euclidean line through the origin, or its intersection with a Euclidean circle satisfying the
orthogonality relation `‖c‖ ^ 2 = R ^ 2 + 1`.

This is the classical picture of the Poincaré disc, and it is
`TauCeti.PoincareDisc.range_coe_toUnitDisc_geodesicLine_eq_ball_inter_or` freed of the
parametrisation: nothing here refers to `geodesicLine`, only to being a geodesic line. It runs in
one direction only, from a geodesic to the Euclidean set it traces; that every such diameter or
orthogonal circular arc is in turn traced by a geodesic is not claimed here. -/
theorem range_coe_toUnitDisc_eq_ball_inter_or_of_isometry {γ : ℝ → PoincareDisc}
    (hγ : Isometry γ) :
    (∃ v : ℂ, ‖v‖ = 1 ∧
        Set.range (fun t : ℝ => ((toUnitDisc (γ t) : Complex.UnitDisc) : ℂ))
          = ball 0 1 ∩ {z : ℂ | (v * z).im = 0}) ∨
      ∃ c : ℂ, ∃ R : ℝ, 0 < R ∧ ‖c‖ ^ 2 = R ^ 2 + 1 ∧
        Set.range (fun t : ℝ => ((toUnitDisc (γ t) : Complex.UnitDisc) : ℂ))
          = ball 0 1 ∩ sphere c R := by
  obtain ⟨u, hu, -⟩ := existsUnique_eq_geodesicLine hγ
  rw [hu]
  exact range_coe_toUnitDisc_geodesicLine_eq_ball_inter_or (γ 0) u

end PoincareDisc

end TauCeti
