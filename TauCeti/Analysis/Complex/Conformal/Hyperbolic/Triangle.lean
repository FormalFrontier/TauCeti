/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.Hyperbolic.Distance
public import TauCeti.Analysis.Complex.Conformal.Moebius
public import TauCeti.Analysis.SpecialFunctions.Artanh

/-!
# The triangle inequality for the hyperbolic distance on the unit disc

This file proves the **triangle inequality** for the hyperbolic (Poincaré) distance
`hyperbolicDist` on the complex open unit disc, the metric-completeness step deferred in
`HyperbolicDistance.lean`.

The core analytic input is the *strong* triangle-type inequality for the pseudo-hyperbolic
expression `pseudoHyperbolicExpr z w = ‖(z - w) / (1 - conj w * z)‖`, taken here in its
origin-centred form
`pseudoHyperbolicExpr z w ≤ (‖z‖ + ‖w‖) / (1 + ‖z‖ * ‖w‖)`
(`pseudoHyperbolicExpr_le_add_div_one_add_mul_of_norm_lt_one`). Squaring, this rests on the
factorisation
`((‖z‖ + ‖w‖) ‖1 - conj w z‖) ^ 2 - (‖z - w‖ (1 + ‖z‖ ‖w‖)) ^ 2`
`  = 2 (1 - ‖z‖ ^ 2)(1 - ‖w‖ ^ 2)(‖z‖ ‖w‖ + (z conj w).re)`,
each factor of which is nonnegative on the disc.

The same factorisation, read as an equation rather than as a sign, says *when* the inequality is
tight: the first two factors are strictly positive on the disc, so equality holds exactly when
`(z * conj w).re = -(‖z‖ * ‖w‖)`, that is exactly when `z` and `w` point in opposite directions.
Flipping the sign of the difference `‖z‖ - ‖w‖` throughout gives the mirror statements — the
*reverse* triangle inequality `|‖z‖ - ‖w‖| / (1 - ‖z‖ * ‖w‖) ≤ pseudoHyperbolicExpr z w` and its
own equality case `(z * conj w).re = ‖z‖ * ‖w‖`, that is `z` and `w` pointing in the same
direction. These two equality cases are what identify the degenerate hyperbolic triangles, and
hence the hyperbolic geodesics, in `Conformal/Poincare/Betweenness.lean`.

Passing to the hyperbolic distance `hyperbolicDist = artanh ∘ pseudoHyperbolicExpr` uses the
addition formula for the inverse hyperbolic tangent,
`Real.artanh a + Real.artanh b = Real.artanh ((a + b) / (1 + a * b))` (`Real.artanh_add`, proved
in `TauCeti/Analysis/SpecialFunctions/Artanh.lean`), together with the isometry invariance of
`hyperbolicDist` under the disc Moebius factors (`hyperbolicDist_unitDiscMoebius`): the general
triangle inequality is reduced to the origin case by sending the middle point to `0`.

Main results:

* `pseudoHyperbolicExpr_le_add_div_one_add_mul_of_norm_lt_one` — the strong pseudo-hyperbolic
  triangle inequality against the origin, and
  `pseudoHyperbolicExpr_eq_add_div_one_add_mul_iff_of_norm_lt_one` — its equality case;
* `abs_sub_div_one_sub_mul_le_pseudoHyperbolicExpr_of_norm_lt_one` — the reverse
  pseudo-hyperbolic triangle inequality against the origin, and
  `pseudoHyperbolicExpr_eq_abs_sub_div_one_sub_mul_iff_of_norm_lt_one` — its equality case;
* `hyperbolicDist_triangle_zero` — the hyperbolic triangle inequality with the origin as the
  middle point;
* `hyperbolicDist_triangle` / `hyperbolicDist_triangle_unitDisc` — the full hyperbolic triangle
  inequality `hyperbolicDist z w ≤ hyperbolicDist z u + hyperbolicDist u w`, in ball and
  bundled `Complex.UnitDisc` form;
* `pseudoHyperbolicExpr_le_add_div_one_add_mul` and
  `abs_sub_div_one_sub_mul_le_pseudoHyperbolicExpr` — the same two pseudo-hyperbolic inequalities
  with an *arbitrary* middle point `u` in place of the origin, with their equality cases
  `pseudoHyperbolicExpr_eq_add_div_one_add_mul_iff` and
  `pseudoHyperbolicExpr_eq_abs_sub_div_one_sub_mul_iff`;
* `pseudoHyperbolicExpr_triangle` — the plain triangle inequality
  `pseudoHyperbolicExpr z w ≤ pseudoHyperbolicExpr z u + pseudoHyperbolicExpr u w`, so that the
  pseudo-hyperbolic expression is itself a metric on the disc and not merely a
  monotone reparametrisation of one.

Each of those five carries a hypothesis-free `Complex.UnitDisc` form, named by the suffix
`_unitDisc`.

Together with the symmetry, nonnegativity and vanishing-on-the-diagonal lemmas already in
`HyperbolicDistance.lean`, these give the metric-space axioms for `hyperbolicDist` on the open
unit disc. A `MetricSpace` *instance* is deliberately not registered on `Complex.UnitDisc`,
which already carries the Euclidean subspace metric; recording the Poincaré metric as an
instance would require a dedicated type synonym and is left to future work.

The origin plays no role in the pseudo-hyperbolic statements: the whole point of
`pseudoHyperbolicExpr` is that it is invariant under the disc Moebius factors
(`pseudoHyperbolicExpr_unitDiscMoebiusFormula_of_norm_lt_one`), which act transitively. The
last group of results above therefore removes it, and does so without repeating the transport
argument: since `hyperbolicDist = artanh ∘ pseudoHyperbolicExpr` and `artanh` is a strictly
monotone bijection `(-1, 1) ≃ ℝ`, an inequality between pseudo-hyperbolic expressions is
*equivalent* to the corresponding inequality between hyperbolic distances, and the addition
formula `Real.artanh_add` is exactly the dictionary translating the additive law
`d(z, u) + d(u, w)` into the Moebius law `(a + b) / (1 + a b)`. So the general forms are read
off `hyperbolicDist_triangle` — which is where the transport already happened — and their
equality cases off the injectivity of `artanh`.

This advances the conformal-mapping roadmap's L2 target "the hyperbolic / Poincaré metric on
`𝔻`" (see `ConformalMapping/README.md`). It reuses Tau Ceti's pseudo-hyperbolic, Moebius and
Schwarz--Pick API. As with the rest of the L0--L3 conformal-mapping material, it is
coordinated with the upstream Mathlib RMT effort leanprover-community/mathlib4#33505 and should
be refactored to upstream API if that work lands a human-curated Poincaré metric.
-/

public section

namespace TauCeti

open _root_.Complex Metric Set
open scoped ComplexConjugate

/-- **Poincaré defect identity.** The factorisation behind the strong pseudo-hyperbolic triangle
inequality against the origin: the difference of the squared cross-multiplied sides of
`pseudoHyperbolicExpr z w ≤ (‖z‖ + ‖w‖) / (1 + ‖z‖ * ‖w‖)` is
`2 (1 - ‖z‖ ^ 2)(1 - ‖w‖ ^ 2)(‖z‖ ‖w‖ + (z conj w).re)`.

Kept private: it is a bookkeeping step shared by that inequality and its equality case, and only
the two named consequences below are meant to be used. -/
private lemma sq_sub_sq_triangle (z w : ℂ) :
    ((‖z‖ + ‖w‖) * ‖1 - (starRingEnd ℂ) w * z‖) ^ 2
      - (‖z - w‖ * (1 + ‖z‖ * ‖w‖)) ^ 2
      = 2 * ((1 - ‖z‖ ^ 2) * (1 - ‖w‖ ^ 2) *
          (‖z‖ * ‖w‖ + (z * (starRingEnd ℂ) w).re)) := by
  have hN2 : ‖z - w‖ ^ 2 = ‖z‖ ^ 2 + ‖w‖ ^ 2 - 2 * (z * (starRingEnd ℂ) w).re := by
    simpa [Complex.normSq_eq_norm_sq] using Complex.normSq_sub z w
  have hD2 : ‖1 - (starRingEnd ℂ) w * z‖ ^ 2
      = 1 - 2 * (z * (starRingEnd ℂ) w).re + ‖z‖ ^ 2 * ‖w‖ ^ 2 := by
    linear_combination norm_sq_one_sub_conj_mul_sub_norm_sq_sub z w + hN2
  rw [mul_pow, mul_pow, hD2, hN2]; ring

/-- **Strong pseudo-hyperbolic triangle inequality (origin form).** For two points of the open
unit disc, `pseudoHyperbolicExpr z w ≤ (‖z‖ + ‖w‖) / (1 + ‖z‖ * ‖w‖)`. This is the
`ρ(z, w) ≤ (ρ(z, 0) + ρ(0, w)) / (1 + ρ(z, 0) ρ(0, w))` form of the pseudo-hyperbolic triangle
inequality. -/
theorem pseudoHyperbolicExpr_le_add_div_one_add_mul_of_norm_lt_one {z w : ℂ}
    (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) :
    pseudoHyperbolicExpr z w ≤ (‖z‖ + ‖w‖) / (1 + ‖z‖ * ‖w‖) := by
  have hDpos : 0 < ‖1 - (starRingEnd ℂ) w * z‖ :=
    norm_pos_iff.mpr (one_sub_conj_mul_ne_zero_of_norm_lt_one hz hw)
  have hABpos : (0 : ℝ) < 1 + ‖z‖ * ‖w‖ := by positivity
  have hdiff := sq_sub_sq_triangle z w
  have htabs : |(z * (starRingEnd ℂ) w).re| ≤ ‖z‖ * ‖w‖ := by
    have h := Complex.abs_re_le_norm (z * (starRingEnd ℂ) w)
    rwa [norm_mul, Complex.norm_conj] at h
  have hfacarg : 0 ≤ ‖z‖ * ‖w‖ + (z * (starRingEnd ℂ) w).re := by
    have := (abs_le.mp htabs).1
    linarith
  have h1A : 0 ≤ 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have h1B : 0 ≤ 1 - ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]
  have hfac : 0 ≤ (1 - ‖z‖ ^ 2) * (1 - ‖w‖ ^ 2) *
      (‖z‖ * ‖w‖ + (z * (starRingEnd ℂ) w).re) :=
    mul_nonneg (mul_nonneg h1A h1B) hfacarg
  have hsq : (‖z - w‖ * (1 + ‖z‖ * ‖w‖)) ^ 2
      ≤ ((‖z‖ + ‖w‖) * ‖1 - (starRingEnd ℂ) w * z‖) ^ 2 := by
    linarith [hfac, hdiff]
  have hLnn : 0 ≤ ‖z - w‖ * (1 + ‖z‖ * ‖w‖) := by positivity
  have hRnn : 0 ≤ (‖z‖ + ‖w‖) * ‖1 - (starRingEnd ℂ) w * z‖ := by positivity
  have hcore : ‖z - w‖ * (1 + ‖z‖ * ‖w‖)
      ≤ (‖z‖ + ‖w‖) * ‖1 - (starRingEnd ℂ) w * z‖ := by
    have h := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq hLnn, Real.sqrt_sq hRnn] at h
  rw [pseudoHyperbolicExpr_def, norm_div, div_le_div_iff₀ hDpos hABpos]
  exact hcore

/-- **Poincaré defect identity, reverse form.** The mirror of `sq_sub_sq_triangle`, obtained from
it by replacing the sum `‖z‖ + ‖w‖` by the difference `|‖z‖ - ‖w‖|` and the denominator
`1 + ‖z‖ * ‖w‖` by
`1 - ‖z‖ * ‖w‖`; the effect on the right-hand side is to flip the sign of `(z * conj w).re`.

Kept private: it is a bookkeeping step shared by the reverse inequality and its equality case, and
only the two named consequences below are meant to be used. -/
private lemma sq_sub_sq_reverse_triangle (z w : ℂ) :
    (‖z - w‖ * (1 - ‖z‖ * ‖w‖)) ^ 2
      - (|‖z‖ - ‖w‖| * ‖1 - (starRingEnd ℂ) w * z‖) ^ 2
      = 2 * ((1 - ‖z‖ ^ 2) * (1 - ‖w‖ ^ 2) *
          (‖z‖ * ‖w‖ - (z * (starRingEnd ℂ) w).re)) := by
  have hN2 : ‖z - w‖ ^ 2 = ‖z‖ ^ 2 + ‖w‖ ^ 2 - 2 * (z * (starRingEnd ℂ) w).re := by
    simpa [Complex.normSq_eq_norm_sq] using Complex.normSq_sub z w
  have hD2 : ‖1 - (starRingEnd ℂ) w * z‖ ^ 2
      = 1 - 2 * (z * (starRingEnd ℂ) w).re + ‖z‖ ^ 2 * ‖w‖ ^ 2 := by
    linear_combination norm_sq_one_sub_conj_mul_sub_norm_sq_sub z w + hN2
  rw [mul_pow, mul_pow, sq_abs, hD2, hN2]; ring

/-- **Equality in the strong pseudo-hyperbolic triangle inequality against the origin.** For two
points of the open unit disc, `pseudoHyperbolicExpr z w = (‖z‖ + ‖w‖) / (1 + ‖z‖ * ‖w‖)` holds
exactly when `(z * conj w).re = -(‖z‖ * ‖w‖)`, that is (by the equality case of
`Complex.abs_re_le_norm`) exactly when `z` and `w` point in opposite directions.

The two sides of the inequality are quotients of nonnegative reals with positive denominators, so
they agree exactly when the cross-multiplied products do, hence exactly when the squares of those
products do; and the shared defect identity displays that difference of squares as
`2 (1 - ‖z‖ ^ 2)(1 - ‖w‖ ^ 2)(‖z‖ ‖w‖ + (z conj w).re)`, whose first two factors are positive on
the disc. -/
theorem pseudoHyperbolicExpr_eq_add_div_one_add_mul_iff_of_norm_lt_one {z w : ℂ}
    (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) :
    pseudoHyperbolicExpr z w = (‖z‖ + ‖w‖) / (1 + ‖z‖ * ‖w‖) ↔
      (z * (starRingEnd ℂ) w).re = -(‖z‖ * ‖w‖) := by
  have hDpos : 0 < ‖1 - (starRingEnd ℂ) w * z‖ :=
    norm_pos_iff.mpr (one_sub_conj_mul_ne_zero_of_norm_lt_one hz hw)
  have hABpos : (0 : ℝ) < 1 + ‖z‖ * ‖w‖ := by positivity
  have hdiff := sq_sub_sq_triangle z w
  have hposfac : 0 < (1 - ‖z‖ ^ 2) * (1 - ‖w‖ ^ 2) := by
    have h₁ : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
    have h₂ : 0 < 1 - ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]
    exact mul_pos h₁ h₂
  rw [pseudoHyperbolicExpr_def, norm_div, div_eq_div_iff hDpos.ne' hABpos.ne']
  constructor
  · intro h
    have hzero : (1 - ‖z‖ ^ 2) * (1 - ‖w‖ ^ 2) *
        (‖z‖ * ‖w‖ + (z * (starRingEnd ℂ) w).re) = 0 := by
      rw [h] at hdiff; linarith
    have := (mul_eq_zero.mp hzero).resolve_left hposfac.ne'
    linarith
  · intro h
    have hsq : (‖z - w‖ * (1 + ‖z‖ * ‖w‖)) ^ 2
        = ((‖z‖ + ‖w‖) * ‖1 - (starRingEnd ℂ) w * z‖) ^ 2 := by
      rw [h] at hdiff; linarith
    have hL : 0 ≤ ‖z - w‖ * (1 + ‖z‖ * ‖w‖) := by positivity
    have hR : 0 ≤ (‖z‖ + ‖w‖) * ‖1 - (starRingEnd ℂ) w * z‖ := by positivity
    have := congrArg Real.sqrt hsq
    rwa [Real.sqrt_sq hL, Real.sqrt_sq hR] at this

/-- **Reverse strong pseudo-hyperbolic triangle inequality (origin form).** For two points of the
open unit disc, `|‖z‖ - ‖w‖| / (1 - ‖z‖ * ‖w‖) ≤ pseudoHyperbolicExpr z w`. This is the
pseudo-hyperbolic form of `|d(z, 0) - d(0, w)| ≤ d(z, w)`, the reverse triangle inequality against
the origin, and it rests on the mirror factorisation
`(‖z - w‖ (1 - ‖z‖ ‖w‖)) ^ 2 - (|‖z‖ - ‖w‖| ‖1 - conj w z‖) ^ 2`
`  = 2 (1 - ‖z‖ ^ 2)(1 - ‖w‖ ^ 2)(‖z‖ ‖w‖ - (z conj w).re)`
of the one behind `pseudoHyperbolicExpr_le_add_div_one_add_mul_of_norm_lt_one`. -/
theorem abs_sub_div_one_sub_mul_le_pseudoHyperbolicExpr_of_norm_lt_one {z w : ℂ}
    (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) :
    |‖z‖ - ‖w‖| / (1 - ‖z‖ * ‖w‖) ≤ pseudoHyperbolicExpr z w := by
  have hDpos : 0 < ‖1 - (starRingEnd ℂ) w * z‖ :=
    norm_pos_iff.mpr (one_sub_conj_mul_ne_zero_of_norm_lt_one hz hw)
  have hABpos : (0 : ℝ) < 1 - ‖z‖ * ‖w‖ := by
    nlinarith [norm_nonneg z, norm_nonneg w]
  have hsq := sq_sub_sq_reverse_triangle z w
  have hL : 0 ≤ ‖z - w‖ * (1 - ‖z‖ * ‖w‖) := by positivity
  have hle : |‖z‖ - ‖w‖| * ‖1 - (starRingEnd ℂ) w * z‖ ≤ ‖z - w‖ * (1 - ‖z‖ * ‖w‖) := by
    have hfac : 0 ≤ (1 - ‖z‖ ^ 2) * (1 - ‖w‖ ^ 2) *
        (‖z‖ * ‖w‖ - (z * (starRingEnd ℂ) w).re) := by
      have h₁ : 0 ≤ 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
      have h₂ : 0 ≤ 1 - ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]
      have h₃ : (z * (starRingEnd ℂ) w).re ≤ ‖z‖ * ‖w‖ := by
        have h := Complex.abs_re_le_norm (z * (starRingEnd ℂ) w)
        rw [norm_mul, Complex.norm_conj] at h
        exact (abs_le.mp h).2
      exact mul_nonneg (mul_nonneg h₁ h₂) (by linarith)
    have hsq' : (|‖z‖ - ‖w‖| * ‖1 - (starRingEnd ℂ) w * z‖) ^ 2
        ≤ (‖z - w‖ * (1 - ‖z‖ * ‖w‖)) ^ 2 := by linarith
    calc |‖z‖ - ‖w‖| * ‖1 - (starRingEnd ℂ) w * z‖
        ≤ |(|‖z‖ - ‖w‖| * ‖1 - (starRingEnd ℂ) w * z‖)| := le_abs_self _
      _ = Real.sqrt ((|‖z‖ - ‖w‖| * ‖1 - (starRingEnd ℂ) w * z‖) ^ 2) :=
          (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt ((‖z - w‖ * (1 - ‖z‖ * ‖w‖)) ^ 2) := Real.sqrt_le_sqrt hsq'
      _ = ‖z - w‖ * (1 - ‖z‖ * ‖w‖) := Real.sqrt_sq hL
  rw [pseudoHyperbolicExpr_def, norm_div, div_le_div_iff₀ hABpos hDpos]
  exact hle

/-- **Equality in the reverse pseudo-hyperbolic triangle inequality against the origin.** For two
points of the open unit disc, `pseudoHyperbolicExpr z w = |‖z‖ - ‖w‖| / (1 - ‖z‖ * ‖w‖)` holds
exactly when `(z * conj w).re = ‖z‖ * ‖w‖`, that is exactly when `z` and `w` point in the same
direction. Together with
`TauCeti.pseudoHyperbolicExpr_eq_add_div_one_add_mul_iff_of_norm_lt_one` this pins down the two
degenerate positions of a hyperbolic triangle with a vertex at the origin. -/
theorem pseudoHyperbolicExpr_eq_abs_sub_div_one_sub_mul_iff_of_norm_lt_one {z w : ℂ}
    (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) :
    pseudoHyperbolicExpr z w = |‖z‖ - ‖w‖| / (1 - ‖z‖ * ‖w‖) ↔
      (z * (starRingEnd ℂ) w).re = ‖z‖ * ‖w‖ := by
  have hDpos : 0 < ‖1 - (starRingEnd ℂ) w * z‖ :=
    norm_pos_iff.mpr (one_sub_conj_mul_ne_zero_of_norm_lt_one hz hw)
  have hABpos : (0 : ℝ) < 1 - ‖z‖ * ‖w‖ := by
    nlinarith [norm_nonneg z, norm_nonneg w]
  have hsq := sq_sub_sq_reverse_triangle z w
  have hposfac : 0 < (1 - ‖z‖ ^ 2) * (1 - ‖w‖ ^ 2) := by
    have h₁ : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
    have h₂ : 0 < 1 - ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]
    exact mul_pos h₁ h₂
  rw [pseudoHyperbolicExpr_def, norm_div, div_eq_div_iff hDpos.ne' hABpos.ne']
  constructor
  · intro h
    have hzero : (1 - ‖z‖ ^ 2) * (1 - ‖w‖ ^ 2) *
        (‖z‖ * ‖w‖ - (z * (starRingEnd ℂ) w).re) = 0 := by
      rw [h] at hsq; linarith
    have := (mul_eq_zero.mp hzero).resolve_left hposfac.ne'
    linarith
  · intro h
    have hsq' : (‖z - w‖ * (1 - ‖z‖ * ‖w‖)) ^ 2
        = (|‖z‖ - ‖w‖| * ‖1 - (starRingEnd ℂ) w * z‖) ^ 2 := by
      rw [h] at hsq; linarith
    have hL : 0 ≤ ‖z - w‖ * (1 - ‖z‖ * ‖w‖) := by positivity
    have hR : 0 ≤ |‖z‖ - ‖w‖| * ‖1 - (starRingEnd ℂ) w * z‖ := by positivity
    have := congrArg Real.sqrt hsq'
    rwa [Real.sqrt_sq hL, Real.sqrt_sq hR] at this

/-- **Hyperbolic triangle inequality against the origin.** For two points of the open unit
disc, `hyperbolicDist z w ≤ hyperbolicDist z 0 + hyperbolicDist 0 w`. -/
theorem hyperbolicDist_triangle_zero {z w : ℂ}
    (hz : z ∈ ball (0 : ℂ) 1) (hw : w ∈ ball (0 : ℂ) 1) :
    hyperbolicDist z w ≤ hyperbolicDist z 0 + hyperbolicDist 0 w := by
  have hzn : ‖z‖ < 1 := by simpa [mem_ball_zero_iff] using hz
  have hwn : ‖w‖ < 1 := by simpa [mem_ball_zero_iff] using hw
  have hρge : 0 ≤ pseudoHyperbolicExpr z w := pseudoHyperbolicExpr_nonneg z w
  rw [hyperbolicDist_def z w, hyperbolicDist_zero_right z, hyperbolicDist_comm 0 w,
    hyperbolicDist_zero_right w]
  have hzIoo : ‖z‖ ∈ Ioo (-1 : ℝ) 1 := ⟨by have := norm_nonneg z; linarith, hzn⟩
  have hwIoo : ‖w‖ ∈ Ioo (-1 : ℝ) 1 := ⟨by have := norm_nonneg w; linarith, hwn⟩
  rw [Real.artanh_add hzIoo hwIoo]
  refine Real.artanh_le_artanh (by linarith) ?_ ?_
  · rw [div_lt_one (by positivity)]
    nlinarith [mul_pos (sub_pos.mpr hzn) (sub_pos.mpr hwn)]
  · exact pseudoHyperbolicExpr_le_add_div_one_add_mul_of_norm_lt_one hzn hwn

/-- **Hyperbolic triangle inequality (bundled unit-disc form).**
`hyperbolicDist z w ≤ hyperbolicDist z u + hyperbolicDist u w`, proved by sending the middle
point `u` to the origin with the Moebius isometry `unitDiscMoebius u`. -/
theorem hyperbolicDist_triangle_unitDisc (u z w : Complex.UnitDisc) :
    hyperbolicDist (z : ℂ) (w : ℂ)
      ≤ hyperbolicDist (z : ℂ) (u : ℂ) + hyperbolicDist (u : ℂ) (w : ℂ) := by
  have hinv : ∀ p q : Complex.UnitDisc,
      hyperbolicDist (unitDiscMoebius u p : ℂ) (unitDiscMoebius u q : ℂ)
        = hyperbolicDist (p : ℂ) (q : ℂ) := fun p q => by
    rw [coe_unitDiscMoebius, coe_unitDiscMoebius]
    exact hyperbolicDist_unitDiscMoebius u p q
  have hmem : ∀ p : Complex.UnitDisc, (unitDiscMoebius u p : ℂ) ∈ ball (0 : ℂ) 1 := fun p => by
    simpa [mem_ball_zero_iff] using (unitDiscMoebius u p).norm_lt_one
  have hself : (unitDiscMoebius u u : ℂ) = 0 := by simp
  have hbase := hyperbolicDist_triangle_zero (hmem z) (hmem w)
  rw [← hself] at hbase
  rw [hinv z w, hinv z u, hinv u w] at hbase
  exact hbase

/-- **Hyperbolic triangle inequality.** The hyperbolic (Poincaré) distance on the complex open
unit disc satisfies `hyperbolicDist z w ≤ hyperbolicDist z u + hyperbolicDist u w`. -/
theorem hyperbolicDist_triangle {z w u : ℂ}
    (hz : z ∈ ball (0 : ℂ) 1) (hw : w ∈ ball (0 : ℂ) 1) (hu : u ∈ ball (0 : ℂ) 1) :
    hyperbolicDist z w ≤ hyperbolicDist z u + hyperbolicDist u w := by
  have hzn : ‖z‖ < 1 := by simpa [mem_ball_zero_iff] using hz
  have hwn : ‖w‖ < 1 := by simpa [mem_ball_zero_iff] using hw
  have hun : ‖u‖ < 1 := by simpa [mem_ball_zero_iff] using hu
  simpa [Complex.UnitDisc.coe_mk] using
    hyperbolicDist_triangle_unitDisc (Complex.UnitDisc.mk u hun)
      (Complex.UnitDisc.mk z hzn) (Complex.UnitDisc.mk w hwn)

/-! ### The pseudo-hyperbolic inequalities at an arbitrary middle point -/

/-- **The strong pseudo-hyperbolic triangle inequality.** For three points of the open unit disc,
`ρ(z, w) ≤ (ρ(z, u) + ρ(u, w)) / (1 + ρ(z, u) ρ(u, w))`, where `ρ = pseudoHyperbolicExpr`. This is
`TauCeti.pseudoHyperbolicExpr_le_add_div_one_add_mul_of_norm_lt_one` with the middle point freed
from the origin: taking `u = 0` and rewriting `ρ(z, 0) = ‖z‖`, `ρ(0, w) = ‖w‖`
(`TauCeti.pseudoHyperbolicExpr_zero_right`, `TauCeti.pseudoHyperbolicExpr_zero_left`) returns that
statement.

The right-hand side is the Moebius sum of `ρ(z, u)` and `ρ(u, w)`, the operation under which
`artanh` carries ordinary addition. It is the sharp bound;
`TauCeti.pseudoHyperbolicExpr_triangle` below is the weaker plain form. -/
theorem pseudoHyperbolicExpr_le_add_div_one_add_mul {z w u : ℂ}
    (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) (hu : ‖u‖ < 1) :
    pseudoHyperbolicExpr z w ≤
      (pseudoHyperbolicExpr z u + pseudoHyperbolicExpr u w) /
        (1 + pseudoHyperbolicExpr z u * pseudoHyperbolicExpr u w) := by
  have hzu := pseudoHyperbolicExpr_mem_Ioo_of_norm_lt_one hz hu
  have huw := pseudoHyperbolicExpr_mem_Ioo_of_norm_lt_one hu hw
  have hzw := pseudoHyperbolicExpr_mem_Ioo_of_norm_lt_one hz hw
  have hd : hyperbolicDist z w ≤ hyperbolicDist z u + hyperbolicDist u w :=
    hyperbolicDist_triangle (by simpa [mem_ball_zero_iff] using hz)
      (by simpa [mem_ball_zero_iff] using hw) (by simpa [mem_ball_zero_iff] using hu)
  rw [hyperbolicDist_def z w, hyperbolicDist_def z u, hyperbolicDist_def u w,
    Real.artanh_add hzu huw] at hd
  exact (Real.artanh_le_artanh_iff hzw (Real.add_div_one_add_mul_mem_Ioo hzu huw)).mp hd

/-- **The strong pseudo-hyperbolic triangle inequality (bundled unit-disc form).** The
hypothesis-free form of `TauCeti.pseudoHyperbolicExpr_le_add_div_one_add_mul` for points of
`Complex.UnitDisc`. -/
theorem pseudoHyperbolicExpr_le_add_div_one_add_mul_unitDisc (z w u : Complex.UnitDisc) :
    pseudoHyperbolicExpr (z : ℂ) (w : ℂ) ≤
      (pseudoHyperbolicExpr (z : ℂ) (u : ℂ) + pseudoHyperbolicExpr (u : ℂ) (w : ℂ)) /
        (1 + pseudoHyperbolicExpr (z : ℂ) (u : ℂ) * pseudoHyperbolicExpr (u : ℂ) (w : ℂ)) :=
  pseudoHyperbolicExpr_le_add_div_one_add_mul z.norm_lt_one w.norm_lt_one u.norm_lt_one

/-- **Equality in the strong pseudo-hyperbolic triangle inequality.** The bound of
`TauCeti.pseudoHyperbolicExpr_le_add_div_one_add_mul` is attained exactly on the degenerate
hyperbolic triangles, those with `hyperbolicDist z w = hyperbolicDist z u + hyperbolicDist u w`,
that is exactly when `u` lies on the hyperbolic geodesic segment from `z` to `w`. -/
theorem pseudoHyperbolicExpr_eq_add_div_one_add_mul_iff {z w u : ℂ}
    (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) (hu : ‖u‖ < 1) :
    pseudoHyperbolicExpr z w =
        (pseudoHyperbolicExpr z u + pseudoHyperbolicExpr u w) /
          (1 + pseudoHyperbolicExpr z u * pseudoHyperbolicExpr u w) ↔
      hyperbolicDist z w = hyperbolicDist z u + hyperbolicDist u w := by
  have hzu := pseudoHyperbolicExpr_mem_Ioo_of_norm_lt_one hz hu
  have huw := pseudoHyperbolicExpr_mem_Ioo_of_norm_lt_one hu hw
  have hzw := pseudoHyperbolicExpr_mem_Ioo_of_norm_lt_one hz hw
  rw [hyperbolicDist_def z w, hyperbolicDist_def z u, hyperbolicDist_def u w,
    Real.artanh_add hzu huw]
  refine ⟨fun h => by rw [h],
    fun h => Real.artanh_injOn hzw (Real.add_div_one_add_mul_mem_Ioo hzu huw) h⟩

/-- **Equality in the strong pseudo-hyperbolic triangle inequality (bundled unit-disc form).**
The hypothesis-free form of `TauCeti.pseudoHyperbolicExpr_eq_add_div_one_add_mul_iff` for points
of `Complex.UnitDisc`. -/
theorem pseudoHyperbolicExpr_eq_add_div_one_add_mul_iff_unitDisc (z w u : Complex.UnitDisc) :
    pseudoHyperbolicExpr (z : ℂ) (w : ℂ) =
        (pseudoHyperbolicExpr (z : ℂ) (u : ℂ) + pseudoHyperbolicExpr (u : ℂ) (w : ℂ)) /
          (1 + pseudoHyperbolicExpr (z : ℂ) (u : ℂ) * pseudoHyperbolicExpr (u : ℂ) (w : ℂ)) ↔
      hyperbolicDist (z : ℂ) (w : ℂ)
        = hyperbolicDist (z : ℂ) (u : ℂ) + hyperbolicDist (u : ℂ) (w : ℂ) :=
  pseudoHyperbolicExpr_eq_add_div_one_add_mul_iff z.norm_lt_one w.norm_lt_one u.norm_lt_one

/-- **The pseudo-hyperbolic triangle inequality.** For three points of the open unit disc,
`ρ(z, w) ≤ ρ(z, u) + ρ(u, w)`: the Moebius sum bounding `ρ(z, w)` in
`TauCeti.pseudoHyperbolicExpr_le_add_div_one_add_mul` has denominator at least `1`, so it is at
most the ordinary sum.

With `TauCeti.pseudoHyperbolicExpr_comm`, `TauCeti.pseudoHyperbolicExpr_self` and
`TauCeti.pseudoHyperbolicExpr_eq_zero_iff_of_norm_lt_one` this makes `pseudoHyperbolicExpr` a
metric on the open unit disc in its own right, and not only a monotone reparametrisation of one.
The Moebius sum is the sharp bound, so this weaker form is the one to quote when the denominator
is a nuisance and the sharpness is not needed. -/
theorem pseudoHyperbolicExpr_triangle {z w u : ℂ}
    (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) (hu : ‖u‖ < 1) :
    pseudoHyperbolicExpr z w ≤ pseudoHyperbolicExpr z u + pseudoHyperbolicExpr u w :=
  (pseudoHyperbolicExpr_le_add_div_one_add_mul hz hw hu).trans <|
    div_le_self (add_nonneg (pseudoHyperbolicExpr_nonneg z u) (pseudoHyperbolicExpr_nonneg u w))
      (le_add_of_nonneg_right
        (mul_nonneg (pseudoHyperbolicExpr_nonneg z u) (pseudoHyperbolicExpr_nonneg u w)))

/-- **The pseudo-hyperbolic triangle inequality (bundled unit-disc form).** The hypothesis-free
form of `TauCeti.pseudoHyperbolicExpr_triangle` for points of `Complex.UnitDisc`, which together
with `TauCeti.pseudoHyperbolicExpr_comm`, `TauCeti.pseudoHyperbolicExpr_self` and
`TauCeti.pseudoHyperbolicExpr_eq_zero_iff_unitDisc` gives the metric axioms for
`pseudoHyperbolicExpr` on that type. -/
theorem pseudoHyperbolicExpr_triangle_unitDisc (z w u : Complex.UnitDisc) :
    pseudoHyperbolicExpr (z : ℂ) (w : ℂ)
      ≤ pseudoHyperbolicExpr (z : ℂ) (u : ℂ) + pseudoHyperbolicExpr (u : ℂ) (w : ℂ) :=
  pseudoHyperbolicExpr_triangle z.norm_lt_one w.norm_lt_one u.norm_lt_one

/-- **The reverse strong pseudo-hyperbolic triangle inequality.** For three points of the open
unit disc, `|ρ(z, u) - ρ(u, w)| / (1 - ρ(z, u) ρ(u, w)) ≤ ρ(z, w)`. This is
`TauCeti.abs_sub_div_one_sub_mul_le_pseudoHyperbolicExpr_of_norm_lt_one` with the middle point
freed from the origin, in the same sense as
`TauCeti.pseudoHyperbolicExpr_le_add_div_one_add_mul`. -/
theorem abs_sub_div_one_sub_mul_le_pseudoHyperbolicExpr {z w u : ℂ}
    (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) (hu : ‖u‖ < 1) :
    |pseudoHyperbolicExpr z u - pseudoHyperbolicExpr u w| /
        (1 - pseudoHyperbolicExpr z u * pseudoHyperbolicExpr u w)
      ≤ pseudoHyperbolicExpr z w := by
  have ha₀ := pseudoHyperbolicExpr_nonneg z u
  have hb₀ := pseudoHyperbolicExpr_nonneg u w
  have hc₀ := pseudoHyperbolicExpr_nonneg z w
  have ha₁ := pseudoHyperbolicExpr_lt_one_of_norm_lt_one hz hu
  have hb₁ := pseudoHyperbolicExpr_lt_one_of_norm_lt_one hu hw
  have hden : (0 : ℝ) < 1 - pseudoHyperbolicExpr z u * pseudoHyperbolicExpr u w := by nlinarith
  have hcb : (0 : ℝ) < 1 + pseudoHyperbolicExpr z w * pseudoHyperbolicExpr u w := by
    have := mul_nonneg hc₀ hb₀; linarith
  have hac : (0 : ℝ) < 1 + pseudoHyperbolicExpr z u * pseudoHyperbolicExpr z w := by
    have := mul_nonneg ha₀ hc₀; linarith
  -- Writing `a = ρ(z, u)`, `b = ρ(u, w)`, `c = ρ(z, w)`, the strong inequality with `w` as the
  -- middle point and with `z` as the middle point gives `a (1 + c b) ≤ c + b` and
  -- `b (1 + a c) ≤ a + c`; each rearranges to a bound `± (a - b) ≤ c (1 - a b)` on the numerator.
  have h₁ := pseudoHyperbolicExpr_le_add_div_one_add_mul hz hu hw
  have h₂ := pseudoHyperbolicExpr_le_add_div_one_add_mul hu hw hz
  rw [pseudoHyperbolicExpr_comm w u] at h₁
  rw [pseudoHyperbolicExpr_comm u z] at h₂
  rw [le_div_iff₀ hcb] at h₁
  rw [le_div_iff₀ hac] at h₂
  rw [div_le_iff₀ hden]
  exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩

/-- **The reverse strong pseudo-hyperbolic triangle inequality (bundled unit-disc form).** The
hypothesis-free form of `TauCeti.abs_sub_div_one_sub_mul_le_pseudoHyperbolicExpr` for points of
`Complex.UnitDisc`. -/
theorem abs_sub_div_one_sub_mul_le_pseudoHyperbolicExpr_unitDisc (z w u : Complex.UnitDisc) :
    |pseudoHyperbolicExpr (z : ℂ) (u : ℂ) - pseudoHyperbolicExpr (u : ℂ) (w : ℂ)| /
        (1 - pseudoHyperbolicExpr (z : ℂ) (u : ℂ) * pseudoHyperbolicExpr (u : ℂ) (w : ℂ))
      ≤ pseudoHyperbolicExpr (z : ℂ) (w : ℂ) :=
  abs_sub_div_one_sub_mul_le_pseudoHyperbolicExpr z.norm_lt_one w.norm_lt_one u.norm_lt_one

/-- **Equality in the reverse strong pseudo-hyperbolic triangle inequality.** The bound of
`TauCeti.abs_sub_div_one_sub_mul_le_pseudoHyperbolicExpr` is attained exactly when one of `z`,
`w` lies on the hyperbolic geodesic segment joining `u` to the other — the two degenerate
positions in which the triangle collapses with `u` outside, rather than inside, the segment
`[z, w]`. -/
theorem pseudoHyperbolicExpr_eq_abs_sub_div_one_sub_mul_iff {z w u : ℂ}
    (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) (hu : ‖u‖ < 1) :
    pseudoHyperbolicExpr z w =
        |pseudoHyperbolicExpr z u - pseudoHyperbolicExpr u w| /
          (1 - pseudoHyperbolicExpr z u * pseudoHyperbolicExpr u w) ↔
      hyperbolicDist z u = hyperbolicDist z w + hyperbolicDist w u ∨
        hyperbolicDist u w = hyperbolicDist u z + hyperbolicDist z w := by
  have ha₀ := pseudoHyperbolicExpr_nonneg z u
  have hb₀ := pseudoHyperbolicExpr_nonneg u w
  have hc₀ := pseudoHyperbolicExpr_nonneg z w
  have ha₁ := pseudoHyperbolicExpr_lt_one_of_norm_lt_one hz hu
  have hb₁ := pseudoHyperbolicExpr_lt_one_of_norm_lt_one hu hw
  have hden : (0 : ℝ) < 1 - pseudoHyperbolicExpr z u * pseudoHyperbolicExpr u w := by nlinarith
  have hcb : (0 : ℝ) < 1 + pseudoHyperbolicExpr z w * pseudoHyperbolicExpr u w := by
    have := mul_nonneg hc₀ hb₀; linarith
  have hac : (0 : ℝ) < 1 + pseudoHyperbolicExpr z u * pseudoHyperbolicExpr z w := by
    have := mul_nonneg ha₀ hc₀; linarith
  -- With `a = ρ(z, u)`, `b = ρ(u, w)`, `c = ρ(z, w)`, the equation `|a - b| = c (1 - a b)` splits
  -- into `a - b = c (1 - a b)` and `b - a = c (1 - a b)`, and each of those rearranges to the
  -- equality case of the strong inequality with `w`, respectively `z`, as middle point.
  have e₁ := pseudoHyperbolicExpr_eq_add_div_one_add_mul_iff hz hu hw
  have e₂ := pseudoHyperbolicExpr_eq_add_div_one_add_mul_iff hu hw hz
  rw [pseudoHyperbolicExpr_comm w u] at e₁
  rw [pseudoHyperbolicExpr_comm u z] at e₂
  rw [eq_div_iff hcb.ne'] at e₁
  rw [eq_div_iff hac.ne'] at e₂
  rw [eq_div_iff hden.ne', eq_comm, abs_eq (mul_nonneg hc₀ hden.le), ← e₁, ← e₂]
  constructor
  · rintro (h | h)
    · exact Or.inl (by linear_combination h)
    · exact Or.inr (by linear_combination -h)
  · rintro (h | h)
    · exact Or.inl (by linear_combination h)
    · exact Or.inr (by linear_combination -h)

/-- **Equality in the reverse strong pseudo-hyperbolic triangle inequality (bundled unit-disc
form).** The hypothesis-free form of
`TauCeti.pseudoHyperbolicExpr_eq_abs_sub_div_one_sub_mul_iff` for points of
`Complex.UnitDisc`. -/
theorem pseudoHyperbolicExpr_eq_abs_sub_div_one_sub_mul_iff_unitDisc (z w u : Complex.UnitDisc) :
    pseudoHyperbolicExpr (z : ℂ) (w : ℂ) =
        |pseudoHyperbolicExpr (z : ℂ) (u : ℂ) - pseudoHyperbolicExpr (u : ℂ) (w : ℂ)| /
          (1 - pseudoHyperbolicExpr (z : ℂ) (u : ℂ) * pseudoHyperbolicExpr (u : ℂ) (w : ℂ)) ↔
      hyperbolicDist (z : ℂ) (u : ℂ)
          = hyperbolicDist (z : ℂ) (w : ℂ) + hyperbolicDist (w : ℂ) (u : ℂ) ∨
        hyperbolicDist (u : ℂ) (w : ℂ)
          = hyperbolicDist (u : ℂ) (z : ℂ) + hyperbolicDist (z : ℂ) (w : ℂ) :=
  pseudoHyperbolicExpr_eq_abs_sub_div_one_sub_mul_iff z.norm_lt_one w.norm_lt_one u.norm_lt_one

end TauCeti
