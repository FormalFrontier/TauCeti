/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.Poincare.MetricSpace

/-!
# Hyperbolic balls of the Poincaré disc are Euclidean discs

The hyperbolic (Poincaré) metric `TauCeti.hyperbolicDist` on the open unit disc is
`Real.artanh` of the pseudo-hyperbolic expression
`p (z, a) = ‖(z - a) / (1 - conj a * z)‖`, and both are visibly non-Euclidean: the metric blows
up at the boundary circle, and `p` is a Moebius quotient rather than a norm. Nevertheless the
*balls* of the two metrics are the same sets. This file proves that, with the centre and radius
computed explicitly.

Fix `a` in the disc and a pseudo-hyperbolic radius `t ∈ [0, 1)`. Writing
`D = 1 - t ^ 2 * ‖a‖ ^ 2`, which is positive, put

* `TauCeti.pseudoHyperbolicCenter a t = ((1 - t ^ 2) / D) • a`,
* `TauCeti.pseudoHyperbolicRadius a t = t * (1 - ‖a‖ ^ 2) / D`.

Then `{z ∈ 𝔻 | p (z, a) < t}` is exactly the Euclidean disc of that centre and radius
(`TauCeti.sep_ball_pseudoHyperbolicExpr_lt_eq_ball`), and likewise for `≤` and `=` with the
closed disc and the circle. Substituting `t = Real.tanh R` converts these into statements about
the hyperbolic metric, since `Real.artanh` and `Real.tanh` are inverse increasing bijections
between `(-1, 1)` and `ℝ`: the hyperbolic ball of centre `a` and radius `R` is the Euclidean
disc of centre `pseudoHyperbolicCenter a (Real.tanh R)` and radius
`pseudoHyperbolicRadius a (Real.tanh R)` (`TauCeti.sep_ball_hyperbolicDist_lt_eq_ball`).

## The computation

Everything comes from a single algebraic identity between real quadratics
(`TauCeti.sq_norm_sub_sub_mul_sq_norm_one_sub_conj_mul`):

> `‖z - a‖ ^ 2 - t ^ 2 * ‖1 - conj a * z‖ ^ 2`
> `  = D * (‖z - pseudoHyperbolicCenter a t‖ ^ 2 - pseudoHyperbolicRadius a t ^ 2)`,

valid for every `z : ℂ` as soon as `D ≠ 0`. Expanding both norms as
`‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2` turns each side into a real polynomial in
`a.re, a.im, z.re, z.im, t`, and the two agree after clearing the denominator `D`. Since `D > 0`,
the left side is negative, zero or positive exactly when `‖z - c‖` is less than, equal to or
greater than the radius, which is the whole content: the pseudo-hyperbolic condition
`‖z - a‖ < t * ‖1 - conj a * z‖` is a Euclidean disc.

Two features of the statement are worth noting. First, the identity — and hence the description
of the sublevel set of `‖z - a‖ - t * ‖1 - conj a * z‖` — needs no hypothesis on `z` at all; it is
only the passage to the *quotient* `p (z, a)` that requires `z` in the disc, so that the Moebius
denominator does not vanish. Second, the resulting Euclidean disc automatically lies inside the
unit disc: `‖c‖ + s < 1` because
`1 - ‖c‖ - s = (1 - ‖a‖) * (1 - t) * (1 - t * ‖a‖) / D`
(`TauCeti.norm_pseudoHyperbolicCenter_add_pseudoHyperbolicRadius_lt_one`). So the restriction to
the disc in the set equalities is a genuine description of a subset of `𝔻`, not an artefact.

The Euclidean centre `c` is *not* `a` unless `a = 0` or `t = 0`: a hyperbolic ball is a Euclidean
disc, but an off-centre one, its Euclidean centre pulled towards the origin by the factor
`(1 - t ^ 2) / D`. The hyperbolic centre does lie inside it
(`TauCeti.mem_ball_pseudoHyperbolicCenter`), as it must.

## What this adds

`Poincare/Topology.lean` already identifies the closed hyperbolic ball *about the origin* with a
Euclidean ball (`TauCeti.hyperbolicDist_zero_le_iff_norm_le_tanh`, the case `a = 0`, where the
Moebius denominator is `1` and the computation is immediate) and uses it for properness. The
general centre is what a *local* argument needs, and it is not a formal consequence of the special
case: the disc automorphism moving `a` to the origin is a hyperbolic isometry but not a Euclidean
one, so it does not transport a Euclidean ball to a Euclidean ball. The explicit centre and radius
are the point.

Two immediate consequences are recorded: hyperbolic balls are convex for the *Euclidean* structure
(`TauCeti.convex_sep_ball_hyperbolicDist_lt`), a fact with no hyperbolic proof at this stage of the
development, since geodesic convexity is a different statement; and the balls of the metric space
`TauCeti.PoincareDisc` are characterised in Euclidean terms
(`TauCeti.PoincareDisc.mem_ball_iff`).

## Generality

In accordance with the generality bar of `ConformalMapping/README.md`, which fixes scalar `ℂ` for
every theorem added in layers L0–L6, everything below is stated for `ℂ`. The statements are not
merely specialised but genuinely two-dimensional: the identity above is the complex-analytic
Apollonius computation, and its conclusion — that a Moebius sublevel set is a disc — has no
analogue in a general normed space.

## Main definitions

* `TauCeti.pseudoHyperbolicCenter` — the Euclidean centre of the pseudo-hyperbolic ball.
* `TauCeti.pseudoHyperbolicRadius` — its Euclidean radius.

## Main results

* `TauCeti.sq_norm_sub_sub_mul_sq_norm_one_sub_conj_mul` — the Apollonius identity the file runs
  on.
* `TauCeti.norm_pseudoHyperbolicCenter_add_pseudoHyperbolicRadius_lt_one` and
  `TauCeti.closedBall_pseudoHyperbolicCenter_subset_ball` — the Euclidean disc lies inside `𝔻`.
* `TauCeti.pseudoHyperbolicExpr_lt_iff_mem_ball` and
  `TauCeti.pseudoHyperbolicExpr_le_iff_mem_closedBall` — the pointwise form.
* `TauCeti.sep_ball_pseudoHyperbolicExpr_lt_eq_ball`,
  `TauCeti.sep_ball_pseudoHyperbolicExpr_le_eq_closedBall` and
  `TauCeti.sep_ball_pseudoHyperbolicExpr_eq_eq_sphere` — pseudo-hyperbolic balls, closed balls and
  circles are Euclidean ones.
* `TauCeti.sep_ball_hyperbolicDist_lt_eq_ball` and
  `TauCeti.sep_ball_hyperbolicDist_le_eq_closedBall` — the same for the hyperbolic metric, with
  `t = Real.tanh R`.
* `TauCeti.PoincareDisc.mem_ball_iff` — the balls of the Poincaré metric space, read on the
  Euclidean disc.

This carries the conformal-mapping roadmap's L2 target "the hyperbolic / Poincaré metric on `𝔻`"
(see `ConformalMapping/README.md`) onto its metric geometry, completing the basic ball API of that
metric. As with the rest of the L0–L3 conformal-mapping material it is coordinated with the
upstream Mathlib Riemann mapping effort leanprover-community/mathlib4#33505, which contains the
preceding human-curated work along with `Analysis/Complex/RiemannMapping.lean` and
`Analysis/Complex/BranchLogRoot.lean`; none of that material describes the hyperbolic metric on
the disc, and Mathlib's `Analysis/Complex/UpperHalfPlane` hyperbolic metric carries no ball
description of this kind, so nothing here duplicates it.

## References

* L. V. Ahlfors, *Conformal Invariants*, Ch. 1.
* J. B. Garnett and D. E. Marshall, *Harmonic Measure*, Ch. I §1.
* Ch. Pommerenke, *Boundary Behaviour of Conformal Maps*, §1.2.
-/

public section

namespace TauCeti

open _root_.Complex Metric Set
open scoped ComplexConjugate

variable {a z : ℂ} {t R : ℝ}

/-! ### The Euclidean centre and radius -/

/-- The Euclidean centre of the pseudo-hyperbolic ball of centre `a` and radius `t`: the
hyperbolic centre `a` pulled towards the origin by the factor
`(1 - t ^ 2) / (1 - t ^ 2 * ‖a‖ ^ 2)`. -/
@[expose] noncomputable def pseudoHyperbolicCenter (a : ℂ) (t : ℝ) : ℂ :=
  ((1 - t ^ 2) / (1 - t ^ 2 * ‖a‖ ^ 2)) • a

/-- The Euclidean radius of the pseudo-hyperbolic ball of centre `a` and radius `t`. -/
@[expose] noncomputable def pseudoHyperbolicRadius (a : ℂ) (t : ℝ) : ℝ :=
  t * (1 - ‖a‖ ^ 2) / (1 - t ^ 2 * ‖a‖ ^ 2)

/-- The defining formula for `TauCeti.pseudoHyperbolicCenter`. -/
lemma pseudoHyperbolicCenter_def (a : ℂ) (t : ℝ) :
    pseudoHyperbolicCenter a t = ((1 - t ^ 2) / (1 - t ^ 2 * ‖a‖ ^ 2)) • a := rfl

/-- The defining formula for `TauCeti.pseudoHyperbolicRadius`. -/
lemma pseudoHyperbolicRadius_def (a : ℂ) (t : ℝ) :
    pseudoHyperbolicRadius a t = t * (1 - ‖a‖ ^ 2) / (1 - t ^ 2 * ‖a‖ ^ 2) := rfl

/-- Balls centred at the origin are unmoved: the Euclidean centre of a pseudo-hyperbolic ball
about `0` is `0`. -/
@[simp]
lemma pseudoHyperbolicCenter_zero_left (t : ℝ) : pseudoHyperbolicCenter 0 t = 0 := by
  simp [pseudoHyperbolicCenter_def]

/-- Balls centred at the origin have their Euclidean radius equal to the pseudo-hyperbolic one,
so that at the origin the two descriptions of a ball coincide. -/
@[simp]
lemma pseudoHyperbolicRadius_zero_left (t : ℝ) : pseudoHyperbolicRadius 0 t = t := by
  simp [pseudoHyperbolicRadius_def]

/-- A ball of radius `0` is centred at its hyperbolic centre. -/
@[simp]
lemma pseudoHyperbolicCenter_zero_right (a : ℂ) : pseudoHyperbolicCenter a 0 = a := by
  simp [pseudoHyperbolicCenter_def]

/-- A ball of radius `0` has Euclidean radius `0`. -/
@[simp]
lemma pseudoHyperbolicRadius_zero_right (a : ℂ) : pseudoHyperbolicRadius a 0 = 0 := by
  simp [pseudoHyperbolicRadius_def]

/-- The denominator `1 - t ^ 2 * ‖a‖ ^ 2` is positive for a disc centre and a radius in `[0, 1]`.
This is what makes the Apollonius identity a genuine comparison of discs rather than a degenerate
one. -/
lemma one_sub_sq_mul_sq_norm_pos (ha : ‖a‖ < 1) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    0 < 1 - t ^ 2 * ‖a‖ ^ 2 := by
  have hn : 0 ≤ ‖a‖ := norm_nonneg a
  have hn2 : ‖a‖ ^ 2 < 1 := by nlinarith
  nlinarith [mul_nonneg (by nlinarith : (0 : ℝ) ≤ 1 - t ^ 2) (sq_nonneg ‖a‖)]

/-- The Euclidean radius of a pseudo-hyperbolic ball is nonnegative. -/
lemma pseudoHyperbolicRadius_nonneg (ha : ‖a‖ < 1) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    0 ≤ pseudoHyperbolicRadius a t := by
  have hn : 0 ≤ ‖a‖ := norm_nonneg a
  have hn2 : ‖a‖ ^ 2 < 1 := by nlinarith
  exact div_nonneg (mul_nonneg ht₀ (by linarith))
    (one_sub_sq_mul_sq_norm_pos ha ht₀ ht₁).le

/-- The Euclidean radius of a pseudo-hyperbolic ball of positive radius is positive. -/
lemma pseudoHyperbolicRadius_pos (ha : ‖a‖ < 1) (ht₀ : 0 < t) (ht₁ : t ≤ 1) :
    0 < pseudoHyperbolicRadius a t := by
  have hn : 0 ≤ ‖a‖ := norm_nonneg a
  have hn2 : ‖a‖ ^ 2 < 1 := by nlinarith
  exact div_pos (mul_pos ht₀ (by linarith))
    (one_sub_sq_mul_sq_norm_pos ha ht₀.le ht₁)

/-! ### The Euclidean disc lies inside the unit disc -/

/-- **A pseudo-hyperbolic ball stays inside the unit disc**, quantitatively: the Euclidean centre
and radius satisfy `‖c‖ + s < 1`, because
`1 - ‖c‖ - s = (1 - ‖a‖) * (1 - t) * (1 - t * ‖a‖) / (1 - t ^ 2 * ‖a‖ ^ 2)`
and each of the three factors is positive. -/
lemma norm_pseudoHyperbolicCenter_add_pseudoHyperbolicRadius_lt_one
    (ha : ‖a‖ < 1) (ht₀ : 0 ≤ t) (ht₁ : t < 1) :
    ‖pseudoHyperbolicCenter a t‖ + pseudoHyperbolicRadius a t < 1 := by
  have hn : 0 ≤ ‖a‖ := norm_nonneg a
  have hD : 0 < 1 - t ^ 2 * ‖a‖ ^ 2 := one_sub_sq_mul_sq_norm_pos ha ht₀ ht₁.le
  have hnum : 0 ≤ (1 - t ^ 2) / (1 - t ^ 2 * ‖a‖ ^ 2) := by
    apply div_nonneg _ hD.le
    nlinarith
  have hcnorm : ‖pseudoHyperbolicCenter a t‖ = (1 - t ^ 2) / (1 - t ^ 2 * ‖a‖ ^ 2) * ‖a‖ := by
    rw [pseudoHyperbolicCenter_def, norm_smul, Real.norm_eq_abs, abs_of_nonneg hnum]
  have hkey : 0 < (1 - ‖a‖) * (1 - t) * (1 - t * ‖a‖) := by
    refine mul_pos (mul_pos (by linarith) (by linarith)) ?_
    nlinarith
  rw [hcnorm, pseudoHyperbolicRadius_def, div_mul_eq_mul_div, ← add_div, div_lt_one hD]
  nlinarith [hkey]

/-- The closed Euclidean disc describing a pseudo-hyperbolic ball is contained in the open unit
disc; a fortiori so is the open one. -/
lemma closedBall_pseudoHyperbolicCenter_subset_ball (ha : ‖a‖ < 1) (ht₀ : 0 ≤ t) (ht₁ : t < 1) :
    closedBall (pseudoHyperbolicCenter a t) (pseudoHyperbolicRadius a t) ⊆ ball (0 : ℂ) 1 := by
  intro w hw
  have h := norm_pseudoHyperbolicCenter_add_pseudoHyperbolicRadius_lt_one ha ht₀ ht₁
  have hle : ‖w - pseudoHyperbolicCenter a t‖ ≤ pseudoHyperbolicRadius a t := by
    simpa [dist_eq_norm] using hw
  have : ‖w‖ ≤ ‖w - pseudoHyperbolicCenter a t‖ + ‖pseudoHyperbolicCenter a t‖ := by
    simpa using norm_add_le (w - pseudoHyperbolicCenter a t) (pseudoHyperbolicCenter a t)
  exact mem_ball_zero_iff.2 (by linarith)

/-! ### The Apollonius identity -/

/-- **The Apollonius identity for the Moebius factor.** For every `z : ℂ`,

`‖z - a‖ ^ 2 - t ^ 2 * ‖1 - conj a * z‖ ^ 2`
`  = (1 - t ^ 2 * ‖a‖ ^ 2)`
`      * (‖z - pseudoHyperbolicCenter a t‖ ^ 2 - pseudoHyperbolicRadius a t ^ 2)`.

Both sides are real quadratics in `z.re` and `z.im` with the same leading coefficient
`1 - t ^ 2 * ‖a‖ ^ 2`, and the definitions of `TauCeti.pseudoHyperbolicCenter` and
`TauCeti.pseudoHyperbolicRadius` are exactly what completes the square. No hypothesis is placed on
`z`, and the disc hypothesis on `a` enters only through the nonvanishing of the denominator. -/
theorem sq_norm_sub_sub_mul_sq_norm_one_sub_conj_mul (a z : ℂ) (t : ℝ)
    (hD : 1 - t ^ 2 * ‖a‖ ^ 2 ≠ 0) :
    ‖z - a‖ ^ 2 - t ^ 2 * ‖1 - conj a * z‖ ^ 2
      = (1 - t ^ 2 * ‖a‖ ^ 2) *
        (‖z - pseudoHyperbolicCenter a t‖ ^ 2 - pseudoHyperbolicRadius a t ^ 2) := by
  have hshift : ∀ k : ℝ, ‖z - k • a‖ ^ 2
      = ‖z‖ ^ 2 - 2 * k * (z.re * a.re + z.im * a.im) + k ^ 2 * ‖a‖ ^ 2 := by
    intro k
    simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.real_smul, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hsub : ‖z - a‖ ^ 2
      = ‖z‖ ^ 2 - 2 * (z.re * a.re + z.im * a.im) + ‖a‖ ^ 2 := by
    simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
    ring
  have hmoebius : ‖1 - conj a * z‖ ^ 2
      = 1 - 2 * (z.re * a.re + z.im * a.im) + ‖a‖ ^ 2 * ‖z‖ ^ 2 := by
    simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.mul_im, Complex.one_re, Complex.one_im, Complex.conj_re,
      Complex.conj_im]
    ring
  rw [pseudoHyperbolicCenter_def, pseudoHyperbolicRadius_def, hshift, hsub, hmoebius]
  obtain ⟨D, hDdef⟩ : ∃ D : ℝ, D = 1 - t ^ 2 * ‖a‖ ^ 2 := ⟨_, rfl⟩
  rw [← hDdef] at hD ⊢
  field_simp
  subst hDdef
  ring

/-! ### Pseudo-hyperbolic balls are Euclidean discs -/

/-- **The pseudo-hyperbolic ball is a Euclidean disc.** A point `z` of the unit disc satisfies
`pseudoHyperbolicExpr z a < t` exactly when it lies in the Euclidean disc of centre
`TauCeti.pseudoHyperbolicCenter a t` and radius `TauCeti.pseudoHyperbolicRadius a t`.

Clearing the Moebius denominator — legitimate because `z` and `a` lie in the disc — turns the
left-hand condition into `‖z - a‖ < t * ‖1 - conj a * z‖`, and squaring both sides makes
`TauCeti.sq_norm_sub_sub_mul_sq_norm_one_sub_conj_mul` applicable; the factor
`1 - t ^ 2 * ‖a‖ ^ 2` it produces is positive, so it does not affect the sign. -/
theorem pseudoHyperbolicExpr_lt_iff_mem_ball (ha : ‖a‖ < 1) (hz : ‖z‖ < 1)
    (ht₀ : 0 ≤ t) (ht₁ : t < 1) :
    pseudoHyperbolicExpr z a < t ↔
      z ∈ ball (pseudoHyperbolicCenter a t) (pseudoHyperbolicRadius a t) := by
  have hD : 0 < 1 - t ^ 2 * ‖a‖ ^ 2 := one_sub_sq_mul_sq_norm_pos ha ht₀ ht₁.le
  have hdenpos : 0 < ‖(1 : ℂ) - conj a * z‖ :=
    norm_pos_iff.2 (one_sub_conj_mul_ne_zero_of_norm_lt_one hz ha)
  have hid := sq_norm_sub_sub_mul_sq_norm_one_sub_conj_mul a z t hD.ne'
  rw [pseudoHyperbolicExpr_def, norm_div, div_lt_iff₀ hdenpos, mem_ball, dist_eq_norm,
    ← sq_lt_sq₀ (norm_nonneg _) (by positivity),
    ← sq_lt_sq₀ (norm_nonneg _) (pseudoHyperbolicRadius_nonneg ha ht₀ ht₁.le), mul_pow]
  constructor <;> intro h <;> nlinarith

/-- **The closed pseudo-hyperbolic ball is a closed Euclidean disc**, the `≤` companion of
`TauCeti.pseudoHyperbolicExpr_lt_iff_mem_ball` with the same proof. -/
theorem pseudoHyperbolicExpr_le_iff_mem_closedBall (ha : ‖a‖ < 1) (hz : ‖z‖ < 1)
    (ht₀ : 0 ≤ t) (ht₁ : t < 1) :
    pseudoHyperbolicExpr z a ≤ t ↔
      z ∈ closedBall (pseudoHyperbolicCenter a t) (pseudoHyperbolicRadius a t) := by
  have hD : 0 < 1 - t ^ 2 * ‖a‖ ^ 2 := one_sub_sq_mul_sq_norm_pos ha ht₀ ht₁.le
  have hdenpos : 0 < ‖(1 : ℂ) - conj a * z‖ :=
    norm_pos_iff.2 (one_sub_conj_mul_ne_zero_of_norm_lt_one hz ha)
  have hid := sq_norm_sub_sub_mul_sq_norm_one_sub_conj_mul a z t hD.ne'
  rw [pseudoHyperbolicExpr_def, norm_div, div_le_iff₀ hdenpos, mem_closedBall, dist_eq_norm,
    ← sq_le_sq₀ (norm_nonneg _) (by positivity),
    ← sq_le_sq₀ (norm_nonneg _) (pseudoHyperbolicRadius_nonneg ha ht₀ ht₁.le), mul_pow]
  constructor <;> intro h <;> nlinarith

/-- The hyperbolic centre of a ball of positive radius lies in the Euclidean disc describing it —
off centre, but inside. -/
theorem mem_ball_pseudoHyperbolicCenter (ha : ‖a‖ < 1) (ht₀ : 0 < t) (ht₁ : t < 1) :
    a ∈ ball (pseudoHyperbolicCenter a t) (pseudoHyperbolicRadius a t) :=
  (pseudoHyperbolicExpr_lt_iff_mem_ball ha ha ht₀.le ht₁).1 (by simpa using ht₀)

/-- **A pseudo-hyperbolic ball of the unit disc is a Euclidean disc**, in set form. -/
theorem sep_ball_pseudoHyperbolicExpr_lt_eq_ball (ha : ‖a‖ < 1) (ht₀ : 0 ≤ t) (ht₁ : t < 1) :
    {z ∈ ball (0 : ℂ) 1 | pseudoHyperbolicExpr z a < t}
      = ball (pseudoHyperbolicCenter a t) (pseudoHyperbolicRadius a t) := by
  ext w
  simp only [mem_ball_zero_iff]
  refine ⟨fun h => (pseudoHyperbolicExpr_lt_iff_mem_ball ha h.1 ht₀ ht₁).1 h.2, fun h => ?_⟩
  have hw : ‖w‖ < 1 := mem_ball_zero_iff.1 <| closedBall_pseudoHyperbolicCenter_subset_ball
    ha ht₀ ht₁ (ball_subset_closedBall h)
  exact ⟨hw, (pseudoHyperbolicExpr_lt_iff_mem_ball ha hw ht₀ ht₁).2 h⟩

/-- **A closed pseudo-hyperbolic ball of the unit disc is a closed Euclidean disc**, in set
form. -/
theorem sep_ball_pseudoHyperbolicExpr_le_eq_closedBall (ha : ‖a‖ < 1) (ht₀ : 0 ≤ t)
    (ht₁ : t < 1) :
    {z ∈ ball (0 : ℂ) 1 | pseudoHyperbolicExpr z a ≤ t}
      = closedBall (pseudoHyperbolicCenter a t) (pseudoHyperbolicRadius a t) := by
  ext w
  simp only [mem_ball_zero_iff]
  refine ⟨fun h => (pseudoHyperbolicExpr_le_iff_mem_closedBall ha h.1 ht₀ ht₁).1 h.2, fun h => ?_⟩
  have hw : ‖w‖ < 1 :=
    mem_ball_zero_iff.1 <| closedBall_pseudoHyperbolicCenter_subset_ball ha ht₀ ht₁ h
  exact ⟨hw, (pseudoHyperbolicExpr_le_iff_mem_closedBall ha hw ht₀ ht₁).2 h⟩

/-- **A pseudo-hyperbolic circle of the unit disc is a Euclidean circle**: the level set is the
difference of the closed and the open disc. -/
theorem sep_ball_pseudoHyperbolicExpr_eq_eq_sphere (ha : ‖a‖ < 1) (ht₀ : 0 ≤ t) (ht₁ : t < 1) :
    {z ∈ ball (0 : ℂ) 1 | pseudoHyperbolicExpr z a = t}
      = sphere (pseudoHyperbolicCenter a t) (pseudoHyperbolicRadius a t) := by
  ext w
  constructor
  · rintro ⟨hw, heq⟩
    rw [mem_ball_zero_iff] at hw
    have hle := (pseudoHyperbolicExpr_le_iff_mem_closedBall ha hw ht₀ ht₁).1 heq.le
    have hnlt : ¬ dist w (pseudoHyperbolicCenter a t) < pseudoHyperbolicRadius a t := fun hd => by
      have := (pseudoHyperbolicExpr_lt_iff_mem_ball ha hw ht₀ ht₁).2 (mem_ball.2 hd)
      rw [heq] at this
      exact lt_irrefl t this
    exact mem_sphere.2 (le_antisymm (mem_closedBall.1 hle) (not_lt.1 hnlt))
  · intro h
    rw [mem_sphere] at h
    have hle : w ∈ closedBall (pseudoHyperbolicCenter a t) (pseudoHyperbolicRadius a t) :=
      mem_closedBall.2 h.le
    have hw : ‖w‖ < 1 := mem_ball_zero_iff.1
      (closedBall_pseudoHyperbolicCenter_subset_ball ha ht₀ ht₁ hle)
    refine ⟨mem_ball_zero_iff.2 hw,
      le_antisymm ((pseudoHyperbolicExpr_le_iff_mem_closedBall ha hw ht₀ ht₁).2 hle) ?_⟩
    by_contra hlt
    have hb := (pseudoHyperbolicExpr_lt_iff_mem_ball ha hw ht₀ ht₁).1 (not_le.1 hlt)
    rw [mem_ball, h] at hb
    exact lt_irrefl _ hb

/-! ### Hyperbolic balls -/

/-- `Real.tanh` is nonnegative on the nonnegative reals, so a hyperbolic radius `R ≥ 0`
corresponds to a pseudo-hyperbolic radius `Real.tanh R ∈ [0, 1)`. -/
lemma tanh_nonneg (hR : 0 ≤ R) : 0 ≤ Real.tanh R := by
  by_contra h
  have hneg : Real.tanh R < 0 := not_le.1 h
  have hle : R ≤ 0 := by
    have := Real.artanh_nonpos hneg.le
    rwa [Real.artanh_tanh] at this
  rw [le_antisymm hle hR, Real.tanh_zero] at hneg
  exact lt_irrefl 0 hneg

/-- The hyperbolic distance is below `R` exactly when the pseudo-hyperbolic expression is below
`Real.tanh R`: the hyperbolic distance is `Real.artanh` of the pseudo-hyperbolic expression, and
`Real.artanh` is the increasing inverse of `Real.tanh`. -/
lemma hyperbolicDist_lt_iff_pseudoHyperbolicExpr_lt_tanh (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) :
    hyperbolicDist z a < R ↔ pseudoHyperbolicExpr z a < Real.tanh R := by
  have hp₀ : 0 ≤ pseudoHyperbolicExpr z a := pseudoHyperbolicExpr_nonneg z a
  have hp₁ : pseudoHyperbolicExpr z a < 1 := pseudoHyperbolicExpr_lt_one_of_norm_lt_one hz ha
  rw [hyperbolicDist_def]
  refine Iff.trans ?_ (Real.artanh_lt_artanh_iff (x := pseudoHyperbolicExpr z a)
    (y := Real.tanh R) ⟨by linarith, hp₁⟩ ⟨Real.neg_one_lt_tanh R, Real.tanh_lt_one R⟩)
  rw [Real.artanh_tanh]

/-- The `≤` companion of `TauCeti.hyperbolicDist_lt_iff_pseudoHyperbolicExpr_lt_tanh`. -/
lemma hyperbolicDist_le_iff_pseudoHyperbolicExpr_le_tanh (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) :
    hyperbolicDist z a ≤ R ↔ pseudoHyperbolicExpr z a ≤ Real.tanh R := by
  have hp₀ : 0 ≤ pseudoHyperbolicExpr z a := pseudoHyperbolicExpr_nonneg z a
  have hp₁ : pseudoHyperbolicExpr z a < 1 := pseudoHyperbolicExpr_lt_one_of_norm_lt_one hz ha
  rw [hyperbolicDist_def]
  refine Iff.trans ?_ (Real.artanh_le_artanh_iff (x := pseudoHyperbolicExpr z a)
    (y := Real.tanh R) ⟨by linarith, hp₁⟩ ⟨Real.neg_one_lt_tanh R, Real.tanh_lt_one R⟩)
  rw [Real.artanh_tanh]

/-- **A hyperbolic ball of the Poincaré disc is a Euclidean disc.** The hyperbolic ball of centre
`a` and radius `R ≥ 0` is the Euclidean disc of centre
`pseudoHyperbolicCenter a (Real.tanh R)` and radius `pseudoHyperbolicRadius a (Real.tanh R)`.

The Euclidean centre is `a` only for `a = 0` or `R = 0`; for `a ≠ 0` the hyperbolic ball is an
off-centre Euclidean disc, pulled towards the origin. Specialising to `a = 0` recovers
`TauCeti.hyperbolicDist_zero_le_iff_norm_le_tanh` of `Poincare/Topology.lean`, where the
Euclidean centre is the origin and the Euclidean radius is `Real.tanh R`. -/
theorem sep_ball_hyperbolicDist_lt_eq_ball (ha : ‖a‖ < 1) (hR : 0 ≤ R) :
    {z ∈ ball (0 : ℂ) 1 | hyperbolicDist z a < R}
      = ball (pseudoHyperbolicCenter a (Real.tanh R)) (pseudoHyperbolicRadius a (Real.tanh R)) := by
  rw [← sep_ball_pseudoHyperbolicExpr_lt_eq_ball ha (tanh_nonneg hR) (Real.tanh_lt_one R)]
  ext w
  simp only [mem_ball_zero_iff]
  exact and_congr_right fun hw => hyperbolicDist_lt_iff_pseudoHyperbolicExpr_lt_tanh ha hw

/-- **A closed hyperbolic ball of the Poincaré disc is a closed Euclidean disc**, the `≤`
companion of `TauCeti.sep_ball_hyperbolicDist_lt_eq_ball`. -/
theorem sep_ball_hyperbolicDist_le_eq_closedBall (ha : ‖a‖ < 1) (hR : 0 ≤ R) :
    {z ∈ ball (0 : ℂ) 1 | hyperbolicDist z a ≤ R}
      = closedBall (pseudoHyperbolicCenter a (Real.tanh R))
        (pseudoHyperbolicRadius a (Real.tanh R)) := by
  rw [← sep_ball_pseudoHyperbolicExpr_le_eq_closedBall ha (tanh_nonneg hR) (Real.tanh_lt_one R)]
  ext w
  simp only [mem_ball_zero_iff]
  exact and_congr_right fun hw => hyperbolicDist_le_iff_pseudoHyperbolicExpr_le_tanh ha hw

/-- **Hyperbolic balls are Euclidean-convex.** Being Euclidean discs, the balls of the hyperbolic
metric are convex for the linear structure of `ℂ`. This is not the geodesic convexity of the
hyperbolic metric, which is a separate statement about the hyperbolic geodesics of
`Poincare/Geodesic.lean`; it is the stronger Euclidean one, and it has no proof internal to the
hyperbolic metric. -/
theorem convex_sep_ball_hyperbolicDist_lt (ha : ‖a‖ < 1) (hR : 0 ≤ R) :
    Convex ℝ {z ∈ ball (0 : ℂ) 1 | hyperbolicDist z a < R} := by
  rw [sep_ball_hyperbolicDist_lt_eq_ball ha hR]
  exact convex_ball _ _

namespace PoincareDisc

/-- **The balls of the Poincaré metric space, read on the Euclidean disc.** A point of
`TauCeti.PoincareDisc` lies in the hyperbolic ball of centre `x` and radius `R ≥ 0` exactly when
its Euclidean coordinate lies in the corresponding Euclidean disc. -/
theorem mem_ball_iff (x w : PoincareDisc) (hR : 0 ≤ R) :
    w ∈ ball x R ↔ (toUnitDisc w : ℂ) ∈
      ball (pseudoHyperbolicCenter (toUnitDisc x : ℂ) (Real.tanh R))
        (pseudoHyperbolicRadius (toUnitDisc x : ℂ) (Real.tanh R)) := by
  rw [mem_ball, dist_eq]
  exact (hyperbolicDist_lt_iff_pseudoHyperbolicExpr_lt_tanh (toUnitDisc x).norm_lt_one
    (toUnitDisc w).norm_lt_one).trans
    (pseudoHyperbolicExpr_lt_iff_mem_ball (toUnitDisc x).norm_lt_one (toUnitDisc w).norm_lt_one
      (tanh_nonneg hR) (Real.tanh_lt_one R))

end PoincareDisc

end TauCeti
