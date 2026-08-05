/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Complex.Conformal.UnitDisc.Automorphism.Basic

/-!
# Disc automorphisms are infinitesimal isometries of the Poincaré metric

The infinitesimal Schwarz--Pick inequality `norm_deriv_div_one_sub_norm_sq_le` shows that
every holomorphic self-map of the open unit disc contracts the Poincaré (hyperbolic) metric
`|dz| / (1 - |z| ^ 2)`.  This file proves that the **disc automorphisms attain equality**: for
the standard automorphism formula `z ↦ u * (z - a) / (1 - conj a * z)` (with `u` on the unit
circle and `‖a‖ < 1`),
`‖deriv f z‖ / (1 - ‖f z‖ ^ 2) = 1 / (1 - ‖z‖ ^ 2)` at every disc point `z`.  In other words
the standard automorphisms act as isometries of the Poincaré metric — the equality case of the
infinitesimal Schwarz--Pick lemma and the differential counterpart of the finite Moebius
invariance `pseudoHyperbolicExpr_unitDiscMoebius`.

The proof is a direct computation from Tau Ceti's Moebius derivative
`hasDerivAt_unitDiscMoebiusFormula` and the Pythagorean identity
`‖1 - conj a * z‖ ^ 2 - ‖z - a‖ ^ 2 = (1 - ‖z‖ ^ 2) * (1 - ‖a‖ ^ 2)`, which forces the metric
factors to cancel exactly rather than merely bound one another.

This advances the conformal-mapping roadmap's **L2 Schwarz--Pick / disc-automorphism** target
(`TauCetiRoadmap/ConformalMapping/README.md`: the hyperbolic/Poincaré metric on `𝔻` and the
automorphism group `Aut(𝔻)`).  As with the rest of the L0--L3 conformal-mapping material it is
coordinated with the upstream Mathlib RMT effort leanprover-community/mathlib4#33505 and should
be refactored to upstream API if that work lands a human-curated Schwarz--Pick theorem.
-/

public section

namespace TauCeti

open _root_.Complex Metric Set
open scoped ComplexConjugate

/-- **Value-level equality case of the infinitesimal Schwarz--Pick lemma.** The quotient built
from the Moebius derivative value `(1 - conj a * a) / (1 - conj a * z) ^ 2` and the Moebius
image `(z - a) / (1 - conj a * z)` collapses to the reciprocal Poincaré factor `1 / (1 - ‖z‖ ^ 2)`.
Both public isometry theorems below rewrite their derivative to this value and apply this
computation. -/
private lemma poincare_defect_quotient {a : ℂ} (ha : ‖a‖ < 1) {z : ℂ} (hz : ‖z‖ < 1) :
    ‖(1 - (starRingEnd ℂ) a * a) / (1 - (starRingEnd ℂ) a * z) ^ 2‖
        / (1 - ‖(z - a) / (1 - (starRingEnd ℂ) a * z)‖ ^ 2)
      = 1 / (1 - ‖z‖ ^ 2) := by
  have hden : (1 : ℂ) - (starRingEnd ℂ) a * z ≠ 0 :=
    one_sub_conj_mul_ne_zero_of_norm_lt_one hz ha
  have hD_pos : (0 : ℝ) < ‖(1 : ℂ) - (starRingEnd ℂ) a * z‖ ^ 2 :=
    pow_pos (norm_pos_iff.mpr hden) 2
  have hz_pos : (0 : ℝ) < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have ha_pos : (0 : ℝ) < 1 - ‖a‖ ^ 2 := by nlinarith [norm_nonneg a]
  -- Norm of the derivative factor: `(1 - ‖a‖ ^ 2) / ‖1 - conj a * z‖ ^ 2`.
  have hnum : ‖(1 - (starRingEnd ℂ) a * a) / (1 - (starRingEnd ℂ) a * z) ^ 2‖
      = (1 - ‖a‖ ^ 2) / ‖(1 : ℂ) - (starRingEnd ℂ) a * z‖ ^ 2 := by
    rw [norm_div, norm_pow, norm_one_sub_conj_mul_self_of_norm_le_one ha.le]
  -- Squared norm of the Moebius image.
  have hM : 1 - ‖(z - a) / (1 - (starRingEnd ℂ) a * z)‖ ^ 2
      = (1 - ‖z‖ ^ 2) * (1 - ‖a‖ ^ 2) / ‖(1 : ℂ) - (starRingEnd ℂ) a * z‖ ^ 2 := by
    rw [norm_div, div_pow, ← norm_sq_one_sub_conj_mul_sub_norm_sq_sub z a, sub_div,
      div_self hD_pos.ne']
  rw [hnum, hM]
  field_simp

/-- **The standard disc automorphism is an infinitesimal isometry of the Poincaré metric.** For a
rotation factor `u` of norm `1` and `‖a‖ < 1` the automorphism `z ↦ u * (z - a) / (1 - conj a * z)`
attains equality in the infinitesimal Schwarz--Pick inequality at every disc point: its Poincaré
metric distortion is exactly `1`.  The rotation factor `u` does not change the distortion. -/
theorem norm_deriv_div_one_sub_norm_sq_unitDiscStandardAutomorphismFormula_of_norm_lt_one
    {u : ℂ} (hu : ‖u‖ = 1) {a : ℂ} (ha : ‖a‖ < 1) {z : ℂ} (hz : ‖z‖ < 1) :
    ‖deriv (fun ξ : ℂ => u * ((ξ - a) / (1 - (starRingEnd ℂ) a * ξ))) z‖
        / (1 - ‖u * ((z - a) / (1 - (starRingEnd ℂ) a * z))‖ ^ 2)
      = 1 / (1 - ‖z‖ ^ 2) := by
  have hden : (1 : ℂ) - (starRingEnd ℂ) a * z ≠ 0 :=
    one_sub_conj_mul_ne_zero_of_norm_lt_one hz ha
  have hA := (hasDerivAt_unitDiscMoebiusFormula a z hden).const_mul u
  rw [hA.deriv, norm_mul, norm_mul, hu, one_mul, one_mul]
  exact poincare_defect_quotient ha hz

/-- **The Moebius factor is an infinitesimal isometry of the Poincaré metric.** For `‖a‖ < 1`
the disc automorphism `z ↦ (z - a) / (1 - conj a * z)` attains equality in the infinitesimal
Schwarz--Pick inequality `norm_deriv_div_one_sub_norm_sq_le`: at every point of the open unit
disc its Poincaré metric distortion is exactly `1`.  This is the `u = 1` (no rotation) case of
`norm_deriv_div_one_sub_norm_sq_unitDiscStandardAutomorphismFormula_of_norm_lt_one`. -/
theorem norm_deriv_div_one_sub_norm_sq_unitDiscMoebiusFormula_of_norm_lt_one {a : ℂ}
    (ha : ‖a‖ < 1) {z : ℂ} (hz : ‖z‖ < 1) :
    ‖deriv (fun ξ : ℂ => (ξ - a) / (1 - (starRingEnd ℂ) a * ξ)) z‖
        / (1 - ‖(z - a) / (1 - (starRingEnd ℂ) a * z)‖ ^ 2)
      = 1 / (1 - ‖z‖ ^ 2) := by
  simpa only [one_mul] using
    norm_deriv_div_one_sub_norm_sq_unitDiscStandardAutomorphismFormula_of_norm_lt_one
      norm_one ha hz

/-- Bundled unit-disc form of the automorphism Poincaré-isometry: for disc points `a z` the
standard automorphism formula centred at `a` has Poincaré metric distortion exactly `1` at `z`. -/
theorem norm_deriv_div_one_sub_norm_sq_unitDiscStandardAutomorphismFormula_unitDisc
    (u : Circle) (a z : Complex.UnitDisc) :
    ‖deriv (fun ξ : ℂ => (u : ℂ) * (((ξ : ℂ) - (a : ℂ)) /
          (1 - (starRingEnd ℂ) (a : ℂ) * ξ))) (z : ℂ)‖
        / (1 - ‖(u : ℂ) * (((z : ℂ) - (a : ℂ)) /
          (1 - (starRingEnd ℂ) (a : ℂ) * (z : ℂ)))‖ ^ 2)
      = 1 / (1 - ‖(z : ℂ)‖ ^ 2) :=
  norm_deriv_div_one_sub_norm_sq_unitDiscStandardAutomorphismFormula_of_norm_lt_one
    (Circle.norm_coe u) a.norm_lt_one z.norm_lt_one

end TauCeti
