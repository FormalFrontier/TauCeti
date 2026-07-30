/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Complex.Conformal.Poincare.MetricSpace
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# The Poincaré disc carries the Euclidean topology and is a proper metric space

`Poincare/MetricSpace.lean` equips the type synonym `TauCeti.PoincareDisc` of
`Complex.UnitDisc` with the hyperbolic (Poincaré) distance `TauCeti.hyperbolicDist` as a
`MetricSpace` instance. That instance says nothing yet about how the resulting topology
compares with the Euclidean subspace topology of the disc, nor whether the metric is complete.
This file settles both.

The comparison rests on two elementary estimates for the pseudo-hyperbolic expression
`p = pseudoHyperbolicExpr z w = ‖(z - w) / (1 - conj w * z)‖`, of which the hyperbolic distance
is the reparametrisation `Real.artanh p`:

* the Moebius denominator has norm at most `2` on the disc, so `‖z - w‖ ≤ 2 * p`, which makes
  the identity map from the Poincaré disc to the Euclidean disc Lipschitz-like near the
  diagonal;
* `p` depends continuously on `(z, w)` and `Real.artanh` is continuous on `(-1, 1)`, so the
  hyperbolic distance is jointly continuous for the Euclidean topology.

Properness comes from a compact exhaustion: a closed hyperbolic ball around `x` of radius `r`
is contained in the closed Euclidean disc of radius `Real.tanh (r + hyperbolicDist x 0)`, whose
radius is strictly less than one, so it is a closed subset of a compact subset of the open disc.

## Main declarations

* `TauCeti.continuousOn_hyperbolicDist` — the hyperbolic distance is jointly continuous on
  `ball 0 1 ×ˢ ball 0 1`.
* `TauCeti.norm_sub_le_two_mul_pseudoHyperbolicExpr` — the Euclidean distance of two disc
  points is at most twice their pseudo-hyperbolic expression.
* `TauCeti.hyperbolicDist_zero_le_iff_norm_le_tanh` — the closed hyperbolic ball about the
  origin of radius `r` is the closed Euclidean ball of radius `Real.tanh r`.
* `TauCeti.PoincareDisc.toUnitDiscHomeomorph` — the identification of the Poincaré disc with
  `Complex.UnitDisc` is a homeomorphism; the `simp` lemmas `toUnitDiscHomeomorph_apply` and
  `toUnitDiscHomeomorph_symm_apply` characterise both directions, so consumers never need to
  unfold the definition, whose body is deliberately not exposed.
* `TauCeti.PoincareDisc.instProperSpace` — the Poincaré disc is a proper metric space, hence
  complete and locally compact.

This carries the conformal-mapping roadmap's L2 target "the hyperbolic / Poincaré metric on
`𝔻`" (see `ConformalMapping/README.md`) onto its topological side: with the homeomorphism in
hand, the hyperbolic metric may be used interchangeably with the Euclidean one for topological
purposes, and completeness is what makes the Poincaré disc a usable model of the hyperbolic
plane. It reuses Tau Ceti's pseudo-hyperbolic and hyperbolic-distance API. As with the rest of
the L0--L3 conformal-mapping material, it is coordinated with the upstream Mathlib Riemann
mapping effort leanprover-community/mathlib4#33505 and should be refactored to upstream API if
that work lands a human-curated Poincaré metric. Mathlib already contains the preceding
human-curated work in `Analysis/Complex/RiemannMapping.lean` and
`Analysis/Complex/BranchLogRoot.lean`; this file duplicates none of their branch-logarithm and
root API, adding only the topological side of the hyperbolic metric. Mathlib has the hyperbolic
metric on the upper half-plane (`Analysis/Complex/UpperHalfPlane`), but no Poincaré metric on
the disc.
-/

public section

namespace TauCeti

open Complex Metric Set
open scoped ComplexConjugate Topology

/-! ### Continuity of the inverse hyperbolic tangent -/

/-- `Real.artanh` is continuous on the interval `(-1, 1)` on which it inverts `Real.tanh`.

Mathlib's `Analysis/SpecialFunctions/Artanh.lean` proves the monotonicity and inversion
properties of `Real.artanh` but records no continuity statement. This is a local proof helper
for `continuousOn_hyperbolicDist`, kept private so that a general real-analysis fact is not
exported from a file about the Poincaré metric. -/
private lemma continuousOn_artanh : ContinuousOn Real.artanh (Ioo (-1 : ℝ) 1) := by
  have hpos : ∀ x ∈ Ioo (-1 : ℝ) 1, (0 : ℝ) < (1 + x) / (1 - x) := fun x hx =>
    div_pos (by linarith [hx.1]) (by linarith [hx.2])
  have hcont : ContinuousOn (fun x : ℝ => 1 / 2 * Real.log ((1 + x) / (1 - x)))
      (Ioo (-1 : ℝ) 1) := by
    refine continuousOn_const.mul (ContinuousOn.log ?_ fun x hx => (hpos x hx).ne')
    exact (continuousOn_const.add continuousOn_id).div (continuousOn_const.sub continuousOn_id)
      fun x hx => by have : (0 : ℝ) < 1 - x := by linarith [hx.2]
                     exact this.ne'
  exact hcont.congr fun x hx => Real.artanh_eq_half_log (Ioo_subset_Icc_self hx)

/-! ### Comparison of the Euclidean and pseudo-hyperbolic distances -/

/-- The Euclidean distance between two points of the open unit disc is at most twice their
pseudo-hyperbolic expression: the Moebius denominator `1 - conj w * z` has norm at most `2`. -/
lemma norm_sub_le_two_mul_pseudoHyperbolicExpr {z w : ℂ} (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) :
    ‖z - w‖ ≤ 2 * pseudoHyperbolicExpr z w := by
  have hden : (1 : ℂ) - (starRingEnd ℂ) w * z ≠ 0 :=
    one_sub_conj_mul_ne_zero_of_norm_lt_one hz hw
  have hle : ‖(1 : ℂ) - (starRingEnd ℂ) w * z‖ ≤ 2 := by
    calc ‖(1 : ℂ) - (starRingEnd ℂ) w * z‖ ≤ ‖(1 : ℂ)‖ + ‖(starRingEnd ℂ) w * z‖ :=
          norm_sub_le _ _
      _ = 1 + ‖w‖ * ‖z‖ := by rw [norm_one, norm_mul, RCLike.norm_conj]
      _ ≤ 2 := by nlinarith [norm_nonneg z, norm_nonneg w]
  have hfac : pseudoHyperbolicExpr z w * ‖(1 : ℂ) - (starRingEnd ℂ) w * z‖ = ‖z - w‖ := by
    rw [pseudoHyperbolicExpr_def, norm_div, div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hden)]
  nlinarith [pseudoHyperbolicExpr_nonneg z w]

/-! ### Joint continuity of the hyperbolic distance -/

/-- The pseudo-hyperbolic expression is continuous on the product of two copies of the open
unit disc, where its Moebius denominator does not vanish. -/
lemma continuousOn_pseudoHyperbolicExpr :
    ContinuousOn (fun p : ℂ × ℂ => pseudoHyperbolicExpr p.1 p.2)
      (ball (0 : ℂ) 1 ×ˢ ball (0 : ℂ) 1) := by
  have hnum : Continuous fun p : ℂ × ℂ => p.1 - p.2 := continuous_fst.sub continuous_snd
  have hden : Continuous fun p : ℂ × ℂ => (1 : ℂ) - (starRingEnd ℂ) p.2 * p.1 :=
    continuous_const.sub ((Complex.continuous_conj.comp continuous_snd).mul continuous_fst)
  have hne : ∀ p ∈ ball (0 : ℂ) 1 ×ˢ ball (0 : ℂ) 1,
      (1 : ℂ) - (starRingEnd ℂ) p.2 * p.1 ≠ 0 := fun _ hp =>
    one_sub_conj_mul_ne_zero_of_mem_ball hp.1 hp.2
  exact ((hnum.continuousOn.div hden.continuousOn hne).norm).congr fun p _ =>
    pseudoHyperbolicExpr_def p.1 p.2

/-- The hyperbolic distance is jointly continuous on the product of two copies of the open unit
disc, for the Euclidean topology of `ℂ`. -/
lemma continuousOn_hyperbolicDist :
    ContinuousOn (fun p : ℂ × ℂ => hyperbolicDist p.1 p.2)
      (ball (0 : ℂ) 1 ×ˢ ball (0 : ℂ) 1) := by
  refine ContinuousOn.congr (continuousOn_artanh.comp continuousOn_pseudoHyperbolicExpr
    fun p hp => ⟨by linarith [pseudoHyperbolicExpr_nonneg p.1 p.2],
      pseudoHyperbolicExpr_lt_one_of_mem_ball hp.1 hp.2⟩) fun p _ => hyperbolicDist_def p.1 p.2

/-- For a fixed base point, the hyperbolic distance is a continuous function on
`Complex.UnitDisc` with its Euclidean subspace topology. -/
lemma continuous_hyperbolicDist_unitDisc (w : Complex.UnitDisc) :
    Continuous fun z : Complex.UnitDisc => hyperbolicDist (z : ℂ) (w : ℂ) :=
  continuousOn_hyperbolicDist.comp_continuous
    (Complex.UnitDisc.continuous_coe.prodMk continuous_const) fun z =>
      ⟨mem_ball_zero_iff.mpr z.norm_lt_one, mem_ball_zero_iff.mpr w.norm_lt_one⟩

/-! ### Hyperbolic balls about the origin -/

/-- A point of the open unit disc lies within hyperbolic distance `r` of the origin exactly when
its Euclidean norm is at most `Real.tanh r`: the closed hyperbolic ball about the origin is the
closed Euclidean ball of radius `Real.tanh r`. -/
lemma hyperbolicDist_zero_le_iff_norm_le_tanh {z : ℂ} (hz : ‖z‖ < 1) (r : ℝ) :
    hyperbolicDist z 0 ≤ r ↔ ‖z‖ ≤ Real.tanh r := by
  have hz' : (-1 : ℝ) < ‖z‖ := by linarith [norm_nonneg z]
  rw [hyperbolicDist_zero_right]
  constructor
  · intro h
    refine (Real.artanh_le_artanh_iff ⟨hz', hz⟩
      ⟨Real.neg_one_lt_tanh r, Real.tanh_lt_one r⟩).mp ?_
    rwa [Real.artanh_tanh]
  · intro h
    have := Real.artanh_le_artanh hz' (Real.tanh_lt_one r) h
    rwa [Real.artanh_tanh] at this

/-! ### The Poincaré disc is homeomorphic to the Euclidean disc -/

namespace PoincareDisc

/-- The identity map from the Poincaré disc to `Complex.UnitDisc` is continuous: two points at
small hyperbolic distance are at small Euclidean distance, since `‖z - w‖ ≤ 2 * p` while the
hyperbolic distance is the increasing reparametrisation `Real.artanh p`. -/
theorem continuous_toUnitDisc :
    Continuous (toUnitDisc : PoincareDisc → Complex.UnitDisc) := by
  rw [Complex.UnitDisc.isEmbedding_coe.isInducing.continuous_iff, Metric.continuous_iff]
  intro b ε hε
  obtain ⟨c, hc0, hc1, hcε⟩ : ∃ c : ℝ, 0 < c ∧ c < 1 ∧ 2 * c < ε :=
    ⟨min (ε / 4) (1 / 2), lt_min (by linarith) (by norm_num),
      lt_of_le_of_lt (min_le_right _ _) (by norm_num),
      by have := min_le_left (ε / 4) (1 / 2); linarith⟩
  refine ⟨Real.artanh c, Real.artanh_pos (Set.mem_Ioo.mpr ⟨hc0, hc1⟩), fun a hab => ?_⟩
  have hp0 : 0 ≤ pseudoHyperbolicExpr (toUnitDisc a : ℂ) (toUnitDisc b : ℂ) :=
    pseudoHyperbolicExpr_nonneg _ _
  have hp1 : pseudoHyperbolicExpr (toUnitDisc a : ℂ) (toUnitDisc b : ℂ) < 1 :=
    pseudoHyperbolicExpr_lt_one_unitDisc _ _
  rw [PoincareDisc.dist_eq, hyperbolicDist_def] at hab
  have hlt : pseudoHyperbolicExpr (toUnitDisc a : ℂ) (toUnitDisc b : ℂ) < c :=
    (Real.artanh_lt_artanh_iff (Set.mem_Ioo.mpr ⟨by linarith, hp1⟩)
      (Set.mem_Ioo.mpr ⟨by linarith, hc1⟩)).mp hab
  have hbound := norm_sub_le_two_mul_pseudoHyperbolicExpr (toUnitDisc a).norm_lt_one
    (toUnitDisc b).norm_lt_one
  simp only [Function.comp_apply, dist_eq_norm]
  linarith

/-- The identity map from `Complex.UnitDisc` to the Poincaré disc is continuous, because the
hyperbolic distance to a fixed point is a continuous function for the Euclidean topology and
vanishes at that point. -/
theorem _root_.Complex.UnitDisc.continuous_toPoincare :
    Continuous (Complex.UnitDisc.toPoincare : Complex.UnitDisc → PoincareDisc) := by
  refine continuous_iff_continuousAt.mpr fun b => Metric.tendsto_nhds.mpr fun ε hε => ?_
  have h := (continuous_hyperbolicDist_unitDisc b).tendsto b
  rw [hyperbolicDist_self] at h
  simpa only [dist_eq, toUnitDisc_toPoincare] using h.eventually_lt_const hε

/-- **The Poincaré disc carries the Euclidean topology.** The identification of the Poincaré
disc with `Complex.UnitDisc` is a homeomorphism, so the hyperbolic metric may be used
interchangeably with the Euclidean one for topological purposes.

The body is not exposed: the two `simp` lemmas below characterise both directions, so consumers
never depend on how the homeomorphism is assembled. -/
def toUnitDiscHomeomorph : PoincareDisc ≃ₜ Complex.UnitDisc where
  toEquiv := toUnitDisc
  continuous_toFun := continuous_toUnitDisc
  continuous_invFun := Complex.UnitDisc.continuous_toPoincare

-- The parenthesised `(rfl)` proofs elaborate against the unexposed body, which a bare `rfl`
-- in an exported theorem may not do.

/-- The homeomorphism acts as the identification `PoincareDisc.toUnitDisc`. -/
@[simp]
lemma toUnitDiscHomeomorph_apply (z : PoincareDisc) :
    toUnitDiscHomeomorph z = toUnitDisc z := (rfl)

/-- The inverse homeomorphism acts as the identification `Complex.UnitDisc.toPoincare`. -/
@[simp]
lemma toUnitDiscHomeomorph_symm_apply (z : Complex.UnitDisc) :
    toUnitDiscHomeomorph.symm z = Complex.UnitDisc.toPoincare z := (rfl)

end PoincareDisc

/-! ### Properness of the Poincaré metric -/

/-- **The Poincaré disc is a proper metric space.** A closed hyperbolic ball of radius `r` about
`x` consists of points at hyperbolic distance at most `r + hyperbolicDist x 0` from the origin,
hence of Euclidean norm at most `Real.tanh (r + hyperbolicDist x 0) < 1`; it is therefore a
closed subset of a compact subset of the open disc.

Concretely, every bounded hyperbolic ball is contained in a Euclidean subdisc of radius strictly
less than one. Together with the instances Mathlib derives from `ProperSpace`, this makes the
Poincaré disc a complete and locally compact metric space. -/
instance PoincareDisc.instProperSpace : ProperSpace PoincareDisc where
  isCompact_closedBall x r := by
    have hsub : PoincareDisc.toUnitDiscHomeomorph '' closedBall x r ⊆
        {z : Complex.UnitDisc |
          ‖(z : ℂ)‖ ≤ Real.tanh (r + dist x (Complex.UnitDisc.toPoincare 0))} := by
      rintro _ ⟨z, hz, rfl⟩
      simp only [Set.mem_setOf_eq, PoincareDisc.toUnitDiscHomeomorph_apply]
      have htri : dist z (Complex.UnitDisc.toPoincare 0)
          ≤ r + dist x (Complex.UnitDisc.toPoincare 0) := by
        have hzx : dist z x ≤ r := mem_closedBall.mp hz
        linarith [dist_triangle z x (Complex.UnitDisc.toPoincare 0)]
      have hzero : hyperbolicDist ((PoincareDisc.toUnitDisc z : ℂ)) 0
          ≤ r + dist x (Complex.UnitDisc.toPoincare 0) := by
        simpa only [PoincareDisc.dist_eq, PoincareDisc.toUnitDisc_toPoincare,
          Complex.UnitDisc.coe_zero] using htri
      exact (hyperbolicDist_zero_le_iff_norm_le_tanh (PoincareDisc.toUnitDisc z).norm_lt_one _).mp
        hzero
    have hclosed : IsClosed (PoincareDisc.toUnitDiscHomeomorph '' closedBall x r) :=
      (Homeomorph.isClosed_image _).mpr isClosed_closedBall
    have hcpt : IsCompact (PoincareDisc.toUnitDiscHomeomorph '' closedBall x r) :=
      IsCompact.of_isClosed_subset
        (Complex.UnitDisc.isCompact_setOf_norm_le (Real.tanh_lt_one _)) hclosed hsub
    exact (Homeomorph.isCompact_image _).mp hcpt

/-! ### Completeness and local compactness

Mathlib derives `CompleteSpace` and `LocallyCompactSpace` from `ProperSpace`; we record that
those instances are indeed found for the Poincaré disc. -/

example : CompleteSpace PoincareDisc := inferInstance

example : LocallyCompactSpace PoincareDisc := inferInstance

end TauCeti
