/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.Poincare.Isometry.Equiv
public import TauCeti.Analysis.Complex.Conformal.SchwarzPick.Isometry
import TauCeti.Analysis.Complex.Isometry
public import TauCeti.Analysis.Complex.UnitDisc.Basic

/-!
# The isometries of the Poincaré disc are the disc automorphisms and their conjugates

The two objects layer **L2** of the conformal-mapping roadmap
(`TauCetiRoadmap/ConformalMapping/README.md`) asks for — "the **hyperbolic / Poincaré metric** on
`𝔻`" and "the disc automorphism group `Aut(𝔻) = {e^{iθ}(z−a)/(1−āz)}`" — are already on `main`,
and `Conformal/Poincare/MetricSpace.lean` records the one implication relating them: every
standard automorphism is a Poincaré isometry. This file proves the converse, which is what makes
`Aut(𝔻)` the *right* group for that metric:

> a map of the open unit disc into itself that preserves the hyperbolic distance is
> `z ↦ u * (z - b) / (1 - conj b * z)` or `z ↦ u * (conj z - b) / (1 - conj b * conj z)`,
> for a single `u` on the unit circle and a single `b` in the disc.

So the isometry group of the Poincaré disc is `Aut(𝔻)` together with its coset under conjugation,
the second alternative being the orientation-reversing half. Two hypotheses one might expect are
absent, and their absence is part of the statement: no holomorphy, and no surjectivity. Dropping
holomorphy is what separates this from the Schwarz--Pick rigidity of
`Conformal/SchwarzPick/Rigidity.lean`, whose
`exists_forall_unitDisc_eq_unitDiscStandardAutomorphismEquiv_of_hyperbolicDist_map_eq` assumes
`DifferentiableOn ℂ` and so can only ever reach the holomorphic half of the group; here `conj` is
admitted, and it is genuinely reached, conjugation being a hyperbolic isometry. Dropping
surjectivity is a conclusion rather than an omission: an isometric self-embedding of the Poincaré
disc is automatically onto (`TauCeti.bijOn_ball_of_hyperbolicDist_map_eq`,
`TauCeti.PoincareDisc.bijective_of_isometry`), the hyperbolic plane admitting no proper isometric
copy of itself.

## The proof

Everything is elementary once the problem is moved to the origin. Post-composing with the Moebius
factor that sends `g 0` to `0` — a hyperbolic isometry by
`TauCeti.pseudoHyperbolicExpr_unitDiscMoebiusFormula_of_norm_lt_one` — reduces to an isometry `h`
fixing `0`, and there the hyperbolic metric collapses to the Euclidean one:

* `‖h z‖ = ‖z‖`, because `pseudoHyperbolicExpr z 0` is `‖z‖`;
* `‖h z - h w‖ = ‖z - w‖` (`TauCeti.norm_sub_eq_of_pseudoHyperbolicExpr_eq`). This is the one
  computation with content. Writing `A = ‖z - w‖ ^ 2` and `B = ‖1 - conj w * z‖ ^ 2`, the Poincaré
  defect identity `TauCeti.norm_sq_one_sub_conj_mul_sub_norm_sq_sub` says `B = A + c` with
  `c = (1 - ‖z‖ ^ 2) * (1 - ‖w‖ ^ 2)`; since `c` depends only on the two norms, which `h`
  preserves, equality of the quotients `A / B` forces equality of the numerators.

That leaves a Euclidean isometry of the disc fixing `0`, and nothing hyperbolic remains in the
problem: `TauCeti/Analysis/Complex/Isometry.lean` classifies those maps as the rotations and the
rotated conjugations, so `h z = u * z` or `h z = u * conj z` for a single unit `u` — with the
alternative fixed once and for all, not chosen per point. Undoing the Moebius factor turns `u`
into the rotation and `g 0` into the centre `b`, by an explicit algebraic identity rather than by
an appeal to the group law. The polarisation step of that Euclidean classification is also
recorded here in hyperbolic language, as
`TauCeti.real_inner_map_map_of_pseudoHyperbolicExpr_map_eq`; the inner product in question is
Mathlib's own, `ℂ` carrying the `InnerProductSpace ℝ ℂ` instance with `⟪w, z⟫_ℝ = (z * conj w).re`
(`Complex.inner`), so nothing about the Euclidean plane is re-encoded here.

## Main results

* `TauCeti.real_inner_map_map_of_pseudoHyperbolicExpr_map_eq` — an isometry fixing the origin
  preserves the real inner product.
* `TauCeti.exists_norm_eq_one_eqOn_ball_const_mul_or_const_mul_conj` — the classification for an
  isometry fixing the origin: it is a rotation or a rotated conjugation.
* `TauCeti.exists_eqOn_ball_unitDiscStandardAutomorphismFormula_or_conj_of_hyperbolicDist_map_eq`
  and its pseudo-hyperbolic companion — **the classification**.
* `TauCeti.PoincareDisc.exists_eq_unitDiscStandardAutomorphismIsometryEquiv_or_comp_star` — the
  same statement for the bundled metric space `PoincareDisc` and the bundled automorphisms
  `PoincareDisc.unitDiscStandardAutomorphismIsometryEquiv`; its `Isometry`-iff form
  `PoincareDisc.isometry_iff_exists_eq_unitDiscStandardAutomorphismIsometryEquiv_or_comp_star`
  describes the isometry group itself, the conjugation entering its second alternative being
  bundled as `PoincareDisc.starIsometryEquiv` in `Isometry/Equiv.lean`.
* `TauCeti.bijOn_ball_of_forall_pseudoHyperbolicExpr_map_eq`,
  `TauCeti.bijOn_ball_of_hyperbolicDist_map_eq` and
  `TauCeti.PoincareDisc.bijective_of_isometry` — an isometric self-embedding of the Poincaré disc
  is a bijection.

## Coordination with upstream Mathlib

Mathlib has no Poincaré metric on the disc at all — its hyperbolic material lives on
`UpperHalfPlane` — so it has no classification of the isometries of one, and this file is new Lean
formalization rather than a temporary shim. The in-progress human-curated Riemann-mapping effort
[mathlib4#33505](https://github.com/leanprover-community/mathlib4/pull/33505), together with the
preceding `Analysis/Complex/RiemannMapping.lean` and `Analysis/Complex/BranchLogRoot.lean`, stops
at the mapping theorem and contains nothing of this; should a human-curated Poincaré metric and
its isometry group land upstream, this file is to be refactored onto it.

## References

* L. V. Ahlfors, *Conformal Invariants: Topics in Geometric Function Theory*, Ch. 1.
* A. F. Beardon, *The Geometry of Discrete Groups*, §7.4 (the isometries of the hyperbolic plane).
-/

public section

namespace TauCeti

open _root_.Complex Metric Set
open scoped ComplexConjugate InnerProductSpace

variable {g : ℂ → ℂ}

/-! ## Isometries of the Poincaré disc that fix the origin -/

section FixZero

variable (hg : ∀ z ∈ ball (0 : ℂ) 1, ∀ w ∈ ball (0 : ℂ) 1,
    pseudoHyperbolicExpr (g z) (g w) = pseudoHyperbolicExpr z w)

include hg

/-- **An isometry fixing the origin preserves norms.** A self-map of the open unit disc that
preserves the pseudo-hyperbolic expression and fixes `0` preserves the norm. -/
theorem norm_map_of_pseudoHyperbolicExpr_map_eq (h0 : g 0 = 0)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    ‖g z‖ = ‖z‖ := by
  -- The pseudo-hyperbolic expression against the origin is the norm.
  have := hg z hz 0 (mem_ball_self one_pos)
  rwa [h0, pseudoHyperbolicExpr_zero_right, pseudoHyperbolicExpr_zero_right] at this

/-- **An isometry fixing the origin is a Euclidean isometry.** It preserves the Euclidean
distance between any two points of the open unit disc. -/
theorem norm_sub_map_of_pseudoHyperbolicExpr_map_eq (h0 : g 0 = 0)
    {z w : ℂ} (hz : z ∈ ball (0 : ℂ) 1) (hw : w ∈ ball (0 : ℂ) 1) :
    ‖g z - g w‖ = ‖z - w‖ :=
  -- Norms are preserved, so the correction term in the Poincaré defect identity is the same on
  -- both sides.
  norm_sub_eq_of_pseudoHyperbolicExpr_eq (mem_ball_zero_iff.mp hz) (mem_ball_zero_iff.mp hw)
    (norm_map_of_pseudoHyperbolicExpr_map_eq hg h0 hz)
    (norm_map_of_pseudoHyperbolicExpr_map_eq hg h0 hw) (hg z hz w hw)

/-- The metric restatement of `TauCeti.norm_sub_map_of_pseudoHyperbolicExpr_map_eq`, which is the
shape in which the Euclidean results of `TauCeti/Analysis/Complex/Isometry.lean` take their
hypothesis. -/
private theorem dist_map_of_pseudoHyperbolicExpr_map_eq (h0 : g 0 = 0) :
    ∀ z ∈ ball (0 : ℂ) 1, ∀ w ∈ ball (0 : ℂ) 1, dist (g z) (g w) = dist z w := fun _ hz _ hw => by
  simpa only [dist_eq_norm] using norm_sub_map_of_pseudoHyperbolicExpr_map_eq hg h0 hz hw

/-- **An isometry fixing the origin preserves the real inner product.** -/
theorem real_inner_map_map_of_pseudoHyperbolicExpr_map_eq (h0 : g 0 = 0)
    {z w : ℂ} (hz : z ∈ ball (0 : ℂ) 1) (hw : w ∈ ball (0 : ℂ) 1) :
    ⟪g z, g w⟫_ℝ = ⟪z, w⟫_ℝ :=
  -- Polarisation, at the generality of a real inner product space.
  real_inner_map_map_of_dist_map_eq (mem_ball_self one_pos) h0
    (dist_map_of_pseudoHyperbolicExpr_map_eq hg h0) hz hw

end FixZero

/-- **Isometries fixing the origin are rotations and rotated conjugations.** A self-map of the
open unit disc that preserves the pseudo-hyperbolic expression and fixes `0` is `z ↦ u * z` or
`z ↦ u * conj z` for a single unit `u`.

The hyperbolic hypothesis has already done its work at
`TauCeti.norm_sub_map_of_pseudoHyperbolicExpr_map_eq`: what is left is a Euclidean isometry of the
disc fixing its centre, which
`TauCeti.exists_norm_eq_one_eqOn_ball_const_mul_or_const_mul_conj_of_dist_map_eq` classifies. -/
theorem exists_norm_eq_one_eqOn_ball_const_mul_or_const_mul_conj
    (hg : ∀ z ∈ ball (0 : ℂ) 1, ∀ w ∈ ball (0 : ℂ) 1,
      pseudoHyperbolicExpr (g z) (g w) = pseudoHyperbolicExpr z w)
    (h0 : g 0 = 0) :
    ∃ u : ℂ, ‖u‖ = 1 ∧
      (EqOn g (fun z => u * z) (ball (0 : ℂ) 1) ∨
        EqOn g (fun z => u * conj z) (ball (0 : ℂ) 1)) :=
  exists_norm_eq_one_eqOn_ball_const_mul_or_const_mul_conj_of_dist_map_eq one_pos h0
    (dist_map_of_pseudoHyperbolicExpr_map_eq hg h0)

/-! ## The classification -/

/-- Undoing the normalising Moebius factor: for a unit `u`, the map
`w ↦ (u * w + a) / (1 + conj a * (u * w))` is the standard automorphism with rotation `u` and
centre `-a * conj u`. -/
private lemma const_mul_add_div_eq_unitDiscStandardAutomorphismFormula {a u : ℂ} (hu : ‖u‖ = 1)
    (w : ℂ) :
    (u * w + a) / (1 + conj a * (u * w))
      = u * ((w - -a * conj u) / (1 - conj (-a * conj u) * w)) := by
  have hmul : u * conj u = 1 := by rw [Complex.mul_conj', hu]; norm_num
  have hden : (1 : ℂ) - conj (-a * conj u) * w = 1 + conj a * (u * w) := by
    rw [map_mul, map_neg, Complex.conj_conj]; ring
  have hnum : u * (w - -a * conj u) = u * w + a := by
    have h : u * (w - -a * conj u) = u * w + a * (u * conj u) := by ring
    rw [h, hmul, mul_one]
  rw [hden, ← mul_div_assoc, hnum]

/-- **The isometries of the Poincaré disc, pseudo-hyperbolic form.** A self-map of the open unit
disc preserving the pseudo-hyperbolic expression is a standard disc automorphism
`z ↦ u * (z - b) / (1 - conj b * z)` or the conjugate of one. Neither holomorphy nor surjectivity
is assumed. -/
theorem exists_eqOn_ball_unitDiscStandardAutomorphismFormula_or_conj_of_pseudoHyperbolicExpr_map_eq
    (hmaps : MapsTo g (ball (0 : ℂ) 1) (ball (0 : ℂ) 1))
    (hg : ∀ z ∈ ball (0 : ℂ) 1, ∀ w ∈ ball (0 : ℂ) 1,
      pseudoHyperbolicExpr (g z) (g w) = pseudoHyperbolicExpr z w) :
    ∃ u b : ℂ, ‖u‖ = 1 ∧ ‖b‖ < 1 ∧
      (EqOn g (fun z => u * ((z - b) / (1 - conj b * z))) (ball (0 : ℂ) 1) ∨
        EqOn g (fun z => u * ((conj z - b) / (1 - conj b * conj z))) (ball (0 : ℂ) 1)) := by
  have ha : ‖g 0‖ < 1 := mem_ball_zero_iff.mp (hmaps (mem_ball_self one_pos))
  -- Normalise: post-composing with the Moebius factor at `g 0` fixes the origin.
  have hczero : (g 0 - g 0) / (1 - conj (g 0) * g 0) = 0 := by rw [sub_self, zero_div]
  have hciso : ∀ z ∈ ball (0 : ℂ) 1, ∀ w ∈ ball (0 : ℂ) 1,
      pseudoHyperbolicExpr ((g z - g 0) / (1 - conj (g 0) * g z))
          ((g w - g 0) / (1 - conj (g 0) * g w))
        = pseudoHyperbolicExpr z w := by
    intro z hz w hw
    rw [pseudoHyperbolicExpr_unitDiscMoebiusFormula_of_norm_lt_one ha (hmaps hz) (hmaps hw)]
    exact hg z hz w hw
  obtain ⟨u, hu, hcase⟩ :=
    exists_norm_eq_one_eqOn_ball_const_mul_or_const_mul_conj hciso hczero
  refine ⟨u, -g 0 * conj u, hu, ?_, ?_⟩
  · rw [norm_mul, norm_neg, Complex.norm_conj, hu, mul_one]; exact ha
  · -- Undo the normalisation, using that the Moebius factor at `-g 0` inverts it.
    rcases hcase with hcase | hcase
    · left
      intro z hz
      have hz1 : (g z - g 0) / (1 - conj (g 0) * g z) = u * z := hcase hz
      have hinv := leftInvOn_unitDiscMoebiusFormula_of_norm_lt_one ha (hmaps hz)
      -- Beta-reduce the scalar Moebius formulas so that `hz1` rewrites `hinv`.
      dsimp only at hinv
      rw [hz1] at hinv
      simp only [map_neg, neg_mul, sub_neg_eq_add] at hinv
      rw [← hinv]
      exact const_mul_add_div_eq_unitDiscStandardAutomorphismFormula hu z
    · right
      intro z hz
      have hz1 : (g z - g 0) / (1 - conj (g 0) * g z) = u * conj z := hcase hz
      have hinv := leftInvOn_unitDiscMoebiusFormula_of_norm_lt_one ha (hmaps hz)
      -- Beta-reduce the scalar Moebius formulas so that `hz1` rewrites `hinv`.
      dsimp only at hinv
      rw [hz1] at hinv
      simp only [map_neg, neg_mul, sub_neg_eq_add] at hinv
      rw [← hinv]
      exact const_mul_add_div_eq_unitDiscStandardAutomorphismFormula hu (conj z)

/-- **The isometries of the Poincaré disc.** A self-map of the open unit disc preserving the
hyperbolic distance is a standard disc automorphism `z ↦ u * (z - b) / (1 - conj b * z)` or the
conjugate of one: the isometry group of the Poincaré metric is `Aut(𝔻)` together with its
orientation-reversing coset. -/
theorem exists_eqOn_ball_unitDiscStandardAutomorphismFormula_or_conj_of_hyperbolicDist_map_eq
    (hmaps : MapsTo g (ball (0 : ℂ) 1) (ball (0 : ℂ) 1))
    (hg : ∀ z ∈ ball (0 : ℂ) 1, ∀ w ∈ ball (0 : ℂ) 1,
      hyperbolicDist (g z) (g w) = hyperbolicDist z w) :
    ∃ u b : ℂ, ‖u‖ = 1 ∧ ‖b‖ < 1 ∧
      (EqOn g (fun z => u * ((z - b) / (1 - conj b * z))) (ball (0 : ℂ) 1) ∨
        EqOn g (fun z => u * ((conj z - b) / (1 - conj b * conj z))) (ball (0 : ℂ) 1)) :=
  exists_eqOn_ball_unitDiscStandardAutomorphismFormula_or_conj_of_pseudoHyperbolicExpr_map_eq
    hmaps fun z hz w hw =>
      (pseudoHyperbolicExpr_eq_iff_hyperbolicDist_eq (hmaps hz) (hmaps hw) hz hw).mpr
        (hg z hz w hw)

/-! ## Isometric self-embeddings are onto -/

/-- A standard disc automorphism maps the open unit disc onto itself: it is the scalar formula of
the bundled equivalence `TauCeti.unitDiscStandardAutomorphismEquiv`. -/
private lemma surjOn_ball_unitDiscStandardAutomorphismFormula {u b : ℂ} (hu : ‖u‖ = 1)
    (hb : ‖b‖ < 1) :
    SurjOn (fun z : ℂ => u * ((z - b) / (1 - conj b * z))) (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) := by
  -- Name the rotation as an element of `Circle`, rather than leaving the anonymous constructor
  -- with its `Submonoid.unitSphere` membership proof in the goal.
  obtain ⟨c, hc⟩ : ∃ c : Circle, (c : ℂ) = u := ⟨⟨u, mem_sphere_zero_iff_norm.2 hu⟩, rfl⟩
  refine (bijOn_ball_of_unitDiscEquiv
    (unitDiscStandardAutomorphismEquiv c (Complex.UnitDisc.mk b hb)) fun z => ?_).surjOn
  rw [coe_unitDiscStandardAutomorphismEquiv_apply, Complex.UnitDisc.coe_mk, hc]

/-- **An isometric self-embedding of the Poincaré disc is onto, pseudo-hyperbolic form.** A
self-map of the open unit disc preserving the pseudo-hyperbolic expression is a bijection of the
disc onto itself: the hyperbolic plane contains no proper isometric copy of itself. The companion
statement for a holomorphic self-map of the disc preserving it at a single pair of *distinct*
points is `TauCeti.bijOn_ball_of_pseudoHyperbolicExpr_map_eq`, from Schwarz--Pick rigidity. -/
theorem bijOn_ball_of_forall_pseudoHyperbolicExpr_map_eq
    (hmaps : MapsTo g (ball (0 : ℂ) 1) (ball (0 : ℂ) 1))
    (hg : ∀ z ∈ ball (0 : ℂ) 1, ∀ w ∈ ball (0 : ℂ) 1,
      pseudoHyperbolicExpr (g z) (g w) = pseudoHyperbolicExpr z w) :
    BijOn g (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) := by
  have hinj : InjOn g (ball (0 : ℂ) 1) := by
    intro z hz w hw hzw
    have hd := hg z hz w hw
    rw [hzw, pseudoHyperbolicExpr_eq_zero_of_eq rfl] at hd
    exact (pseudoHyperbolicExpr_eq_zero_iff_of_mem_ball hz hw).mp hd.symm
  obtain ⟨u, b, hu, hb, hcase⟩ :=
    exists_eqOn_ball_unitDiscStandardAutomorphismFormula_or_conj_of_pseudoHyperbolicExpr_map_eq
      hmaps hg
  refine ⟨hmaps, hinj, ?_⟩
  rcases hcase with hcase | hcase
  · intro y hy
    obtain ⟨z, hz, hzy⟩ := surjOn_ball_unitDiscStandardAutomorphismFormula hu hb hy
    exact ⟨z, hz, by rw [hcase hz]; exact hzy⟩
  · intro y hy
    obtain ⟨z, hz, hzy⟩ := surjOn_ball_unitDiscStandardAutomorphismFormula hu hb hy
    have hcz : conj z ∈ ball (0 : ℂ) 1 := by
      rw [mem_ball_zero_iff, Complex.norm_conj]; exact mem_ball_zero_iff.mp hz
    refine ⟨conj z, hcz, ?_⟩
    rw [hcase hcz]
    simpa only [Complex.conj_conj] using hzy

/-- **An isometric self-embedding of the Poincaré disc is onto.** A self-map of the open unit disc
preserving the hyperbolic distance is a bijection of the disc onto itself. -/
theorem bijOn_ball_of_hyperbolicDist_map_eq
    (hmaps : MapsTo g (ball (0 : ℂ) 1) (ball (0 : ℂ) 1))
    (hg : ∀ z ∈ ball (0 : ℂ) 1, ∀ w ∈ ball (0 : ℂ) 1,
      hyperbolicDist (g z) (g w) = hyperbolicDist z w) :
    BijOn g (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) :=
  bijOn_ball_of_forall_pseudoHyperbolicExpr_map_eq hmaps fun z hz w hw =>
    (pseudoHyperbolicExpr_eq_iff_hyperbolicDist_eq (hmaps hz) (hmaps hw) hz hw).mpr
      (hg z hz w hw)

namespace PoincareDisc

/-- **The scalar representative of an isometry of the Poincaré disc.** Every isometry `f` of
`PoincareDisc` is carried by a self-map `F` of the open unit ball that preserves the hyperbolic
distance on the ball and represents `f` in the coordinate `toUnitDisc`. -/
private lemma exists_mapsTo_ball_and_hyperbolicDist_map_eq_of_isometry
    {f : PoincareDisc → PoincareDisc} (hf : Isometry f) :
    ∃ F : ℂ → ℂ, MapsTo F (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) ∧
      (∀ z ∈ ball (0 : ℂ) 1, ∀ w ∈ ball (0 : ℂ) 1,
        hyperbolicDist (F z) (F w) = hyperbolicDist z w) ∧
      ∀ z : PoincareDisc, F (toUnitDisc z : ℂ) = (toUnitDisc (f z) : ℂ) := by
  classical
  -- the representative is `0` off the ball; the first two conclusions restrict to the ball and
  -- the third is only ever applied at `toUnitDisc z`, which is a disc point
  refine ⟨fun z => if h : ‖z‖ < 1 then
    ((toUnitDisc (f (Complex.UnitDisc.toPoincare (Complex.UnitDisc.mk z h)))) : ℂ) else 0, ?_, ?_,
    ?_⟩
  · refine mapsTo_ball_of_forall_unitDisc_coe_eq
      (e := fun z => toUnitDisc (f (Complex.UnitDisc.toPoincare z))) fun z => ?_
    rw [dite_eq_left z.norm_lt_one, Complex.UnitDisc.mk_coe]
  · intro z hz w hw
    have hz' := mem_ball_zero_iff.mp hz
    have hw' := mem_ball_zero_iff.mp hw
    have hdist := hf.dist_eq (Complex.UnitDisc.toPoincare (Complex.UnitDisc.mk z hz'))
      (Complex.UnitDisc.toPoincare (Complex.UnitDisc.mk w hw'))
    dsimp only
    rw [dite_eq_left hz', dite_eq_left hw']
    simpa only [dist_eq, toUnitDisc_toPoincare, Complex.UnitDisc.coe_mk] using hdist
  · intro z
    dsimp only
    rw [dite_eq_left (toUnitDisc z).norm_lt_one, Complex.UnitDisc.mk_coe, toPoincare_toUnitDisc]

/-- **The isometries of the Poincaré disc, bundled form.** Every isometry of the metric space
`PoincareDisc` is a standard disc automorphism `unitDiscStandardAutomorphismIsometryEquiv u a`,
or that automorphism precomposed with the conjugation `starIsometryEquiv`: the isometry group of
`PoincareDisc` is `Aut(𝔻)` together with its orientation-reversing coset. The converse is
`PoincareDisc.isometry_iff_exists_eq_unitDiscStandardAutomorphismIsometryEquiv_or_comp_star`. -/
theorem exists_eq_unitDiscStandardAutomorphismIsometryEquiv_or_comp_star
    {f : PoincareDisc → PoincareDisc} (hf : Isometry f) :
    ∃ (u : Circle) (a : Complex.UnitDisc),
      (∀ z, f z = unitDiscStandardAutomorphismIsometryEquiv u a z) ∨
        (∀ z, f z = unitDiscStandardAutomorphismIsometryEquiv u a (starIsometryEquiv z)) := by
  -- the scalar representative of `f`, to which the scalar classification applies
  obtain ⟨F, hFmaps, hFiso, hFz⟩ := exists_mapsTo_ball_and_hyperbolicDist_map_eq_of_isometry hf
  obtain ⟨u, b, hu, hb, hcase⟩ :=
    exists_eqOn_ball_unitDiscStandardAutomorphismFormula_or_conj_of_hyperbolicDist_map_eq
      hFmaps hFiso
  -- Name the rotation as an element of `Circle` and the centre as a point of the bundled disc.
  obtain ⟨c, hc⟩ : ∃ c : Circle, (c : ℂ) = u := ⟨⟨u, mem_sphere_zero_iff_norm.2 hu⟩, rfl⟩
  refine ⟨c, Complex.UnitDisc.mk b hb, ?_⟩
  rcases hcase with hcase | hcase
  · refine Or.inl fun z => toUnitDisc.injective (Complex.UnitDisc.coe_injective ?_)
    rw [unitDiscStandardAutomorphismIsometryEquiv_apply, toUnitDisc_toPoincare,
      coe_unitDiscStandardAutomorphismEquiv_apply, Complex.UnitDisc.coe_mk, hc, ← hFz z]
    exact hcase (coe_mem_ball z)
  · refine Or.inr fun z => toUnitDisc.injective (Complex.UnitDisc.coe_injective ?_)
    rw [starIsometryEquiv_apply, unitDiscStandardAutomorphismIsometryEquiv_apply,
      toUnitDisc_toPoincare, coe_unitDiscStandardAutomorphismEquiv_apply,
      Complex.UnitDisc.coe_mk, hc, toUnitDisc_toPoincare, Complex.UnitDisc.coe_star, ← hFz z]
    exact hcase (coe_mem_ball z)

/-- **The isometry group of the Poincaré disc.** A self-map of `PoincareDisc` is an isometry if
and only if it is a standard disc automorphism `unitDiscStandardAutomorphismIsometryEquiv u a` or
that automorphism precomposed with the conjugation `starIsometryEquiv`. The forward direction is
the classification `exists_eq_unitDiscStandardAutomorphismIsometryEquiv_or_comp_star`; the
converse holds because both factors are isometric equivalences. -/
theorem isometry_iff_exists_eq_unitDiscStandardAutomorphismIsometryEquiv_or_comp_star
    {f : PoincareDisc → PoincareDisc} :
    Isometry f ↔ ∃ (u : Circle) (a : Complex.UnitDisc),
      (∀ z, f z = unitDiscStandardAutomorphismIsometryEquiv u a z) ∨
        (∀ z, f z = unitDiscStandardAutomorphismIsometryEquiv u a (starIsometryEquiv z)) := by
  refine ⟨exists_eq_unitDiscStandardAutomorphismIsometryEquiv_or_comp_star, ?_⟩
  rintro ⟨u, a, hcase | hcase⟩
  · exact funext hcase ▸ (unitDiscStandardAutomorphismIsometryEquiv u a).isometry
  · exact funext hcase ▸
      (unitDiscStandardAutomorphismIsometryEquiv u a).isometry.comp starIsometryEquiv.isometry

/-- **Every isometry of the Poincaré disc is a bijection.** Injectivity comes with any `Isometry`;
surjectivity is the content, and it is read off the classification: both a standard automorphism
and the conjugation are bijections. -/
theorem bijective_of_isometry {f : PoincareDisc → PoincareDisc} (hf : Isometry f) :
    Function.Bijective f := by
  obtain ⟨u, a, hcase | hcase⟩ :=
    exists_eq_unitDiscStandardAutomorphismIsometryEquiv_or_comp_star hf
  · exact funext hcase ▸ (unitDiscStandardAutomorphismIsometryEquiv u a).bijective
  · exact funext hcase ▸
      (unitDiscStandardAutomorphismIsometryEquiv u a).bijective.comp starIsometryEquiv.bijective

end PoincareDisc

end TauCeti
