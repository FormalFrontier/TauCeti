/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.Poincare.MetricSpace
public import TauCeti.Analysis.Complex.Conformal.SchwarzPick.Isometry
public import TauCeti.Analysis.Complex.Conformal.UnitDisc.Automorphism.Group
public import Mathlib.Analysis.InnerProductSpace.Basic

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

A Euclidean isometry of the disc fixing `0` preserves the real inner product by polarisation
(`TauCeti.real_inner_map_eq_of_pseudoHyperbolicExpr_map_eq`, proved from Mathlib's
`norm_sub_sq_real`) — the inner product in question is
Mathlib's own, `ℂ` carrying the `InnerProductSpace ℝ ℂ` instance with `⟪w, z⟫_ℝ = (z * conj w).re`
(`Complex.inner`), so nothing about the Euclidean plane is re-encoded here. Two evaluations then
pin the map down: the images of `1 / 2` and of `I / 2`, doubled, are orthogonal unit vectors
`e₁, e₂`, so `e₂ = e₁ * I` or `e₂ = e₁ * (-I)`, while `⟪e₁, h z⟫_ℝ = z.re` and
`⟪e₂, h z⟫_ℝ = z.im` read off the coordinates of `h z` in that orthonormal frame. Hence
`h z = e₁ * z` or `h z = e₁ * conj z` — with the alternative fixed once and for all, not chosen
per point. Undoing the Moebius factor turns `e₁` into the rotation `u` and `g 0` into the centre
`b`, by an explicit algebraic identity rather than by an appeal to the group law.

## Main results

* `TauCeti.real_inner_map_eq_of_pseudoHyperbolicExpr_map_eq` — an isometry fixing the origin
  preserves the real inner product.
* `TauCeti.exists_norm_eq_one_eqOn_ball_const_mul_or_const_mul_conj` — the classification for an
  isometry fixing the origin: it is a rotation or a rotated conjugation.
* `TauCeti.exists_eqOn_ball_unitDiscStandardAutomorphismFormula_or_conj_of_hyperbolicDist_map_eq`
  and its pseudo-hyperbolic companion — **the classification**.
* `TauCeti.bijOn_ball_of_hyperbolicDist_map_eq` and
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

/-! ## Real-inner-product bookkeeping

`ℂ` is a real inner product space in Mathlib (`InnerProductSpace ℝ ℂ`, with
`Complex.inner : ⟪w, z⟫_ℝ = (z * conj w).re`), and that is the inner product used throughout. The
four lemmas here only translate between it and the coordinates `Complex.re`, `Complex.im` in which
the frame argument below reads off a point.
-/

/-- The real inner product of `ℂ`, viewed as the Euclidean plane, in coordinates. -/
private lemma real_inner_eq (z w : ℂ) : ⟪z, w⟫_ℝ = z.re * w.re + z.im * w.im := by
  simp only [Complex.inner, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- The real part of `conj z * w` is the real inner product of `z` and `w`. -/
private lemma re_conj_mul (z w : ℂ) : (conj z * w).re = ⟪z, w⟫_ℝ := by
  simp only [Complex.inner, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- The imaginary part of `conj z * w` is the real inner product of `w` with the quarter turn of
`z`: the two coordinates of `conj z * w` are the coordinates of `w` in the frame `z`, `z * I`. -/
private lemma im_conj_mul (z w : ℂ) : (conj z * w).im = ⟪z * I, w⟫_ℝ := by
  simp only [Complex.inner, map_mul, Complex.conj_I, Complex.mul_re, Complex.mul_im,
    Complex.conj_re, Complex.conj_im, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im]
  ring

/-- Doubling the left argument of the real inner product doubles it. -/
private lemma real_inner_two_mul_left (z w : ℂ) : ⟪(2 : ℂ) * z, w⟫_ℝ = 2 * ⟪z, w⟫_ℝ := by
  have h : (2 : ℂ) * z = z + z := by ring
  rw [h, inner_add_left]
  ring

/-- Doubling the right argument of the real inner product doubles it. -/
private lemma real_inner_two_mul_right (z w : ℂ) : ⟪z, (2 : ℂ) * w⟫_ℝ = 2 * ⟪z, w⟫_ℝ := by
  have h : (2 : ℂ) * w = w + w := by ring
  rw [h, inner_add_right]
  ring

/-- A complex number of norm one times its conjugate is one. -/
private lemma mul_conj_self_eq_one {u : ℂ} (hu : ‖u‖ = 1) : u * conj u = 1 := by
  have h : Complex.normSq u = 1 := by rw [Complex.normSq_eq_norm_sq, hu]; norm_num
  rw [Complex.mul_conj, h, Complex.ofReal_one]

/-! ## Isometries of the Poincaré disc that fix the origin -/

section FixZero

variable (hg : ∀ z ∈ ball (0 : ℂ) 1, ∀ w ∈ ball (0 : ℂ) 1,
    pseudoHyperbolicExpr (g z) (g w) = pseudoHyperbolicExpr z w)

include hg

/-- **An isometry fixing the origin preserves norms.** A self-map of the open unit disc that
preserves the pseudo-hyperbolic expression and fixes `0` preserves the norm. -/
theorem norm_map_eq_of_pseudoHyperbolicExpr_map_eq (h0 : g 0 = 0)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    ‖g z‖ = ‖z‖ := by
  -- The pseudo-hyperbolic expression against the origin is the norm.
  have := hg z hz 0 (mem_ball_self one_pos)
  rwa [h0, pseudoHyperbolicExpr_zero_right, pseudoHyperbolicExpr_zero_right] at this

/-- **An isometry fixing the origin is a Euclidean isometry.** It preserves the Euclidean
distance between any two points of the open unit disc. -/
theorem norm_sub_map_eq_of_pseudoHyperbolicExpr_map_eq (h0 : g 0 = 0)
    {z w : ℂ} (hz : z ∈ ball (0 : ℂ) 1) (hw : w ∈ ball (0 : ℂ) 1) :
    ‖g z - g w‖ = ‖z - w‖ :=
  -- Norms are preserved, so the correction term in the Poincaré defect identity is the same on
  -- both sides.
  norm_sub_eq_of_pseudoHyperbolicExpr_eq (mem_ball_zero_iff.mp hz) (mem_ball_zero_iff.mp hw)
    (norm_map_eq_of_pseudoHyperbolicExpr_map_eq hg h0 hz)
    (norm_map_eq_of_pseudoHyperbolicExpr_map_eq hg h0 hw) (hg z hz w hw)

/-- **An isometry fixing the origin preserves the real inner product.** -/
theorem real_inner_map_eq_of_pseudoHyperbolicExpr_map_eq (h0 : g 0 = 0)
    {z w : ℂ} (hz : z ∈ ball (0 : ℂ) 1) (hw : w ∈ ball (0 : ℂ) 1) :
    ⟪g z, g w⟫_ℝ = ⟪z, w⟫_ℝ := by
  -- Polarisation: the inner product is determined by the three norms `‖z‖`, `‖w‖`, `‖z - w‖`.
  have hnz := norm_map_eq_of_pseudoHyperbolicExpr_map_eq hg h0 hz
  have hnw := norm_map_eq_of_pseudoHyperbolicExpr_map_eq hg h0 hw
  have hsub := norm_sub_map_eq_of_pseudoHyperbolicExpr_map_eq hg h0 hz hw
  have h1 := norm_sub_sq_real (g z) (g w)
  have h2 := norm_sub_sq_real z w
  rw [hsub, hnz, hnw] at h1
  linarith

end FixZero

/-- Two unit complex numbers with vanishing real inner product differ by a quarter turn. -/
private lemma eq_mul_I_or_eq_neg_mul_I {e₁ e₂ : ℂ} (h₁ : ‖e₁‖ = 1) (h₂ : ‖e₂‖ = 1)
    (h : ⟪e₁, e₂⟫_ℝ = 0) : e₂ = e₁ * I ∨ e₂ = e₁ * (-I) := by
  have hmul : e₁ * conj e₁ = 1 := mul_conj_self_eq_one h₁
  have hrecover : e₁ * (conj e₁ * e₂) = e₂ := by rw [← mul_assoc, hmul, one_mul]
  have hre : (conj e₁ * e₂).re = 0 := by rw [re_conj_mul, h]
  have hnorm : ‖conj e₁ * e₂‖ = 1 := by rw [norm_mul, Complex.norm_conj, h₁, h₂, one_mul]
  have hsq : (conj e₁ * e₂).im ^ 2 = 1 := by
    have hns : Complex.normSq (conj e₁ * e₂) = 1 := by
      rw [Complex.normSq_eq_norm_sq, hnorm]; norm_num
    rw [Complex.normSq_apply, hre] at hns
    nlinarith [hns]
  have him : (conj e₁ * e₂).im = 1 ∨ (conj e₁ * e₂).im = -1 := by
    have hfac : ((conj e₁ * e₂).im - 1) * ((conj e₁ * e₂).im + 1) = 0 := by nlinarith [hsq]
    rcases mul_eq_zero.mp hfac with h' | h'
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  rcases him with h' | h'
  · refine Or.inl ?_
    have hI : conj e₁ * e₂ = I := by apply Complex.ext <;> simp [hre, h']
    rw [← hrecover, hI]
  · refine Or.inr ?_
    have hI : conj e₁ * e₂ = -I := by apply Complex.ext <;> simp [hre, h']
    rw [← hrecover, hI]

/-- **Isometries fixing the origin are rotations and rotated conjugations.** A self-map of the
open unit disc that preserves the pseudo-hyperbolic expression and fixes `0` is `z ↦ u * z` or
`z ↦ u * conj z` for a single unit `u`. -/
theorem exists_norm_eq_one_eqOn_ball_const_mul_or_const_mul_conj
    (hg : ∀ z ∈ ball (0 : ℂ) 1, ∀ w ∈ ball (0 : ℂ) 1,
      pseudoHyperbolicExpr (g z) (g w) = pseudoHyperbolicExpr z w)
    (h0 : g 0 = 0) :
    ∃ u : ℂ, ‖u‖ = 1 ∧
      (EqOn g (fun z => u * z) (ball (0 : ℂ) 1) ∨
        EqOn g (fun z => u * conj z) (ball (0 : ℂ) 1)) := by
  set p : ℂ := ((1 / 2 : ℝ) : ℂ) with hp_def
  set q : ℂ := I * ((1 / 2 : ℝ) : ℂ) with hq_def
  have hnp : ‖p‖ = 1 / 2 := by rw [hp_def, Complex.norm_real]; norm_num
  have hnq : ‖q‖ = 1 / 2 := by
    rw [hq_def, norm_mul, Complex.norm_I, one_mul, Complex.norm_real]
    norm_num
  have hp : p ∈ ball (0 : ℂ) 1 := by rw [mem_ball_zero_iff, hnp]; norm_num
  have hq : q ∈ ball (0 : ℂ) 1 := by rw [mem_ball_zero_iff, hnq]; norm_num
  set e₁ : ℂ := 2 * g p with he₁_def
  set e₂ : ℂ := 2 * g q with he₂_def
  have hn₁ : ‖e₁‖ = 1 := by
    rw [he₁_def, norm_mul, norm_map_eq_of_pseudoHyperbolicExpr_map_eq hg h0 hp, hnp,
      RCLike.norm_two]
    norm_num
  have hn₂ : ‖e₂‖ = 1 := by
    rw [he₂_def, norm_mul, norm_map_eq_of_pseudoHyperbolicExpr_map_eq hg h0 hq, hnq,
      RCLike.norm_two]
    norm_num
  have hmul₁ : e₁ * conj e₁ = 1 := mul_conj_self_eq_one hn₁
  -- The frame is orthonormal.
  have horth : ⟪e₁, e₂⟫_ℝ = 0 := by
    rw [he₁_def, he₂_def, real_inner_two_mul_left, real_inner_two_mul_right,
      real_inner_map_eq_of_pseudoHyperbolicExpr_map_eq hg h0 hp hq, real_inner_eq]
    simp only [hp_def, hq_def, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
  -- The frame reads off the coordinates of `g z`.
  have hcoord₁ : ∀ z ∈ ball (0 : ℂ) 1, ⟪e₁, g z⟫_ℝ = z.re := by
    intro z hz
    rw [he₁_def, real_inner_two_mul_left,
      real_inner_map_eq_of_pseudoHyperbolicExpr_map_eq hg h0 hp hz, real_inner_eq]
    simp only [hp_def, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hcoord₂ : ∀ z ∈ ball (0 : ℂ) 1, ⟪e₂, g z⟫_ℝ = z.im := by
    intro z hz
    rw [he₂_def, real_inner_two_mul_left,
      real_inner_map_eq_of_pseudoHyperbolicExpr_map_eq hg h0 hq hz, real_inner_eq]
    simp only [hq_def, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hre : ∀ z ∈ ball (0 : ℂ) 1, (conj e₁ * g z).re = z.re := fun z hz => by
    rw [re_conj_mul]; exact hcoord₁ z hz
  refine ⟨e₁, hn₁, ?_⟩
  rcases eq_mul_I_or_eq_neg_mul_I hn₁ hn₂ horth with hcase | hcase
  · left
    intro z hz
    have him : (conj e₁ * g z).im = z.im := by
      rw [im_conj_mul, ← hcase]
      exact hcoord₂ z hz
    have hxi : conj e₁ * g z = z := Complex.ext (hre z hz) him
    calc g z = e₁ * (conj e₁ * g z) := by rw [← mul_assoc, hmul₁, one_mul]
      _ = e₁ * z := by rw [hxi]
  · right
    intro z hz
    have him : (conj e₁ * g z).im = -z.im := by
      have h2 := hcoord₂ z hz
      rw [hcase, real_inner_eq] at h2
      rw [im_conj_mul, real_inner_eq]
      simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.neg_re,
        Complex.neg_im] at h2 ⊢
      linarith
    have hxi : conj e₁ * g z = conj z := by
      apply Complex.ext
      · rw [Complex.conj_re]; exact hre z hz
      · rw [Complex.conj_im]; exact him
    calc g z = e₁ * (conj e₁ * g z) := by rw [← mul_assoc, hmul₁, one_mul]
      _ = e₁ * conj z := by rw [hxi]

/-! ## The classification -/

/-- Undoing the normalising Moebius factor: for a unit `u`, the map
`w ↦ (u * w + a) / (1 + conj a * (u * w))` is the standard automorphism with rotation `u` and
centre `-a * conj u`. -/
private lemma const_mul_add_div_eq_unitDiscStandardAutomorphismFormula {a u : ℂ} (hu : ‖u‖ = 1)
    (w : ℂ) :
    (u * w + a) / (1 + conj a * (u * w))
      = u * ((w - -a * conj u) / (1 - conj (-a * conj u) * w)) := by
  have hmul : u * conj u = 1 := mul_conj_self_eq_one hu
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
  have hmul : u * conj u = 1 := mul_conj_self_eq_one hu
  refine ⟨u, -g 0 * conj u, hu, ?_, ?_⟩
  · rw [norm_mul, norm_neg, Complex.norm_conj, hu, mul_one]; exact ha
  · -- Undo the normalisation, using that the Moebius factor at `-g 0` inverts it.
    rcases hcase with hcase | hcase
    · left
      intro z hz
      have hz1 : (g z - g 0) / (1 - conj (g 0) * g z) = u * z := hcase hz
      have hinv := leftInvOn_unitDiscMoebiusFormula_of_norm_lt_one ha (hmaps hz)
      simp only at hinv
      rw [hz1] at hinv
      simp only [map_neg, neg_mul, sub_neg_eq_add] at hinv
      rw [← hinv]
      exact const_mul_add_div_eq_unitDiscStandardAutomorphismFormula hu z
    · right
      intro z hz
      have hz1 : (g z - g 0) / (1 - conj (g 0) * g z) = u * conj z := hcase hz
      have hinv := leftInvOn_unitDiscMoebiusFormula_of_norm_lt_one ha (hmaps hz)
      simp only at hinv
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

/-- **An isometric self-embedding of the Poincaré disc is onto.** A self-map of the open unit disc
preserving the hyperbolic distance is a bijection of the disc onto itself: the hyperbolic plane
contains no proper isometric copy of itself. -/
theorem bijOn_ball_of_hyperbolicDist_map_eq
    (hmaps : MapsTo g (ball (0 : ℂ) 1) (ball (0 : ℂ) 1))
    (hg : ∀ z ∈ ball (0 : ℂ) 1, ∀ w ∈ ball (0 : ℂ) 1,
      hyperbolicDist (g z) (g w) = hyperbolicDist z w) :
    BijOn g (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) := by
  have hinj : InjOn g (ball (0 : ℂ) 1) := by
    intro z hz w hw hzw
    have hd := hg z hz w hw
    rw [hzw, hyperbolicDist_self] at hd
    exact (hyperbolicDist_eq_zero_iff_of_mem_ball hz hw).mp hd.symm
  obtain ⟨u, b, hu, hb, hcase⟩ :=
    exists_eqOn_ball_unitDiscStandardAutomorphismFormula_or_conj_of_hyperbolicDist_map_eq hmaps hg
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

namespace PoincareDisc

/-- **Every isometry of the Poincaré disc is a bijection.** Injectivity comes with any `Isometry`;
surjectivity is the content. -/
theorem bijective_of_isometry {f : PoincareDisc → PoincareDisc} (hf : Isometry f) :
    Function.Bijective f := by
  classical
  set F : ℂ → ℂ := fun z =>
    if h : ‖z‖ < 1 then
      ((toUnitDisc (f (Complex.UnitDisc.toPoincare (Complex.UnitDisc.mk z h)))) : ℂ)
    else 0 with hF_def
  have hFval : ∀ (z : ℂ) (h : ‖z‖ < 1),
      F z = ((toUnitDisc (f (Complex.UnitDisc.toPoincare (Complex.UnitDisc.mk z h)))) : ℂ) := by
    intro z h
    rw [hF_def]
    simp only [dif_pos h]
  have hFmaps : MapsTo F (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) := by
    intro z hz
    rw [hFval z (mem_ball_zero_iff.mp hz), mem_ball_zero_iff]
    exact Complex.UnitDisc.norm_lt_one _
  have hFiso : ∀ z ∈ ball (0 : ℂ) 1, ∀ w ∈ ball (0 : ℂ) 1,
      hyperbolicDist (F z) (F w) = hyperbolicDist z w := by
    intro z hz w hw
    have hz' := mem_ball_zero_iff.mp hz
    have hw' := mem_ball_zero_iff.mp hw
    have hdist := hf.dist_eq (Complex.UnitDisc.toPoincare (Complex.UnitDisc.mk z hz'))
      (Complex.UnitDisc.toPoincare (Complex.UnitDisc.mk w hw'))
    rw [hFval z hz', hFval w hw']
    simpa only [dist_eq, toUnitDisc_toPoincare, Complex.UnitDisc.coe_mk] using hdist
  have hbij := bijOn_ball_of_hyperbolicDist_map_eq hFmaps hFiso
  refine ⟨hf.injective, fun y => ?_⟩
  obtain ⟨z, hz, hzy⟩ := hbij.surjOn (coe_mem_ball y)
  refine ⟨Complex.UnitDisc.toPoincare (Complex.UnitDisc.mk z (mem_ball_zero_iff.mp hz)), ?_⟩
  rw [hFval z (mem_ball_zero_iff.mp hz)] at hzy
  exact toUnitDisc.injective (Complex.UnitDisc.coe_injective hzy)

end PoincareDisc

end TauCeti
