/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Complex.Conformal.SchwarzPick.AutomorphismIsometry
public import TauCeti.Analysis.Complex.Conformal.SchwarzPick.Derivative.Basic
public import TauCeti.Analysis.Complex.Conformal.SchwarzPick.Rigidity
import Mathlib.Analysis.Complex.Schwarz

/-!
# Rigidity in the infinitesimal Schwarz--Pick inequality

The infinitesimal Schwarz--Pick inequality `TauCeti.norm_deriv_div_one_sub_norm_sq_le` says a
holomorphic self-map `f` of the open unit disc contracts the Poincaré metric
`|dz| / (1 - |z| ^ 2)`: at every disc point `z`,
`‖deriv f z‖ / (1 - ‖f z‖ ^ 2) ≤ 1 / (1 - ‖z‖ ^ 2)`.  One direction of its equality case is
already on `main`: the standard disc automorphisms attain equality everywhere
(`TauCeti.norm_deriv_div_one_sub_norm_sq_unitDiscStandardAutomorphismFormula_of_norm_lt_one`).
This file proves the converse, and hence the equivalence:

> equality at a *single* disc point forces `f` to be a standard disc automorphism
> `ζ ↦ u * (ζ - b) / (1 - conj b * ζ)`, and so to attain equality at *every* point.

So the holomorphic self-maps of the disc that are infinitesimal isometries of the Poincaré
metric somewhere are exactly those that are infinitesimal isometries everywhere, namely the
automorphisms — the differential counterpart of the finite rigidity statement
`TauCeti.exists_forall_unitDisc_eq_unitDiscStandardAutomorphismEquiv_of_pseudoHyperbolicExpr_map_eq`
in `SchwarzPick/Rigidity.lean`.

## The argument

Everything is read off the Schwarz--Pick conjugate `g = schwarzPickConjugate f a`, the self-map
of the disc obtained by conjugating `f` by the Moebius factors that send `a` to `0` on the
source and `f a` to `0` on the target.  Its derivative at the origin is computed by
`TauCeti.hasDerivAt_schwarzPickConjugate_zero`, and in norm it is exactly the Poincaré
distortion of `f` at `a`; so the hypothesis says `‖deriv g 0‖ = 1`, which is the equality case
of Schwarz's lemma for the origin-fixing map `g`.  Mathlib's
`Complex.affine_of_mapsTo_ball_of_norm_dslope_eq_div` — applied at `c = z₀ = 0`, where
`dslope g 0 0` is `deriv g 0` — then makes `g` the rotation `ζ ↦ deriv g 0 * ζ`.

Taking norms in that identity at the Moebius image of a disc point `z` gives the *finite*
Schwarz--Pick equality `pseudoHyperbolicExpr (f z) (f a) = pseudoHyperbolicExpr z a`, for every
`z` at once.  Feeding one instance of it with `z ≠ a` into the finite rigidity of
`SchwarzPick/Rigidity.lean` yields the classification and the bijectivity; a witness for `z ≠ a`
is `(a + 1) / 2`, which lies in the disc because `‖a + 1‖ < 2` and differs from `a` because
`a = 1` is impossible.  The reverse implication of the equivalence is the automorphism
computation of `SchwarzPick/AutomorphismIsometry.lean`, transported along the equality of `f`
with the automorphism formula on the disc — an open set, so the two derivatives agree.

## The fixed-point form

At a *fixed* point of `f` the two Poincaré defects in
`TauCeti.hasDerivAt_schwarzPickConjugate_zero` cancel, so `deriv g 0` is `deriv f a` on the
nose rather than merely in norm.  The classical Schwarz lemma at an interior fixed point falls
out: `‖deriv f a‖ ≤ 1`, with equality forcing `f` to be the *hyperbolic rotation* about `a` by
the argument of `deriv f a`, in the explicit Moebius-conjugate form
`(f z - a) / (1 - conj a * f z) = deriv f a * ((z - a) / (1 - conj a * z))`.  Specialising the
rotation factor to `1` recovers the identity, which is the one-fixed-point sharpening of
`TauCeti.eqOn_id_of_isFixedPt_of_isFixedPt` of `SchwarzPick/FixedPoint.lean`: there two fixed
points are assumed, here one fixed point and a derivative condition.

## Main results

* `TauCeti.pseudoHyperbolicExpr_map_eq_of_norm_deriv_div_one_sub_norm_sq_eq` — infinitesimal
  equality at `a` gives finite Schwarz--Pick equality at every pair `(z, a)`.
* `TauCeti.forall_pseudoHyperbolicExpr_map_eq_of_norm_deriv_div_one_sub_norm_sq_eq` — hence `f`
  preserves the pseudo-hyperbolic expression on the whole disc.
* `TauCeti.bijOn_ball_of_norm_deriv_div_one_sub_norm_sq_eq` — `f` is a bijection of the disc.
* `TauCeti.norm_deriv_div_one_sub_norm_sq_eq_iff` — **the equality case**: infinitesimal
  equality at one point holds if and only if `f` is a standard disc automorphism, with the
  bundled `Complex.UnitDisc` form `TauCeti.norm_deriv_div_one_sub_norm_sq_eq_iff_unitDisc`.
* `TauCeti.forall_norm_deriv_div_one_sub_norm_sq_eq_of_norm_deriv_div_one_sub_norm_sq_eq` —
  equality at one point propagates to every point, with the bundled `Complex.UnitDisc` form
  `TauCeti.forall_norm_deriv_div_one_sub_norm_sq_eq_of_norm_deriv_div_one_sub_norm_sq_eq_unitDisc`.
* `TauCeti.norm_deriv_le_one_of_isFixedPt` — **the Schwarz lemma at an interior fixed point**.
* `TauCeti.unitDiscMoebiusFormula_map_eq_mul_of_isFixedPt_of_norm_deriv_eq_one` — its equality
  case: `f` is the hyperbolic rotation about the fixed point.
* `TauCeti.eqOn_id_of_isFixedPt_of_deriv_eq_one` — a fixed point with derivative `1` forces the
  identity.

This advances the conformal-mapping roadmap's **L2 Schwarz--Pick** target
(`TauCetiRoadmap/ConformalMapping/README.md`), completing the equality case of the
infinitesimal estimate that `SchwarzPick/Derivative/Basic.lean` proved and
`SchwarzPick/AutomorphismIsometry.lean` proved sharp.  It reuses Mathlib's equality case of the
Schwarz lemma and Tau Ceti's Schwarz--Pick conjugate, finite rigidity and disc-automorphism API
rather than re-deriving any of them.  As with the rest of the L0--L3 conformal-mapping
material, it is coordinated with the upstream Mathlib Riemann-mapping effort
leanprover-community/mathlib4#33505, whose preceding human-curated work in
`Analysis/Complex/RiemannMapping.lean` and `Analysis/Complex/BranchLogRoot.lean` contains no
Schwarz--Pick rigidity; should a human-curated version land upstream, these statements are to
be backed by it, or deleted with their consumers refactored onto it.

## References

* L. Ahlfors, *Conformal Invariants*, Ch. 1 (the invariant form of Schwarz's lemma).
* J. B. Garnett, *Bounded Analytic Functions*, Ch. I §1.
-/

public section

namespace TauCeti

open _root_.Complex Metric Set
open scoped ComplexConjugate

variable {f : ℂ → ℂ} {a : ℂ}

/-- At a point where the infinitesimal Schwarz--Pick inequality is an equality, the Schwarz--Pick
conjugate has a derivative of norm `1` at the origin: the two Poincaré defects rescale
`‖deriv f a‖` to exactly `1`.  This is the hypothesis of the equality case of Schwarz's lemma
for the origin-fixing conjugate. -/
private lemma norm_deriv_schwarzPickConjugate_zero_eq_one
    (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (hmaps : MapsTo f (ball (0 : ℂ) 1) (ball (0 : ℂ) 1)) (ha : a ∈ ball (0 : ℂ) 1)
    (heq : ‖deriv f a‖ / (1 - ‖f a‖ ^ 2) = 1 / (1 - ‖a‖ ^ 2)) :
    ‖deriv (schwarzPickConjugate f a) 0‖ = 1 := by
  have ha1 : ‖a‖ < 1 := by simpa [mem_ball_zero_iff] using ha
  have hfa1 : ‖f a‖ < 1 := by simpa [mem_ball_zero_iff] using hmaps ha
  have hden_a : (0 : ℝ) < 1 - ‖a‖ ^ 2 := by nlinarith [norm_nonneg a]
  have hden_fa : (0 : ℝ) < 1 - ‖f a‖ ^ 2 := by nlinarith [norm_nonneg (f a)]
  have hf_at : HasDerivAt f (deriv f a) a :=
    (hf.differentiableAt (isOpen_ball.mem_nhds ha)).hasDerivAt
  rw [div_eq_div_iff hden_fa.ne' hden_a.ne', one_mul] at heq
  rw [norm_deriv_schwarzPickConjugate_zero ha1 hfa1 hf_at, div_eq_one_iff_eq hden_fa.ne', heq]

/-- Under the same hypothesis the Schwarz--Pick conjugate **is** the rotation
`ζ ↦ deriv (schwarzPickConjugate f a) 0 * ζ` on the whole disc: it fixes the origin and its
derivative there has norm `1`, so Mathlib's equality case of the Schwarz lemma applies to it. -/
private lemma eqOn_schwarzPickConjugate_mul
    (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (hmaps : MapsTo f (ball (0 : ℂ) 1) (ball (0 : ℂ) 1)) (ha : a ∈ ball (0 : ℂ) 1)
    (heq : ‖deriv f a‖ / (1 - ‖f a‖ ^ 2) = 1 / (1 - ‖a‖ ^ 2)) :
    EqOn (schwarzPickConjugate f a)
      (fun ζ => deriv (schwarzPickConjugate f a) 0 * ζ) (ball (0 : ℂ) 1) := by
  have ha1 : ‖a‖ < 1 := by simpa [mem_ball_zero_iff] using ha
  obtain ⟨hg_diff, hg_maps, hg_zero⟩ :=
    differentiableOn_and_mapsTo_ball_and_apply_zero_schwarzPickConjugate hf hmaps ha1
  have hg_closed : MapsTo (schwarzPickConjugate f a) (ball (0 : ℂ) 1)
      (closedBall (schwarzPickConjugate f a 0) 1) := by
    rw [hg_zero]; exact fun ξ hξ => ball_subset_closedBall (hg_maps hξ)
  have hdslope : ‖dslope (schwarzPickConjugate f a) 0 0‖ = 1 / 1 := by
    rw [dslope_same, div_one]
    exact norm_deriv_schwarzPickConjugate_zero_eq_one hf hmaps ha heq
  have haffine := Complex.affine_of_mapsTo_ball_of_norm_dslope_eq_div hg_diff hg_closed
    (mem_ball_self one_pos) hdslope
  intro ζ hζ
  simpa [hg_zero, dslope_same, mul_comm] using haffine hζ

/-- **Infinitesimal Schwarz--Pick rigidity, finite form.**  If a holomorphic self-map of the
open unit disc attains equality in the infinitesimal Schwarz--Pick inequality at one point `a`,
then it attains equality in the *finite* Schwarz--Pick estimate at every pair `(z, a)`: it
preserves the pseudo-hyperbolic expression to `a`. -/
theorem pseudoHyperbolicExpr_map_eq_of_norm_deriv_div_one_sub_norm_sq_eq
    (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (hmaps : MapsTo f (ball (0 : ℂ) 1) (ball (0 : ℂ) 1)) (ha : a ∈ ball (0 : ℂ) 1)
    (heq : ‖deriv f a‖ / (1 - ‖f a‖ ^ 2) = 1 / (1 - ‖a‖ ^ 2))
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    pseudoHyperbolicExpr (f z) (f a) = pseudoHyperbolicExpr z a := by
  have ha1 : ‖a‖ < 1 := by simpa [mem_ball_zero_iff] using ha
  have hz1 : ‖z‖ < 1 := by simpa [mem_ball_zero_iff] using hz
  have hξ : (z - a) / (1 - (starRingEnd ℂ) a * z) ∈ ball (0 : ℂ) 1 :=
    mapsTo_ball_unitDiscMoebiusFormula_of_norm_lt_one ha1 hz
  calc
    pseudoHyperbolicExpr (f z) (f a)
        = ‖schwarzPickConjugate f a ((z - a) / (1 - (starRingEnd ℂ) a * z))‖ := by
      rw [schwarzPickConjugate_apply_unitDiscMoebiusFormula ha1 hz1, pseudoHyperbolicExpr_def]
    _ = ‖deriv (schwarzPickConjugate f a) 0‖ * ‖(z - a) / (1 - (starRingEnd ℂ) a * z)‖ := by
      rw [eqOn_schwarzPickConjugate_mul hf hmaps ha heq hξ, norm_mul]
    _ = pseudoHyperbolicExpr z a := by
      rw [norm_deriv_schwarzPickConjugate_zero_eq_one hf hmaps ha heq, one_mul,
        pseudoHyperbolicExpr_def]

/-- A disc point distinct from a prescribed one: the midpoint of `a` and `1` lies in the open
unit disc, since `‖a + 1‖ < 2`, and it differs from `a`, since `a = 1` is impossible there.
This supplies the "distinct pair" hypothesis of the finite rigidity statements. -/
private lemma exists_mem_ball_ne (ha : a ∈ ball (0 : ℂ) 1) :
    ∃ z ∈ ball (0 : ℂ) 1, z ≠ a := by
  have ha1 : ‖a‖ < 1 := by simpa [mem_ball_zero_iff] using ha
  refine ⟨(a + 1) / 2, ?_, ?_⟩
  · have : ‖(a + 1) / 2‖ ≤ (‖a‖ + 1) / 2 := by
      rw [norm_div, Complex.norm_two]
      gcongr
      simpa using norm_add_le a 1
    simp only [mem_ball_zero_iff]
    linarith
  · intro hcontra
    have h1 : a = 1 := by
      field_simp at hcontra
      linear_combination -hcontra
    rw [h1] at ha1
    simp at ha1

/-- **Infinitesimal Schwarz--Pick rigidity, isometry form.**  Equality in the infinitesimal
Schwarz--Pick inequality at a single point makes `f` a pseudo-hyperbolic isometry of the whole
disc. -/
theorem forall_pseudoHyperbolicExpr_map_eq_of_norm_deriv_div_one_sub_norm_sq_eq
    (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (hmaps : MapsTo f (ball (0 : ℂ) 1) (ball (0 : ℂ) 1)) (ha : a ∈ ball (0 : ℂ) 1)
    (heq : ‖deriv f a‖ / (1 - ‖f a‖ ^ 2) = 1 / (1 - ‖a‖ ^ 2)) :
    ∀ p ∈ ball (0 : ℂ) 1, ∀ q ∈ ball (0 : ℂ) 1,
      pseudoHyperbolicExpr (f p) (f q) = pseudoHyperbolicExpr p q := by
  obtain ⟨z, hz, hne⟩ := exists_mem_ball_ne ha
  exact forall_pseudoHyperbolicExpr_map_eq_of_pseudoHyperbolicExpr_map_eq hf hmaps hz ha hne
    (pseudoHyperbolicExpr_map_eq_of_norm_deriv_div_one_sub_norm_sq_eq hf hmaps ha heq hz)

/-- **Infinitesimal Schwarz--Pick rigidity, bijectivity form.**  A holomorphic self-map of the
open unit disc that attains equality in the infinitesimal Schwarz--Pick inequality at one point
is a bijection of the disc, hence a conformal automorphism. -/
theorem bijOn_ball_of_norm_deriv_div_one_sub_norm_sq_eq
    (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (hmaps : MapsTo f (ball (0 : ℂ) 1) (ball (0 : ℂ) 1)) (ha : a ∈ ball (0 : ℂ) 1)
    (heq : ‖deriv f a‖ / (1 - ‖f a‖ ^ 2) = 1 / (1 - ‖a‖ ^ 2)) :
    BijOn f (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) := by
  obtain ⟨z, hz, hne⟩ := exists_mem_ball_ne ha
  exact bijOn_ball_of_pseudoHyperbolicExpr_map_eq hf hmaps hz ha hne
    (pseudoHyperbolicExpr_map_eq_of_norm_deriv_div_one_sub_norm_sq_eq hf hmaps ha heq hz)

/-- **The equality case of the infinitesimal Schwarz--Pick inequality.**  A holomorphic self-map
of the open unit disc attains equality in the infinitesimal Schwarz--Pick inequality at a point
`a` — that is, it is an infinitesimal isometry of the Poincaré metric at `a` — if and only if it
is one of the standard disc automorphisms `ζ ↦ u * (ζ - b) / (1 - conj b * ζ)`.

The `mpr` direction is the automorphism computation of
`SchwarzPick/AutomorphismIsometry.lean`, transported along the equality of `f` with the
automorphism formula on the disc, which is open. -/
theorem norm_deriv_div_one_sub_norm_sq_eq_iff
    (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (hmaps : MapsTo f (ball (0 : ℂ) 1) (ball (0 : ℂ) 1)) (ha : a ∈ ball (0 : ℂ) 1) :
    ‖deriv f a‖ / (1 - ‖f a‖ ^ 2) = 1 / (1 - ‖a‖ ^ 2) ↔
      ∃ (u : Circle) (b : Complex.UnitDisc),
        ∀ ζ : Complex.UnitDisc, f ζ = (unitDiscStandardAutomorphismEquiv u b ζ : ℂ) := by
  have ha1 : ‖a‖ < 1 := by simpa [mem_ball_zero_iff] using ha
  refine ⟨fun heq => ?_, ?_⟩
  · obtain ⟨z, hz, hne⟩ := exists_mem_ball_ne ha
    exact exists_forall_unitDisc_eq_unitDiscStandardAutomorphismEquiv_of_pseudoHyperbolicExpr_map_eq
      hf hmaps hz ha hne
      (pseudoHyperbolicExpr_map_eq_of_norm_deriv_div_one_sub_norm_sq_eq hf hmaps ha heq hz)
  rintro ⟨u, b, hfb⟩
  -- `f` agrees with the automorphism formula on the disc, an open set, so also in derivative.
  set F : ℂ → ℂ :=
    fun ξ => (u : ℂ) * ((ξ - (b : ℂ)) / (1 - (starRingEnd ℂ) (b : ℂ) * ξ)) with hF
  have hEq : EqOn f F (ball (0 : ℂ) 1) := by
    intro ζ hζ
    have hζ1 : ‖ζ‖ < 1 := by simpa [mem_ball_zero_iff] using hζ
    simpa [hF, Complex.UnitDisc.coe_mk] using hfb (Complex.UnitDisc.mk ζ hζ1)
  have hderiv : deriv f a = deriv F a :=
    Filter.EventuallyEq.deriv_eq (Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds ha) hEq)
  rw [hderiv, hEq ha, hF]
  exact norm_deriv_div_one_sub_norm_sq_unitDiscStandardAutomorphismFormula_of_norm_lt_one
    (Circle.norm_coe u) b.norm_lt_one ha1

/-- Bundled unit-disc form of the equality case of the infinitesimal Schwarz--Pick inequality: a
holomorphic self-map of the disc is an infinitesimal isometry of the Poincaré metric at a disc
point `p` if and only if it is a standard disc automorphism. -/
theorem norm_deriv_div_one_sub_norm_sq_eq_iff_unitDisc
    (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (hmaps : MapsTo f (ball (0 : ℂ) 1) (ball (0 : ℂ) 1)) (p : Complex.UnitDisc) :
    ‖deriv f (p : ℂ)‖ / (1 - ‖f (p : ℂ)‖ ^ 2) = 1 / (1 - ‖(p : ℂ)‖ ^ 2) ↔
      ∃ (u : Circle) (b : Complex.UnitDisc),
        ∀ ζ : Complex.UnitDisc, f ζ = (unitDiscStandardAutomorphismEquiv u b ζ : ℂ) :=
  norm_deriv_div_one_sub_norm_sq_eq_iff hf hmaps p.property

/-- **Infinitesimal Schwarz--Pick rigidity, propagation form.**  Equality in the infinitesimal
Schwarz--Pick inequality at one point of the disc forces it at every point: a holomorphic
self-map of the disc that is an infinitesimal isometry of the Poincaré metric somewhere is one
everywhere. -/
theorem forall_norm_deriv_div_one_sub_norm_sq_eq_of_norm_deriv_div_one_sub_norm_sq_eq
    (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (hmaps : MapsTo f (ball (0 : ℂ) 1) (ball (0 : ℂ) 1)) (ha : a ∈ ball (0 : ℂ) 1)
    (heq : ‖deriv f a‖ / (1 - ‖f a‖ ^ 2) = 1 / (1 - ‖a‖ ^ 2)) :
    ∀ z ∈ ball (0 : ℂ) 1, ‖deriv f z‖ / (1 - ‖f z‖ ^ 2) = 1 / (1 - ‖z‖ ^ 2) := fun _ hz =>
  (norm_deriv_div_one_sub_norm_sq_eq_iff hf hmaps hz).mpr
    ((norm_deriv_div_one_sub_norm_sq_eq_iff hf hmaps ha).mp heq)

/-- Bundled unit-disc form of the propagation of infinitesimal Schwarz--Pick equality: a
holomorphic self-map of the disc attaining equality at one disc point attains it at every disc
point. -/
theorem forall_norm_deriv_div_one_sub_norm_sq_eq_of_norm_deriv_div_one_sub_norm_sq_eq_unitDisc
    (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (hmaps : MapsTo f (ball (0 : ℂ) 1) (ball (0 : ℂ) 1)) (p : Complex.UnitDisc)
    (heq : ‖deriv f (p : ℂ)‖ / (1 - ‖f (p : ℂ)‖ ^ 2) = 1 / (1 - ‖(p : ℂ)‖ ^ 2))
    (q : Complex.UnitDisc) :
    ‖deriv f (q : ℂ)‖ / (1 - ‖f (q : ℂ)‖ ^ 2) = 1 / (1 - ‖(q : ℂ)‖ ^ 2) :=
  forall_norm_deriv_div_one_sub_norm_sq_eq_of_norm_deriv_div_one_sub_norm_sq_eq hf hmaps
    p.property heq (q : ℂ) q.property

/-! ### The Schwarz lemma at an interior fixed point -/

/-- **The Schwarz lemma at an interior fixed point.**  A holomorphic self-map of the open unit
disc fixing a point `a` of the disc has `‖deriv f a‖ ≤ 1`.  This is the infinitesimal
Schwarz--Pick inequality at `a`, where the two Poincaré defects coincide and cancel. -/
theorem norm_deriv_le_one_of_isFixedPt
    (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (hmaps : MapsTo f (ball (0 : ℂ) 1) (ball (0 : ℂ) 1)) (ha : a ∈ ball (0 : ℂ) 1)
    (hfix : Function.IsFixedPt f a) :
    ‖deriv f a‖ ≤ 1 := by
  have ha1 : ‖a‖ < 1 := by simpa [mem_ball_zero_iff] using ha
  have hden : (0 : ℝ) < 1 - ‖a‖ ^ 2 := by nlinarith [norm_nonneg a]
  have hle := norm_deriv_div_one_sub_norm_sq_le hf hmaps ha
  rw [hfix.eq, div_le_div_iff_of_pos_right hden] at hle
  exact hle

/-- At a fixed point the Schwarz--Pick conjugate's derivative at the origin is the derivative of
`f` itself: the source and target Moebius defects are the same nonzero number and cancel. -/
private lemma deriv_schwarzPickConjugate_zero_of_isFixedPt
    (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1)) (ha : a ∈ ball (0 : ℂ) 1)
    (hfix : Function.IsFixedPt f a) :
    deriv (schwarzPickConjugate f a) 0 = deriv f a := by
  have ha1 : ‖a‖ < 1 := by simpa [mem_ball_zero_iff] using ha
  have hf_at : HasDerivAt f (deriv f a) a :=
    (hf.differentiableAt (isOpen_ball.mem_nhds ha)).hasDerivAt
  have hfa1 : ‖f a‖ < 1 := by rw [hfix.eq]; exact ha1
  have hne : (1 : ℂ) - (starRingEnd ℂ) a * a ≠ 0 :=
    one_sub_conj_mul_ne_zero_of_norm_lt_one ha1 ha1
  rw [(hasDerivAt_schwarzPickConjugate_zero
      (one_sub_conj_mul_ne_zero_of_norm_lt_one hfa1 hfa1) hf_at).deriv, hfix.eq,
    mul_div_assoc, div_self hne, mul_one]

/-- **Equality in the Schwarz lemma at an interior fixed point.**  A holomorphic self-map of the
open unit disc that fixes `a` and has `‖deriv f a‖ = 1` is the *hyperbolic rotation* about `a`
by the argument of `deriv f a`: conjugating by the Moebius factor centred at `a` turns `f` into
multiplication by `deriv f a`. -/
theorem unitDiscMoebiusFormula_map_eq_mul_of_isFixedPt_of_norm_deriv_eq_one
    (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (hmaps : MapsTo f (ball (0 : ℂ) 1) (ball (0 : ℂ) 1)) (ha : a ∈ ball (0 : ℂ) 1)
    (hfix : Function.IsFixedPt f a) (hderiv : ‖deriv f a‖ = 1) {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    (f z - a) / (1 - (starRingEnd ℂ) a * f z)
      = deriv f a * ((z - a) / (1 - (starRingEnd ℂ) a * z)) := by
  have ha1 : ‖a‖ < 1 := by simpa [mem_ball_zero_iff] using ha
  have hz1 : ‖z‖ < 1 := by simpa [mem_ball_zero_iff] using hz
  have heq : ‖deriv f a‖ / (1 - ‖f a‖ ^ 2) = 1 / (1 - ‖a‖ ^ 2) := by rw [hfix.eq, hderiv]
  have hξ : (z - a) / (1 - (starRingEnd ℂ) a * z) ∈ ball (0 : ℂ) 1 :=
    mapsTo_ball_unitDiscMoebiusFormula_of_norm_lt_one ha1 hz
  have hg := eqOn_schwarzPickConjugate_mul hf hmaps ha heq hξ
  rw [schwarzPickConjugate_apply_unitDiscMoebiusFormula ha1 hz1,
    deriv_schwarzPickConjugate_zero_of_isFixedPt hf ha hfix, hfix.eq] at hg
  exact hg

/-- **A fixed point with derivative `1` forces the identity.**  A holomorphic self-map of the
open unit disc fixing a disc point `a` with `deriv f a = 1` is the identity on the disc.  This
sharpens `TauCeti.eqOn_id_of_isFixedPt_of_isFixedPt`, which assumes two fixed points, to one
fixed point together with the derivative condition. -/
theorem eqOn_id_of_isFixedPt_of_deriv_eq_one
    (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (hmaps : MapsTo f (ball (0 : ℂ) 1) (ball (0 : ℂ) 1)) (ha : a ∈ ball (0 : ℂ) 1)
    (hfix : Function.IsFixedPt f a) (hderiv : deriv f a = 1) :
    EqOn f id (ball (0 : ℂ) 1) := by
  have ha1 : ‖a‖ < 1 := by simpa [mem_ball_zero_iff] using ha
  intro z hz
  have hrot := unitDiscMoebiusFormula_map_eq_mul_of_isFixedPt_of_norm_deriv_eq_one hf hmaps ha hfix
    (by rw [hderiv, norm_one]) hz
  rw [hderiv, one_mul] at hrot
  -- The Moebius factor centred at `a` is injective on the disc, so `f z = z`.
  have hinj : InjOn (fun ζ : ℂ => (ζ - a) / (1 - (starRingEnd ℂ) a * ζ)) (ball (0 : ℂ) 1) :=
    (leftInvOn_unitDiscMoebiusFormula_of_norm_lt_one ha1).injOn
  exact hinj (hmaps hz) hz hrot

end TauCeti
