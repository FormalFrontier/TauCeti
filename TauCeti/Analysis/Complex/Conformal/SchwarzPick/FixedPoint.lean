/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.FixedPoints.Defs
public import TauCeti.Analysis.Complex.Conformal.SchwarzPick.Rigidity
import TauCeti.Analysis.Complex.Conformal.SchwarzPick.Derivative.Rigidity
import TauCeti.Analysis.Complex.Conformal.UnitDisc.Automorphism.Parametrization

/-!
# Fixed points of holomorphic self-maps of the unit disc

A holomorphic self-map of the open unit disc that fixes **two** distinct points of the disc is
the identity (`TauCeti.eqOn_id_of_isFixedPt_of_isFixedPt`); equivalently, the fixed-point set in
the open unit disc of any self-map other than the identity is a subsingleton
(`TauCeti.subsingleton_inter_fixedPoints_of_not_eqOn_id`), which read hypothesis-free is the
dichotomy that a self-map is either the identity or fixes at most one point of the disc
(`TauCeti.eqOn_id_or_subsingleton_inter_fixedPoints`).

This generalises `TauCeti.eq_one_of_mem_unitDiscAut_of_isFixedPt` of
`UnitDisc/Automorphism/Parametrization.lean`, which says the same for a member of `Aut(𝔻)`, from
automorphisms to arbitrary holomorphic self-maps.

The second half of the file is what a **single** interior fixed point gives, once the derivative
there is taken into account: the classical Schwarz lemma at an interior fixed point
`TauCeti.norm_deriv_le_one_of_isFixedPt`, its equality case
`TauCeti.unitDiscMoebiusFormula_map_eq_mul_of_isFixedPt_of_norm_deriv_eq_one` identifying `f` as
the hyperbolic rotation about the fixed point, and
`TauCeti.eqOn_id_of_isFixedPt_of_deriv_eq_one`, which sharpens the two-fixed-point statement
above to one fixed point together with `deriv f a = 1`.

## The argument

The automorphism case is exactly what the proof runs on.  Two fixed points make the
Schwarz--Pick contraction estimate an equality at that pair of points for a trivial reason —
both sides are the same pseudo-hyperbolic expression — so the classification form of
Schwarz--Pick rigidity,
`exists_forall_unitDisc_eq_unitDiscStandardAutomorphismEquiv_of_pseudoHyperbolicExpr_map_eq`
of `SchwarzPick/Rigidity.lean`, turns `f` into a standard disc automorphism
`ζ ↦ u * (ζ - b) / (1 - conj b * ζ)`.  Its two fixed points then force it to be the identity of
`Aut(𝔻)` by the already-merged automorphism statement.

The single-fixed-point statements read off the infinitesimal Schwarz--Pick material of
`SchwarzPick/Derivative/`.  At a fixed point the source and target Poincaré defects in
`TauCeti.hasDerivAt_schwarzPickConjugate_zero` are the same nonzero number and cancel, so the
Schwarz--Pick conjugate has derivative `deriv f a` at the origin on the nose and not merely in
norm.  The estimate `TauCeti.norm_deriv_div_one_sub_norm_sq_le` then reads `‖deriv f a‖ ≤ 1`,
and in the equality case the conjugate form of the infinitesimal rigidity,
`TauCeti.eqOn_schwarzPickConjugate_mul_of_norm_deriv_div_one_sub_norm_sq_eq`, says the conjugate
is multiplication by that derivative.  Injectivity of the Moebius factor centred at `a` turns the
rotation factor `1` into `EqOn f id`.

## Generality

In accordance with the generality bar of `ConformalMapping/README.md`, which fixes scalar `ℂ`
for every theorem added in layers L0--L6, everything below is stated for maps of `ℂ`, matching
the rest of `Conformal/SchwarzPick/`.  The hypothesis `Function.IsFixedPt f a` is Mathlib's
spelling of `f a = a`, as in `TauCeti.eq_one_of_mem_unitDiscAut_of_isFixedPt`.

## Coordination with upstream Mathlib

Per the *Coordination with upstream Mathlib* section of `ConformalMapping/README.md`, the
L0--L3 material of this roadmap overlaps the in-progress human-curated Riemann-mapping effort
[mathlib4#33505](https://github.com/leanprover-community/mathlib4/pull/33505), which proves its
prerequisites internally as private lemmas; Mathlib's `Analysis/Complex/Schwarz.lean` and
`Analysis/Complex/BranchLogRoot.lean` are the preceding human-curated work.  This file is
therefore a **temporary shim** in the same sense as the rest of `Conformal/SchwarzPick/`: should
a human-curated fixed-point form of Schwarz--Pick land upstream, these statements are to be
backed by it, or deleted and their consumers refactored onto it.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 6 §1.2.
* J. B. Conway, *Functions of One Complex Variable I* (GTM 11), Ch. VI §2.
-/

public section

namespace TauCeti

open Metric Set

variable {f : ℂ → ℂ} {a z w : ℂ}

/-- **A holomorphic self-map of the disc with two distinct fixed points is the identity.**

If `f` is differentiable on the open unit ball `ball (0 : ℂ) 1`, maps that ball into itself and
fixes two distinct points `z ≠ w` of it, then `f` agrees with the identity on the whole ball.
This is `TauCeti.eq_one_of_mem_unitDiscAut_of_isFixedPt` with its hypothesis weakened from
membership in `Aut(𝔻)` to an arbitrary holomorphic self-map. -/
theorem eqOn_id_of_isFixedPt_of_isFixedPt (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (hmaps : MapsTo f (ball (0 : ℂ) 1) (ball (0 : ℂ) 1)) (hz : z ∈ ball (0 : ℂ) 1)
    (hw : w ∈ ball (0 : ℂ) 1) (hne : z ≠ w) (hfz : Function.IsFixedPt f z)
    (hfw : Function.IsFixedPt f w) : EqOn f id (ball (0 : ℂ) 1) := by
  have hz1 : ‖z‖ < 1 := by simpa [mem_ball_zero_iff] using hz
  have hw1 : ‖w‖ < 1 := by simpa [mem_ball_zero_iff] using hw
  have heq : pseudoHyperbolicExpr (f z) (f w) = pseudoHyperbolicExpr z w := by
    rw [hfz.eq, hfw.eq]
  obtain ⟨u, b, hb⟩ :=
    exists_forall_unitDisc_eq_unitDiscStandardAutomorphismEquiv_of_pseudoHyperbolicExpr_map_eq
      hf hmaps hz hw hne heq
  -- Read the two fixed points inside the disc as fixed points of the automorphism.
  have hmem : unitDiscStandardAutomorphismEquiv u b ∈ unitDiscAut :=
    unitDiscStandardAutomorphismEquiv_mem_unitDiscAut u b
  have hfix : ∀ {p : ℂ} (hp : ‖p‖ < 1), Function.IsFixedPt f p →
      Function.IsFixedPt (unitDiscStandardAutomorphismEquiv u b) (Complex.UnitDisc.mk p hp) := by
    intro p hp hfp
    have h := hb (Complex.UnitDisc.mk p hp)
    rw [Complex.UnitDisc.coe_mk, hfp.eq] at h
    exact Complex.UnitDisc.coe_injective (h.symm.trans (Complex.UnitDisc.coe_mk p hp).symm)
  have hmkne : Complex.UnitDisc.mk z hz1 ≠ Complex.UnitDisc.mk w hw1 := by
    intro h
    exact hne (by simpa using congrArg (fun t : Complex.UnitDisc => (t : ℂ)) h)
  have hone : unitDiscStandardAutomorphismEquiv u b = 1 :=
    eq_one_of_mem_unitDiscAut_of_isFixedPt hmem hmkne (hfix hz1 hfz) (hfix hw1 hfw)
  intro ζ hζ
  have hζ1 : ‖ζ‖ < 1 := by simpa [mem_ball_zero_iff] using hζ
  have h := hb (Complex.UnitDisc.mk ζ hζ1)
  rw [hone] at h
  simpa using h

/-- **The fixed-point set in the disc of a self-map other than the identity is a subsingleton.**

The hypotheses constrain `f` only on `ball (0 : ℂ) 1`, so only the fixed points lying in that
ball are controlled: fixed points of `f` outside the disc are arbitrary. -/
theorem subsingleton_inter_fixedPoints_of_not_eqOn_id
    (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (hmaps : MapsTo f (ball (0 : ℂ) 1) (ball (0 : ℂ) 1))
    (hid : ¬ EqOn f id (ball (0 : ℂ) 1)) :
    (ball (0 : ℂ) 1 ∩ Function.fixedPoints f).Subsingleton := by
  rintro p ⟨hp, hfp⟩ q ⟨hq, hfq⟩
  by_contra hne
  exact hid (eqOn_id_of_isFixedPt_of_isFixedPt hf hmaps hp hq hne hfp hfq)

/-- **The fixed-point dichotomy for a holomorphic self-map of the disc.** Either the map is the
identity, or it fixes at most one point of the disc. -/
theorem eqOn_id_or_subsingleton_inter_fixedPoints (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (hmaps : MapsTo f (ball (0 : ℂ) 1) (ball (0 : ℂ) 1)) :
    EqOn f id (ball (0 : ℂ) 1) ∨ (ball (0 : ℂ) 1 ∩ Function.fixedPoints f).Subsingleton := by
  by_cases hid : EqOn f id (ball (0 : ℂ) 1)
  · exact Or.inl hid
  · exact Or.inr (subsingleton_inter_fixedPoints_of_not_eqOn_id hf hmaps hid)

/-! ### A single fixed point, with the derivative there -/

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
    (hfix : Function.IsFixedPt f a) (hderiv : ‖deriv f a‖ = 1) (hz : z ∈ ball (0 : ℂ) 1) :
    (f z - a) / (1 - (starRingEnd ℂ) a * f z)
      = deriv f a * ((z - a) / (1 - (starRingEnd ℂ) a * z)) := by
  have ha1 : ‖a‖ < 1 := by simpa [mem_ball_zero_iff] using ha
  have hz1 : ‖z‖ < 1 := by simpa [mem_ball_zero_iff] using hz
  have heq : ‖deriv f a‖ / (1 - ‖f a‖ ^ 2) = 1 / (1 - ‖a‖ ^ 2) := by rw [hfix.eq, hderiv]
  have hξ : (z - a) / (1 - (starRingEnd ℂ) a * z) ∈ ball (0 : ℂ) 1 :=
    mapsTo_ball_unitDiscMoebiusFormula_of_norm_lt_one ha1 hz
  have hg := eqOn_schwarzPickConjugate_mul_of_norm_deriv_div_one_sub_norm_sq_eq hf hmaps ha heq hξ
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
