/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.FixedPoints.Basic
public import TauCeti.Analysis.Complex.Conformal.SchwarzPick.Rigidity
import Mathlib.Analysis.Complex.Schwarz
import TauCeti.Analysis.Complex.Conformal.InverseFunction
import TauCeti.Analysis.Complex.Conformal.SchwarzPick.Derivative
import TauCeti.Analysis.Complex.Conformal.UnitDisc.Automorphism.Parametrization

/-!
# Fixed points of holomorphic self-maps of the unit disc

Schwarz's lemma is the statement that a holomorphic self-map of the open unit disc *fixing the
origin* does not move points away from the origin and has `‖f' 0‖ ≤ 1`, with equality only for a
rotation.  Schwarz--Pick makes the estimate invariant, and this file reads the invariant estimate
back at an arbitrary **interior fixed point** `a` of `f`, where the origin plays no distinguished
role:

* the multiplier `‖deriv f a‖` of a self-map at a fixed point is at most `1`
  (`TauCeti.norm_deriv_le_one_of_isFixedPt`);
* it equals `1` exactly when `f` is a conformal automorphism of the disc
  (`TauCeti.norm_deriv_eq_one_iff_bijOn_of_isFixedPt`), in which case `f` is the *elliptic*
  automorphism rotating the disc about `a`
  (`TauCeti.exists_norm_eq_one_forall_eq_of_isFixedPt_of_norm_deriv_eq_one`);
* a self-map with **two** distinct fixed points is the identity
  (`TauCeti.eqOn_id_of_isFixedPt_of_isFixedPt`), so the fixed-point set of a self-map other than
  the identity is a subsingleton (`TauCeti.eqOn_id_or_subsingleton_inter_fixedPoints`).

The last statement generalises `TauCeti.eq_one_of_mem_unitDiscAut_of_isFixedPt`, which says the
same for a member of `Aut(𝔻)`, from automorphisms to arbitrary holomorphic self-maps; the
automorphism case is what the proof runs on, once Schwarz--Pick rigidity has shown a self-map with
two fixed points *is* an automorphism.

## The argument

Every proof reduces to the origin by the Schwarz--Pick conjugate `TauCeti.schwarzPickConjugate`
of `SchwarzPick/Basic.lean`, the self-map `g = M_{f a} ∘ f ∘ M_a⁻¹` of the disc that fixes `0`.

The bound `‖deriv f a‖ ≤ 1` is the infinitesimal Schwarz--Pick inequality
`TauCeti.norm_deriv_div_one_sub_norm_sq_le` read at `f a = a`, where the two Poincaré densities
cancel.  For its equality case, `TauCeti.norm_deriv_schwarzPickConjugate_at_zero` turns
`‖deriv f a‖ = 1` into `‖deriv g 0‖ = 1`, and Mathlib's equality case of the Schwarz lemma,
`Complex.affine_of_mapsTo_ball_of_norm_dslope_eq_div`, forces `g` to be linear: `g ζ = c * ζ` with
`‖c‖ = 1`.  Undoing the conjugation is the displayed identity
`M_a (f z) = c * M_a z`, and taking norms in it gives an equality
`pseudoHyperbolicExpr (f z) (f a) = pseudoHyperbolicExpr z a` at a pair of distinct points, which
is exactly the hypothesis of the Schwarz--Pick rigidity theorems of `SchwarzPick/Rigidity.lean`.
The converse — an automorphism has multiplier of modulus one at a fixed point — is the same bound
applied to `f` and to its holomorphic inverse, whose multipliers are reciprocal.

Two fixed points make that pseudo-hyperbolic equality hold for a trivial reason, with no
derivative in sight, so the rigidity theorems apply directly.

## Generality

In accordance with the generality bar of `ConformalMapping/README.md`, which fixes scalar `ℂ` for
every theorem added in layers L0--L6, everything below is stated for maps of `ℂ`, matching the
rest of `Conformal/SchwarzPick/`.  The hypothesis `Function.IsFixedPt f a` is Mathlib's spelling
of `f a = a`, as in `TauCeti.eq_one_of_mem_unitDiscAut_of_isFixedPt`.

## Coordination with upstream Mathlib

Per the *Coordination with upstream Mathlib* section of `ConformalMapping/README.md`, the L0--L3
material of this roadmap overlaps the in-progress human-curated Riemann-mapping effort
[mathlib4#33505](https://github.com/leanprover-community/mathlib4/pull/33505), which proves its
prerequisites internally as private lemmas; Mathlib's `Analysis/Complex/Schwarz.lean` and
`Analysis/Complex/BranchLogRoot.lean` are the preceding human-curated work.  This file is
therefore a **temporary shim** in the same sense as the rest of `Conformal/SchwarzPick/`: should a
human-curated fixed-point form of Schwarz--Pick land upstream, these statements are to be backed
by it, or deleted and their consumers refactored onto it.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 6 §1.2.
* J. B. Conway, *Functions of One Complex Variable I* (GTM 11), Ch. VI §2.
-/

public section

namespace TauCeti

open _root_.Complex Metric Set
open scoped ComplexConjugate Topology

variable {f : ℂ → ℂ} {a z w : ℂ}

/-- The open unit disc contains a point other than a prescribed one: the disc is not a
subsingleton, so a rigidity theorem needing *two* distinct points can always be fed. -/
private lemma exists_mem_ball_ne (ha : ‖a‖ < 1) : ∃ z ∈ ball (0 : ℂ) 1, z ≠ a := by
  have hnn : (0 : ℝ) ≤ (1 + ‖a‖) / 2 := by positivity
  have hnorm : ‖(((1 + ‖a‖) / 2 : ℝ) : ℂ)‖ = (1 + ‖a‖) / 2 := by
    rw [Complex.norm_real, Real.norm_of_nonneg hnn]
  refine ⟨(((1 + ‖a‖) / 2 : ℝ) : ℂ), ?_, ?_⟩
  · rw [mem_ball_zero_iff, hnorm]
    linarith
  · intro h
    rw [h] at hnorm
    linarith [norm_nonneg a]

/-! ### The multiplier at a fixed point -/

/-- **The multiplier at an interior fixed point has modulus at most one.** A holomorphic self-map
of the open unit disc fixing a point `a` of the disc satisfies `‖deriv f a‖ ≤ 1`.

This is Schwarz's bound `‖deriv f 0‖ ≤ 1` moved off the origin: the infinitesimal Schwarz--Pick
inequality bounds `‖deriv f a‖ / (1 - ‖f a‖ ^ 2)` by `1 / (1 - ‖a‖ ^ 2)`, and at a fixed point the
two Poincaré densities are equal. -/
theorem norm_deriv_le_one_of_isFixedPt (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (hmaps : MapsTo f (ball (0 : ℂ) 1) (ball (0 : ℂ) 1)) (ha : a ∈ ball (0 : ℂ) 1)
    (hfa : Function.IsFixedPt f a) : ‖deriv f a‖ ≤ 1 := by
  have ha1 : ‖a‖ < 1 := by simpa [mem_ball_zero_iff] using ha
  have hden : (0 : ℝ) < 1 - ‖a‖ ^ 2 := by nlinarith [norm_nonneg a]
  have h := norm_deriv_div_one_sub_norm_sq_le hf hmaps ha
  rw [hfa.eq] at h
  have hmul := mul_le_mul_of_nonneg_right h hden.le
  rwa [div_mul_cancel₀ _ hden.ne', div_mul_cancel₀ _ hden.ne'] at hmul

/-- **The equality case of Schwarz--Pick at a fixed point.** A holomorphic self-map of the open
unit disc fixing a point `a` of the disc and having `‖deriv f a‖ = 1` is the elliptic automorphism
rotating the disc about `a`: conjugated by the Moebius factor `M_a ζ = (ζ - a) / (1 - conj a * ζ)`
that moves `a` to the origin, it is multiplication by a unimodular constant.

The constant is the derivative at the origin of the Schwarz--Pick conjugate of `f` at `a`. -/
theorem exists_norm_eq_one_forall_eq_of_isFixedPt_of_norm_deriv_eq_one
    (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (hmaps : MapsTo f (ball (0 : ℂ) 1) (ball (0 : ℂ) 1)) (ha : a ∈ ball (0 : ℂ) 1)
    (hfa : Function.IsFixedPt f a) (hd : ‖deriv f a‖ = 1) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ z ∈ ball (0 : ℂ) 1,
      (f z - a) / (1 - (starRingEnd ℂ) a * f z)
        = c * ((z - a) / (1 - (starRingEnd ℂ) a * z)) := by
  have ha1 : ‖a‖ < 1 := by simpa [mem_ball_zero_iff] using ha
  have hfa1 : ‖f a‖ < 1 := by rw [hfa.eq]; exact ha1
  have hden : (0 : ℝ) < 1 - ‖a‖ ^ 2 := by nlinarith [norm_nonneg a]
  obtain ⟨hg_diff, hg_maps, hg_zero⟩ :=
    differentiableOn_and_mapsTo_ball_and_apply_zero_schwarzPickConjugate hf hmaps ha1
  have hf_at : HasDerivAt f (deriv f a) a :=
    (hf.differentiableAt (isOpen_ball.mem_nhds ha)).hasDerivAt
  -- The conjugate is a self-map of the disc fixing `0` whose multiplier there is again unimodular.
  have hg_deriv : ‖deriv (schwarzPickConjugate f a) 0‖ = 1 := by
    rw [norm_deriv_schwarzPickConjugate_at_zero ha1 hfa1 hf_at, hd, hfa.eq, one_mul,
      div_self hden.ne']
  have hg_closed : MapsTo (schwarzPickConjugate f a) (ball (0 : ℂ) 1)
      (closedBall (schwarzPickConjugate f a 0) 1) := by
    rw [hg_zero]
    exact fun ξ hξ => ball_subset_closedBall (hg_maps hξ)
  have hds : ‖dslope (schwarzPickConjugate f a) 0 0‖ = 1 / 1 := by
    simpa [dslope_same] using hg_deriv
  -- Mathlib's equality case of the Schwarz lemma makes the conjugate linear.
  have haff := Complex.affine_of_mapsTo_ball_of_norm_dslope_eq_div hg_diff hg_closed
    (mem_ball_self one_pos) hds
  refine ⟨deriv (schwarzPickConjugate f a) 0, hg_deriv, fun z hz => ?_⟩
  have hz1 : ‖z‖ < 1 := by simpa [mem_ball_zero_iff] using hz
  have hmem : (z - a) / (1 - (starRingEnd ℂ) a * z) ∈ ball (0 : ℂ) 1 :=
    mapsTo_ball_unitDiscMoebiusFormula_of_norm_lt_one ha1 hz
  -- Undo the conjugation: the linear identity for the conjugate is the claim for `f`.
  have hlin := haff hmem
  rw [schwarzPickConjugate_apply_unitDiscMoebiusFormula ha1 hz1, hg_zero, hfa.eq] at hlin
  simpa [dslope_same, mul_comm] using hlin

/-- **A unimodular multiplier at a fixed point forces a pseudo-hyperbolic isometry.** A
holomorphic self-map of the open unit disc fixing `a` with `‖deriv f a‖ = 1` preserves the
pseudo-hyperbolic expression measured from `a`. -/
theorem pseudoHyperbolicExpr_map_eq_of_isFixedPt_of_norm_deriv_eq_one
    (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (hmaps : MapsTo f (ball (0 : ℂ) 1) (ball (0 : ℂ) 1)) (ha : a ∈ ball (0 : ℂ) 1)
    (hfa : Function.IsFixedPt f a) (hd : ‖deriv f a‖ = 1) :
    ∀ z ∈ ball (0 : ℂ) 1, pseudoHyperbolicExpr (f z) a = pseudoHyperbolicExpr z a := by
  obtain ⟨c, hc, hlin⟩ :=
    exists_norm_eq_one_forall_eq_of_isFixedPt_of_norm_deriv_eq_one hf hmaps ha hfa hd
  intro z hz
  rw [pseudoHyperbolicExpr_def, pseudoHyperbolicExpr_def, hlin z hz, norm_mul, hc, one_mul]

/-- **A unimodular multiplier at a fixed point forces an automorphism.** A holomorphic self-map of
the open unit disc fixing `a` with `‖deriv f a‖ = 1` is a bijection of the disc onto itself. -/
theorem bijOn_ball_of_isFixedPt_of_norm_deriv_eq_one (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (hmaps : MapsTo f (ball (0 : ℂ) 1) (ball (0 : ℂ) 1)) (ha : a ∈ ball (0 : ℂ) 1)
    (hfa : Function.IsFixedPt f a) (hd : ‖deriv f a‖ = 1) :
    BijOn f (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) := by
  have ha1 : ‖a‖ < 1 := by simpa [mem_ball_zero_iff] using ha
  obtain ⟨z, hz, hzne⟩ := exists_mem_ball_ne ha1
  have heq : pseudoHyperbolicExpr (f z) (f a) = pseudoHyperbolicExpr z a := by
    rw [hfa.eq]
    exact pseudoHyperbolicExpr_map_eq_of_isFixedPt_of_norm_deriv_eq_one hf hmaps ha hfa hd z hz
  exact bijOn_ball_of_pseudoHyperbolicExpr_map_eq hf hmaps hz ha hzne heq

/-- **Classification of a self-map with a unimodular multiplier at a fixed point.** Such a map is
one of the standard disc automorphisms `ζ ↦ u * (ζ - b) / (1 - conj b * ζ)`. -/
theorem exists_forall_unitDisc_eq_unitDiscStandardAutomorphismEquiv_of_norm_deriv_eq_one
    (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (hmaps : MapsTo f (ball (0 : ℂ) 1) (ball (0 : ℂ) 1)) (ha : a ∈ ball (0 : ℂ) 1)
    (hfa : Function.IsFixedPt f a) (hd : ‖deriv f a‖ = 1) :
    ∃ (u : Circle) (b : Complex.UnitDisc),
      ∀ ζ : Complex.UnitDisc, f ζ = (unitDiscStandardAutomorphismEquiv u b ζ : ℂ) := by
  have ha1 : ‖a‖ < 1 := by simpa [mem_ball_zero_iff] using ha
  obtain ⟨z, hz, hzne⟩ := exists_mem_ball_ne ha1
  have heq : pseudoHyperbolicExpr (f z) (f a) = pseudoHyperbolicExpr z a := by
    rw [hfa.eq]
    exact pseudoHyperbolicExpr_map_eq_of_isFixedPt_of_norm_deriv_eq_one hf hmaps ha hfa hd z hz
  exact exists_forall_unitDisc_eq_unitDiscStandardAutomorphismEquiv_of_pseudoHyperbolicExpr_map_eq
    hf hmaps hz ha hzne heq

/-- **An automorphism has a unimodular multiplier at a fixed point.** The converse of
`TauCeti.bijOn_ball_of_isFixedPt_of_norm_deriv_eq_one`: the bound `‖deriv f a‖ ≤ 1` applies to the
holomorphic inverse as well, and the two multipliers are reciprocal. -/
theorem norm_deriv_eq_one_of_isFixedPt_of_bijOn (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (ha : a ∈ ball (0 : ℂ) 1) (hfa : Function.IsFixedPt f a)
    (hbij : BijOn f (ball (0 : ℂ) 1) (ball (0 : ℂ) 1)) : ‖deriv f a‖ = 1 := by
  refine le_antisymm (norm_deriv_le_one_of_isFixedPt hf hbij.mapsTo ha hfa) ?_
  -- The inverse is a holomorphic self-map of the disc fixing `a`, so its multiplier is bounded too.
  obtain ⟨g, hgd, hgm, hgf⟩ : ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (ball (0 : ℂ) 1) ∧
      MapsTo g (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) ∧ LeftInvOn g f (ball (0 : ℂ) 1) := by
    refine ⟨Function.invFunOn f (ball (0 : ℂ) 1), ?_, ?_, hbij.injOn.leftInvOn_invFunOn⟩
    · have h := TauCeti.DifferentiableOn.invFunOn hf isOpen_ball hbij.injOn
      rwa [hbij.image_eq] at h
    · intro v hv
      obtain ⟨x, hx, rfl⟩ := hbij.surjOn hv
      rw [hbij.injOn.leftInvOn_invFunOn hx]
      exact hx
  have hga : Function.IsFixedPt g a := by
    have h := hgf ha
    rwa [hfa.eq] at h
  have hgle : ‖deriv g a‖ ≤ 1 := norm_deriv_le_one_of_isFixedPt hgd hgm ha hga
  -- The chain rule on `g ∘ f = id` near `a` makes the two multipliers reciprocal.
  have hf_at : HasDerivAt f (deriv f a) a :=
    (hf.differentiableAt (isOpen_ball.mem_nhds ha)).hasDerivAt
  have hg_at : HasDerivAt g (deriv g a) (f a) := by
    rw [hfa.eq]
    exact (hgd.differentiableAt (isOpen_ball.mem_nhds ha)).hasDerivAt
  have hcomp : HasDerivAt (g ∘ f) (deriv g a * deriv f a) a := hg_at.comp a hf_at
  have hev : (g ∘ f) =ᶠ[𝓝 a] id := by
    filter_upwards [isOpen_ball.mem_nhds ha] with v hv using hgf hv
  have hmul : deriv g a * deriv f a = 1 :=
    hcomp.unique ((hasDerivAt_id a).congr_of_eventuallyEq hev)
  have hnorm : ‖deriv g a‖ * ‖deriv f a‖ = 1 := by rw [← norm_mul, hmul, norm_one]
  nlinarith [norm_nonneg (deriv f a), norm_nonneg (deriv g a)]

/-- **The multiplier at an interior fixed point detects the automorphisms.** A holomorphic
self-map of the open unit disc fixing a disc point `a` is a conformal automorphism of the disc
exactly when its multiplier at `a` has modulus one; otherwise the multiplier is strictly
contracting. -/
theorem norm_deriv_eq_one_iff_bijOn_of_isFixedPt (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (hmaps : MapsTo f (ball (0 : ℂ) 1) (ball (0 : ℂ) 1)) (ha : a ∈ ball (0 : ℂ) 1)
    (hfa : Function.IsFixedPt f a) :
    ‖deriv f a‖ = 1 ↔ BijOn f (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) :=
  ⟨bijOn_ball_of_isFixedPt_of_norm_deriv_eq_one hf hmaps ha hfa,
    norm_deriv_eq_one_of_isFixedPt_of_bijOn hf ha hfa⟩

/-- **A self-map with an interior fixed point that is not an automorphism is a strict contraction
there.** -/
theorem norm_deriv_lt_one_of_isFixedPt_of_not_bijOn (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (hmaps : MapsTo f (ball (0 : ℂ) 1) (ball (0 : ℂ) 1)) (ha : a ∈ ball (0 : ℂ) 1)
    (hfa : Function.IsFixedPt f a) (hbij : ¬ BijOn f (ball (0 : ℂ) 1) (ball (0 : ℂ) 1)) :
    ‖deriv f a‖ < 1 :=
  lt_of_le_of_ne (norm_deriv_le_one_of_isFixedPt hf hmaps ha hfa)
    fun h => hbij ((norm_deriv_eq_one_iff_bijOn_of_isFixedPt hf hmaps ha hfa).mp h)

/-! ### Two fixed points -/

/-- **A holomorphic self-map of the disc with two distinct fixed points is the identity.**

Two fixed points make the Schwarz--Pick estimate an equality at that pair for a trivial reason, so
the classification form of Schwarz--Pick rigidity turns `f` into a disc automorphism; an
automorphism with two distinct fixed points is the identity by
`TauCeti.eq_one_of_mem_unitDiscAut_of_isFixedPt`.  This generalises that statement from `Aut(𝔻)`
to arbitrary holomorphic self-maps. -/
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

/-- **The fixed-point set of a self-map other than the identity is a subsingleton.** -/
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

end TauCeti
