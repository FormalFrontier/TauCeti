/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Complex.Conformal.Hyperbolic.Distance
public import TauCeti.Analysis.Complex.Conformal.UnitDisc.Automorphism.Classification

/-!
# Rigidity in the Schwarz--Pick theorem

The Schwarz--Pick theorem (`TauCeti.pseudoHyperbolicExpr_map_le`) says a holomorphic self-map
`f` of the open unit disc contracts the pseudo-hyperbolic expression
`pseudoHyperbolicExpr z w = ‖(z - w) / (1 - conj w * z)‖`.  This file proves the **equality
case**: if the contraction is an equality at a *single* pair of distinct points, then `f` is a
disc automorphism, and in particular the contraction is an equality everywhere.

The proof runs on the shared `TauCeti.schwarzPickConjugate` construction, which conjugates `f`
by the Moebius factors that send `w` to `0` on the source and `f w` to `0` on the target,
exactly as the contraction estimate does.  The conjugate `g = schwarzPickConjugate f w` is a
holomorphic self-map of the disc fixing the origin, and the hypothesis says `‖g ξ‖ = ‖ξ‖` at
the nonzero point `ξ = (z - w) / (1 - conj w * z)`.  Mathlib's equality case of the Schwarz
lemma, `Complex.affine_of_mapsTo_ball_of_norm_dslope_eq_div`, then forces `g` to be the
rotation `ζ ↦ C * ζ` for a unimodular constant `C`.  Unwinding the conjugation gives the
identity `(f ζ - f w) / (1 - conj (f w) * f ζ) = C * ((ζ - w) / (1 - conj w * ζ))` on the whole
disc, from which the inverse map is read off explicitly as a Moebius factor, an inverse
rotation and a Moebius factor.

## Main results

* `TauCeti.exists_norm_eq_one_forall_eq_of_pseudoHyperbolicExpr_map_eq` — the unwound identity
  above: `f` is the Moebius conjugate of a rotation;
* `TauCeti.exists_differentiableOn_mapsTo_invOn_of_pseudoHyperbolicExpr_map_eq` — the explicit
  holomorphic two-sided inverse of `f` on the disc;
* `TauCeti.bijOn_ball_of_pseudoHyperbolicExpr_map_eq` — `f` is a bijection of the disc;
* `TauCeti.forall_pseudoHyperbolicExpr_map_eq_of_pseudoHyperbolicExpr_map_eq` — one equality
  propagates to every pair of points, so `f` is a pseudo-hyperbolic isometry;
* `exists_forall_unitDisc_eq_unitDiscStandardAutomorphismEquiv_of_pseudoHyperbolicExpr_map_eq`
  — `f` has the standard form `u * (ζ - a) / (1 - conj a * ζ)`;
* `TauCeti.forall_hyperbolicDist_map_eq_of_hyperbolicDist_map_eq` and
  `exists_forall_unitDisc_eq_unitDiscStandardAutomorphismEquiv_of_hyperbolicDist_map_eq` — the
  same rigidity stated for the hyperbolic (Poincaré) distance.

Together with `TauCeti.pseudoHyperbolicExpr_unitDiscStandardAutomorphismEquiv`, which says the
standard automorphisms *are* pseudo-hyperbolic isometries, these results identify the isometry
group of the pseudo-hyperbolic expression among the holomorphic self-maps of the disc.

This advances the conformal-mapping roadmap's L2 target (Schwarz lemma extensions:
Schwarz--Pick and the disc automorphism group `Aut(𝔻) = {e^{iθ}(z−a)/(1−āz)}`; see
`ConformalMapping/README.md`).  It reuses Mathlib's Schwarz-lemma equality case and Tau Ceti's
unit-disc Moebius and disc-automorphism API rather than re-deriving either.  As with the rest
of the L0--L3 conformal-mapping material, it is coordinated with the upstream Mathlib RMT
effort leanprover-community/mathlib4#33505.  Mathlib already contains the preceding
human-curated work in `Analysis/Complex/RiemannMapping.lean` and
`Analysis/Complex/BranchLogRoot.lean`; none of it is duplicated here, and should a
human-curated Schwarz--Pick rigidity statement land upstream this file should be refactored
onto it, or deleted with its consumers refactored.
-/

public section

namespace TauCeti

open _root_.Complex Metric Set
open scoped ComplexConjugate

variable {f : ℂ → ℂ} {z w : ℂ}

/--
**Rigidity in the Schwarz--Pick theorem.**  If a holomorphic self-map `f` of the open unit disc
preserves the pseudo-hyperbolic expression at one pair of distinct points `z ≠ w`, then on the
whole disc `f` is the Moebius conjugate of a rotation: there is a unimodular `C` with

`(f ζ - f w) / (1 - conj (f w) * f ζ) = C * ((ζ - w) / (1 - conj w * ζ))`.
-/
theorem exists_norm_eq_one_forall_eq_of_pseudoHyperbolicExpr_map_eq
    (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (hmaps : MapsTo f (ball (0 : ℂ) 1) (ball (0 : ℂ) 1))
    (hz : z ∈ ball (0 : ℂ) 1) (hw : w ∈ ball (0 : ℂ) 1) (hne : z ≠ w)
    (heq : pseudoHyperbolicExpr (f z) (f w) = pseudoHyperbolicExpr z w) :
    ∃ C : ℂ, ‖C‖ = 1 ∧ ∀ ζ ∈ ball (0 : ℂ) 1,
      (f ζ - f w) / (1 - (starRingEnd ℂ) (f w) * f ζ)
        = C * ((ζ - w) / (1 - (starRingEnd ℂ) w * ζ)) := by
  have hw_norm : ‖w‖ < 1 := by simpa [mem_ball_zero_iff] using hw
  -- The Schwarz--Pick conjugation scaffold: `schwarzPickConjugate f w` fixes the origin.
  obtain ⟨hgd, hgm, hg0⟩ :=
    differentiableOn_and_mapsTo_ball_and_apply_zero_schwarzPickConjugate hf hmaps hw_norm
  have hg_maps_closed : MapsTo (schwarzPickConjugate f w) (ball (0 : ℂ) 1)
      (closedBall (schwarzPickConjugate f w 0) 1) := by
    intro ζ hζ
    rw [hg0]
    exact ball_subset_closedBall (hgm hζ)
  -- The point at which the Schwarz estimate for the conjugate is an equality.
  let ξ : ℂ := (z - w) / (1 - (starRingEnd ℂ) w * z)
  have hξ_mem : ξ ∈ ball (0 : ℂ) 1 := by
    simpa [ξ] using mapsTo_ball_unitDiscMoebiusFormula_of_norm_lt_one (a := w) hw_norm hz
  have hz_norm : ‖z‖ < 1 := by simpa [mem_ball_zero_iff] using hz
  have hξ_norm : ‖ξ‖ = pseudoHyperbolicExpr z w := (pseudoHyperbolicExpr_def z w).symm
  have hξ_ne : ξ ≠ 0 := by
    rw [← norm_ne_zero_iff, hξ_norm]
    exact fun h => hne ((pseudoHyperbolicExpr_eq_zero_iff_of_mem_ball hz hw).mp h)
  have hg_ξ : ‖schwarzPickConjugate f w ξ‖ = ‖ξ‖ := by
    have h1 : schwarzPickConjugate f w ξ
        = (f z - f w) / (1 - (starRingEnd ℂ) (f w) * f z) :=
      schwarzPickConjugate_apply_unitDiscMoebiusFormula hw_norm hz_norm
    rw [h1, ← pseudoHyperbolicExpr_def, heq, hξ_norm]
  -- Mathlib's equality case of the Schwarz lemma: the conjugate is a rotation.
  have hdslope : ‖dslope (schwarzPickConjugate f w) 0 ξ‖ = 1 / 1 := by
    rw [dslope_of_ne _ hξ_ne, slope_def_field, hg0, sub_zero, sub_zero, norm_div, hg_ξ,
      div_self (norm_ne_zero_iff.mpr hξ_ne)]
    norm_num
  have haffine :=
    Complex.affine_of_mapsTo_ball_of_norm_dslope_eq_div hgd hg_maps_closed hξ_mem hdslope
  refine ⟨dslope (schwarzPickConjugate f w) 0 ξ, by simpa using hdslope, fun ζ hζ => ?_⟩
  have hζ' : (ζ - w) / (1 - (starRingEnd ℂ) w * ζ) ∈ ball (0 : ℂ) 1 :=
    mapsTo_ball_unitDiscMoebiusFormula_of_norm_lt_one (a := w) hw_norm hζ
  have hgζ : schwarzPickConjugate f w ((ζ - w) / (1 - (starRingEnd ℂ) w * ζ))
      = (f ζ - f w) / (1 - (starRingEnd ℂ) (f w) * f ζ) :=
    schwarzPickConjugate_apply_unitDiscMoebiusFormula hw_norm
      (by simpa [mem_ball_zero_iff] using hζ)
  have hval := haffine hζ'
  simp only [hgζ, hg0, zero_add, sub_zero, smul_eq_mul] at hval
  exact hval.trans (mul_comm _ _)

/-- **The explicit inverse undoes `f` from the right.** If the Moebius factor at `a` conjugates
`f` into the rotation by `C` composed with the Moebius factor at `w`, then the composite
`M₋w ∘ (C⁻¹ · ) ∘ M_a` is a right inverse of `f` on the disc.

Only the conjugation identity, the two norm bounds and the self-map properties of `f` and of the
inverse rotation are used; differentiability of `f` and of the factors plays no part in this half.
The scalar `C` enters only through `C ≠ 0` and through `hR_maps`, so the caller may supply any
nonzero `C` whose inverse contracts the disc — in particular a unimodular one. -/
private lemma rightInvOn_moebius_rotate_moebius_of_forall_eq {a C : ℂ} (ha : ‖a‖ < 1)
    (hw : ‖w‖ < 1) (hC0 : C ≠ 0)
    (hR_maps : MapsTo (fun η : ℂ => C⁻¹ * η) (ball (0 : ℂ) 1) (ball (0 : ℂ) 1))
    (hmaps : MapsTo f (ball (0 : ℂ) 1) (ball (0 : ℂ) 1))
    (hCeq : ∀ ζ ∈ ball (0 : ℂ) 1, (f ζ - a) / (1 - (starRingEnd ℂ) a * f ζ)
      = C * ((ζ - w) / (1 - (starRingEnd ℂ) w * ζ))) :
    RightInvOn ((fun ξ : ℂ => (ξ - (-w)) / (1 - (starRingEnd ℂ) (-w) * ξ)) ∘
        (fun η : ℂ => C⁻¹ * η) ∘
        (fun η : ℂ => (η - a) / (1 - (starRingEnd ℂ) a * η)))
      f (ball (0 : ℂ) 1) := by
  have hnegw : ‖(-w : ℂ)‖ < 1 := by simpa using hw
  have hT_maps := mapsTo_ball_unitDiscMoebiusFormula_of_norm_lt_one ha
  have hS_maps := mapsTo_ball_unitDiscMoebiusFormula_of_norm_lt_one (a := -w) hnegw
  have hTinj : InjOn (fun ζ : ℂ => (ζ - a) / (1 - (starRingEnd ℂ) a * ζ)) (ball (0 : ℂ) 1) :=
    (leftInvOn_unitDiscMoebiusFormula_of_norm_lt_one ha).injOn
  intro η hη
  simp only [Function.comp_apply]
  set ζ : ℂ := (C⁻¹ * ((η - a) / (1 - (starRingEnd ℂ) a * η)) - -w) /
      (1 - (starRingEnd ℂ) (-w) * (C⁻¹ * ((η - a) / (1 - (starRingEnd ℂ) a * η)))) with hζdef
  have hRTη : C⁻¹ * ((η - a) / (1 - (starRingEnd ℂ) a * η)) ∈ ball (0 : ℂ) 1 :=
    hR_maps (hT_maps hη)
  have hζ : ζ ∈ ball (0 : ℂ) 1 := hS_maps hRTη
  -- Undo the outer Moebius factor, then the rotation, and compare through the injective `M_a`.
  have hmoebius : (ζ - w) / (1 - (starRingEnd ℂ) w * ζ)
      = C⁻¹ * ((η - a) / (1 - (starRingEnd ℂ) a * η)) := by
    simpa [hζdef] using
      leftInvOn_unitDiscMoebiusFormula_of_norm_lt_one (a := -w) hnegw hRTη
  refine hTinj (hmaps hζ) hη ?_
  dsimp only
  rw [hCeq ζ hζ, hmoebius, mul_inv_cancel_left₀ hC0]

/--
**The inverse map produced by Schwarz--Pick rigidity.**  Under the hypotheses of
`TauCeti.exists_norm_eq_one_forall_eq_of_pseudoHyperbolicExpr_map_eq`, the map `f` has an
explicit holomorphic two-sided inverse on the open unit disc, namely the composite of the
Moebius factor centred at `f w`, the inverse rotation, and the Moebius factor centred at `-w`.
-/
theorem exists_differentiableOn_mapsTo_invOn_of_pseudoHyperbolicExpr_map_eq
    (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (hmaps : MapsTo f (ball (0 : ℂ) 1) (ball (0 : ℂ) 1))
    (hz : z ∈ ball (0 : ℂ) 1) (hw : w ∈ ball (0 : ℂ) 1) (hne : z ≠ w)
    (heq : pseudoHyperbolicExpr (f z) (f w) = pseudoHyperbolicExpr z w) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (ball (0 : ℂ) 1) ∧
      MapsTo g (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) ∧
      LeftInvOn g f (ball (0 : ℂ) 1) ∧ RightInvOn g f (ball (0 : ℂ) 1) := by
  obtain ⟨C, hC, hCeq⟩ :=
    exists_norm_eq_one_forall_eq_of_pseudoHyperbolicExpr_map_eq hf hmaps hz hw hne heq
  have hw_norm : ‖w‖ < 1 := by simpa [mem_ball_zero_iff] using hw
  have hnegw : ‖(-w : ℂ)‖ < 1 := by simpa using hw_norm
  have hfw_norm : ‖f w‖ < 1 := by simpa [mem_ball_zero_iff] using hmaps hw
  have hC0 : C ≠ 0 := fun h => zero_ne_one (by rw [h, norm_zero] at hC; exact hC)
  have hCinv : ‖C⁻¹‖ = 1 := by rw [norm_inv, hC, inv_one]
  have hT_diff := differentiableOn_unitDiscMoebiusFormula_of_norm_lt_one hfw_norm
  have hT_maps := mapsTo_ball_unitDiscMoebiusFormula_of_norm_lt_one hfw_norm
  have hS_diff := differentiableOn_unitDiscMoebiusFormula_of_norm_lt_one (a := -w) hnegw
  have hS_maps := mapsTo_ball_unitDiscMoebiusFormula_of_norm_lt_one (a := -w) hnegw
  have hR_diff : DifferentiableOn ℂ (fun η : ℂ => C⁻¹ * η) (ball (0 : ℂ) 1) :=
    differentiableOn_id.const_mul _
  -- The inverse rotation is a disc self-map because a ball at the origin is balanced.
  have hR_maps : MapsTo (fun η : ℂ => C⁻¹ * η) (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) :=
    fun η hη => by
      have h := (balanced_ball_zero (𝕜 := ℂ) (r := 1)).smul_mem hCinv.le hη
      rwa [smul_eq_mul] at h
  refine ⟨(fun ξ : ℂ => (ξ - (-w)) / (1 - (starRingEnd ℂ) (-w) * ξ)) ∘
      (fun η : ℂ => C⁻¹ * η) ∘
      (fun η : ℂ => (η - f w) / (1 - (starRingEnd ℂ) (f w) * η)), ?_, ?_, ?_, ?_⟩
  · exact hS_diff.comp (hR_diff.comp hT_diff hT_maps) (hR_maps.comp hT_maps)
  · exact hS_maps.comp (hR_maps.comp hT_maps)
  · -- `g (f ζ) = ζ`: the rotation and its inverse cancel, then the Moebius factors do.
    intro ζ hζ
    simp only [Function.comp_apply, hCeq ζ hζ, inv_mul_cancel_left₀ hC0]
    exact leftInvOn_unitDiscMoebiusFormula_of_norm_lt_one hw_norm hζ
  · exact rightInvOn_moebius_rotate_moebius_of_forall_eq hfw_norm hw_norm hC0 hR_maps hmaps hCeq

/--
**Schwarz--Pick rigidity, bijectivity form.**  A holomorphic self-map of the open unit disc
that preserves the pseudo-hyperbolic expression at one pair of distinct points is a bijection
of the disc, hence a conformal automorphism.
-/
theorem bijOn_ball_of_pseudoHyperbolicExpr_map_eq
    (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (hmaps : MapsTo f (ball (0 : ℂ) 1) (ball (0 : ℂ) 1))
    (hz : z ∈ ball (0 : ℂ) 1) (hw : w ∈ ball (0 : ℂ) 1) (hne : z ≠ w)
    (heq : pseudoHyperbolicExpr (f z) (f w) = pseudoHyperbolicExpr z w) :
    BijOn f (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) := by
  obtain ⟨g, _, hgmaps, hgf, hfg⟩ :=
    exists_differentiableOn_mapsTo_invOn_of_pseudoHyperbolicExpr_map_eq hf hmaps hz hw hne heq
  exact InvOn.bijOn ⟨hgf, hfg⟩ hmaps hgmaps

/--
**Schwarz--Pick rigidity, isometry form.**  One equality in the Schwarz--Pick estimate
propagates to every pair of points: the map preserves the pseudo-hyperbolic expression on the
whole disc.
-/
theorem forall_pseudoHyperbolicExpr_map_eq_of_pseudoHyperbolicExpr_map_eq
    (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (hmaps : MapsTo f (ball (0 : ℂ) 1) (ball (0 : ℂ) 1))
    (hz : z ∈ ball (0 : ℂ) 1) (hw : w ∈ ball (0 : ℂ) 1) (hne : z ≠ w)
    (heq : pseudoHyperbolicExpr (f z) (f w) = pseudoHyperbolicExpr z w) :
    ∀ p ∈ ball (0 : ℂ) 1, ∀ q ∈ ball (0 : ℂ) 1,
      pseudoHyperbolicExpr (f p) (f q) = pseudoHyperbolicExpr p q := by
  obtain ⟨g, hg, hgmaps, hgf, _⟩ :=
    exists_differentiableOn_mapsTo_invOn_of_pseudoHyperbolicExpr_map_eq hf hmaps hz hw hne heq
  exact fun p hp q hq => pseudoHyperbolicExpr_map_eq hf hmaps hg hgmaps hgf hp hq

/--
**Schwarz--Pick rigidity, classification form.**  A holomorphic self-map of the open unit disc
that preserves the pseudo-hyperbolic expression at one pair of distinct points is one of the
standard disc automorphisms `ζ ↦ u * (ζ - a) / (1 - conj a * ζ)`.
-/
theorem exists_forall_unitDisc_eq_unitDiscStandardAutomorphismEquiv_of_pseudoHyperbolicExpr_map_eq
    (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (hmaps : MapsTo f (ball (0 : ℂ) 1) (ball (0 : ℂ) 1))
    (hz : z ∈ ball (0 : ℂ) 1) (hw : w ∈ ball (0 : ℂ) 1) (hne : z ≠ w)
    (heq : pseudoHyperbolicExpr (f z) (f w) = pseudoHyperbolicExpr z w) :
    ∃ (u : Circle) (a : Complex.UnitDisc),
      ∀ ζ : Complex.UnitDisc, f ζ = (unitDiscStandardAutomorphismEquiv u a ζ : ℂ) := by
  obtain ⟨g, hg, hgmaps, hgf, hfg⟩ :=
    exists_differentiableOn_mapsTo_invOn_of_pseudoHyperbolicExpr_map_eq hf hmaps hz hw hne heq
  obtain ⟨u, a, _, hfa⟩ :=
    exists_forall_unitDisc_eq_unitDiscStandardAutomorphismEquiv hf hg hmaps hgmaps hgf hfg
  exact ⟨u, a, hfa⟩

/--
**Schwarz--Pick rigidity, hyperbolic-distance form.**  A holomorphic self-map of the open unit
disc that preserves the hyperbolic (Poincaré) distance between one pair of distinct points is a
hyperbolic isometry of the disc.
-/
theorem forall_hyperbolicDist_map_eq_of_hyperbolicDist_map_eq
    (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (hmaps : MapsTo f (ball (0 : ℂ) 1) (ball (0 : ℂ) 1))
    (hz : z ∈ ball (0 : ℂ) 1) (hw : w ∈ ball (0 : ℂ) 1) (hne : z ≠ w)
    (heq : hyperbolicDist (f z) (f w) = hyperbolicDist z w) :
    ∀ p ∈ ball (0 : ℂ) 1, ∀ q ∈ ball (0 : ℂ) 1,
      hyperbolicDist (f p) (f q) = hyperbolicDist p q := by
  have heq' : pseudoHyperbolicExpr (f z) (f w) = pseudoHyperbolicExpr z w :=
    (pseudoHyperbolicExpr_eq_iff_hyperbolicDist_eq (hmaps hz) (hmaps hw) hz hw).mpr heq
  intro p hp q hq
  exact (pseudoHyperbolicExpr_eq_iff_hyperbolicDist_eq (hmaps hp) (hmaps hq) hp hq).mp
    (forall_pseudoHyperbolicExpr_map_eq_of_pseudoHyperbolicExpr_map_eq hf hmaps hz hw hne heq'
      p hp q hq)

/--
**Schwarz--Pick rigidity, hyperbolic-distance classification form.**  A holomorphic self-map of
the open unit disc that preserves the hyperbolic distance between one pair of distinct points
is one of the standard disc automorphisms.
-/
theorem exists_forall_unitDisc_eq_unitDiscStandardAutomorphismEquiv_of_hyperbolicDist_map_eq
    (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (hmaps : MapsTo f (ball (0 : ℂ) 1) (ball (0 : ℂ) 1))
    (hz : z ∈ ball (0 : ℂ) 1) (hw : w ∈ ball (0 : ℂ) 1) (hne : z ≠ w)
    (heq : hyperbolicDist (f z) (f w) = hyperbolicDist z w) :
    ∃ (u : Circle) (a : Complex.UnitDisc),
      ∀ ζ : Complex.UnitDisc, f ζ = (unitDiscStandardAutomorphismEquiv u a ζ : ℂ) :=
  exists_forall_unitDisc_eq_unitDiscStandardAutomorphismEquiv_of_pseudoHyperbolicExpr_map_eq
    hf hmaps hz hw hne
    ((pseudoHyperbolicExpr_eq_iff_hyperbolicDist_eq (hmaps hz) (hmaps hw) hz hw).mpr heq)

end TauCeti
