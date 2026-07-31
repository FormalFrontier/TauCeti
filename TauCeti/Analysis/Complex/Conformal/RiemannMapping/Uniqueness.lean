/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Complex.Conformal.UnitDisc.Automorphism.Classification
import TauCeti.Analysis.Complex.Conformal.InverseFunction

/-!
# Uniqueness in the Riemann mapping theorem

This file proves the uniqueness companion to the Riemann mapping theorem. Two biholomorphic maps
from the same open subset of `ℂ` onto the unit disc differ by a standard disc automorphism. If
both maps send the same base point to zero, that automorphism is a rotation.

The proof uses the classical transition-map argument: the inverse of one map is holomorphic on its
image, so composing it with the other map gives a holomorphic automorphism of the disc. The
classification in
`TauCeti.Analysis.Complex.Conformal.UnitDisc.Automorphism.Classification` then supplies the
standard Moebius formula. The inverse is represented by Mathlib's `Function.invFunOn`; its
holomorphy follows from Mathlib's analytic inverse-function theorem and Tau Ceti's local
injectivity criterion.

This advances `TauCetiRoadmap/ConformalMapping/README.md`, layer L3, specifically “Uniqueness up
to `Aut(𝔻)`”. The argument follows Ahlfors, *Complex Analysis*, Chapter 6. As with all L0--L3
material in this roadmap, it is coordinated with the upstream Riemann-mapping work in
leanprover-community/mathlib4#33505 and should be replaced by public human-curated Mathlib API
when that becomes available.
-/

public section

namespace TauCeti

open _root_.Complex Filter Function Metric Set
open scoped ComplexConjugate Topology

/--
**Uniqueness in the Riemann mapping theorem, up to a disc automorphism.** If `f` and `g` are
holomorphic injections from an open set `U` onto the open unit disc, then there are `u` on the
unit circle and `a` in the unit disc such that

`g z = u * (f z - a) / (1 - conj a * f z)`

for every `z ∈ U`.
-/
theorem exists_eqOn_unitDiscStandardAutomorphismFormula_comp {U : Set ℂ} (hU : IsOpen U)
    {f g : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U)
    (hfi : InjOn f U) (hgi : InjOn g U)
    (hfimage : f '' U = ball (0 : ℂ) 1) (hgimage : g '' U = ball (0 : ℂ) 1) :
    ∃ (u : Circle) (a : Complex.UnitDisc),
      EqOn g
        (fun z =>
          (u : ℂ) *
            ((f z - (a : ℂ)) / (1 - (starRingEnd ℂ) (a : ℂ) * f z)))
        U := by
  obtain ⟨hf_surj, hf_maps⟩ := image_eq_iff_surjOn_mapsTo.mp hfimage
  obtain ⟨hg_surj, hg_maps⟩ := image_eq_iff_surjOn_mapsTo.mp hgimage
  let F : ℂ → ℂ := g ∘ Function.invFunOn f U
  let G : ℂ → ℂ := f ∘ Function.invFunOn g U
  have hfinv : DifferentiableOn ℂ (Function.invFunOn f U) (ball (0 : ℂ) 1) := by
    rw [← hfimage]
    exact DifferentiableOn.invFunOn hf hU hfi
  have hginv : DifferentiableOn ℂ (Function.invFunOn g U) (ball (0 : ℂ) 1) := by
    rw [← hgimage]
    exact DifferentiableOn.invFunOn hg hU hgi
  have hFdiff : DifferentiableOn ℂ F (ball (0 : ℂ) 1) :=
    hg.comp hfinv hf_surj.mapsTo_invFunOn
  have hGdiff : DifferentiableOn ℂ G (ball (0 : ℂ) 1) :=
    hf.comp hginv hg_surj.mapsTo_invFunOn
  have hFmaps : MapsTo F (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) :=
    hg_maps.comp hf_surj.mapsTo_invFunOn
  have hGmaps : MapsTo G (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) :=
    hf_maps.comp hg_surj.mapsTo_invFunOn
  have hGF : LeftInvOn G F (ball (0 : ℂ) 1) := by
    intro z hz
    simp only [F, G, Function.comp_apply]
    rw [hgi.leftInvOn_invFunOn (hf_surj.mapsTo_invFunOn hz)]
    exact hf_surj.rightInvOn_invFunOn hz
  have hFG : RightInvOn G F (ball (0 : ℂ) 1) := by
    intro z hz
    simp only [F, G, Function.comp_apply]
    rw [hfi.leftInvOn_invFunOn (hg_surj.mapsTo_invFunOn hz)]
    exact hg_surj.rightInvOn_invFunOn hz
  obtain ⟨u, a, _, hclass⟩ :=
    exists_forall_unitDisc_eq_unitDiscStandardAutomorphismEquiv
      hFdiff hGdiff hFmaps hGmaps hGF hFG
  refine ⟨u, a, fun z hz => ?_⟩
  have hfz : ‖f z‖ < 1 := by
    simpa [mem_ball_zero_iff] using hf_maps hz
  have hclass_z := hclass (Complex.UnitDisc.mk (f z) hfz)
  rw [coe_unitDiscStandardAutomorphismEquiv_apply] at hclass_z
  have hFz : F (f z) = g z := by
    simp only [F, Function.comp_apply]
    rw [hfi.leftInvOn_invFunOn hz]
  rw [← hFz]
  simpa using hclass_z

/--
**Normalized uniqueness in the Riemann mapping theorem.** If two biholomorphic maps onto the unit
disc send the same point of their domain to zero, then they differ by a rotation of the disc.
-/
theorem exists_eqOn_const_mul_of_image_eq_ball_of_apply_eq_zero {U : Set ℂ} (hU : IsOpen U)
    {f g : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U)
    (hfi : InjOn f U) (hgi : InjOn g U)
    (hfimage : f '' U = ball (0 : ℂ) 1) (hgimage : g '' U = ball (0 : ℂ) 1)
    {z₀ : ℂ} (hz₀ : z₀ ∈ U) (hfzero : f z₀ = 0) (hgzero : g z₀ = 0) :
    ∃ u : Circle, EqOn g (fun z => (u : ℂ) * f z) U := by
  obtain ⟨u, a, hfg⟩ :=
    exists_eqOn_unitDiscStandardAutomorphismFormula_comp
      hU hf hg hfi hgi hfimage hgimage
  have hzero := hfg hz₀
  dsimp only at hzero
  rw [hfzero, hgzero] at hzero
  have hu : (u : ℂ) ≠ 0 := by
    intro hu
    have := Circle.norm_coe u
    rw [hu, norm_zero] at this
    norm_num at this
  have ha : (a : ℂ) = 0 := by
    have hua : (u : ℂ) * (-(a : ℂ)) = 0 := by simpa using hzero.symm
    exact neg_eq_zero.mp ((mul_eq_zero.mp hua).resolve_left hu)
  refine ⟨u, fun z hz => ?_⟩
  have hz_eq := hfg hz
  rw [ha] at hz_eq
  simpa using hz_eq

end TauCeti
