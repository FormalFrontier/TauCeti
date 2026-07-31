/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Complex.Conformal.UnitDisc.Automorphism.Rotation

/-!
# Classification of holomorphic automorphisms of the complex unit disc

This file completes the classification of the holomorphic automorphisms of the open unit disc.
If `f` has a holomorphic two-sided inverse `g`, then on the disc

`f z = u * (z - a) / (1 - conj a * z)`

for a unique center `a = g 0` and some `u` of modulus one.  The proof conjugates `f` by the
Moebius factor that sends `a` to the origin, then applies the origin-fixing rotation theorem
`exists_eqOn_const_mul_of_leftInvOn_ball_of_map_zero`.

This discharges the conformal-mapping roadmap's L2 description of the disc automorphism group
`Aut(𝔻) = {e^{iθ}(z−a)/(1−āz)}`.  It builds on Mathlib's Schwarz lemma and on the standard
disc-Moebius API developed in Tau Ceti.  As with the other L0--L3 conformal-mapping material,
this statement is coordinated with the upstream Mathlib Riemann-mapping effort
leanprover-community/mathlib4#33505 and should be replaced by human-curated upstream API if a
disc-automorphism classification lands there.
-/

public section

namespace TauCeti

open _root_.Complex Metric Set
open scoped ComplexConjugate

variable {f g : ℂ → ℂ}

/--
**Classification of holomorphic disc automorphisms.** A holomorphic self-map `f` of the open
unit disc with a holomorphic two-sided inverse `g` has the standard form. Its center is `g 0`,
and its rotation factor lies on the unit circle.
-/
theorem exists_forall_unitDisc_eq_unitDiscStandardAutomorphismEquiv
    (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (hg : DifferentiableOn ℂ g (ball (0 : ℂ) 1))
    (hfmaps : MapsTo f (ball (0 : ℂ) 1) (ball (0 : ℂ) 1))
    (hgmaps : MapsTo g (ball (0 : ℂ) 1) (ball (0 : ℂ) 1))
    (hgf : LeftInvOn g f (ball (0 : ℂ) 1))
    (hfg : RightInvOn g f (ball (0 : ℂ) 1)) :
    ∃ (u : Circle) (a : Complex.UnitDisc), (a : ℂ) = g 0 ∧
      ∀ z : Complex.UnitDisc, f z = (unitDiscStandardAutomorphismEquiv u a z : ℂ) := by
  have hzero : (0 : ℂ) ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff]
    norm_num
  have hfg0 : f (g 0) = 0 := hfg hzero
  have ha_mem : g 0 ∈ ball (0 : ℂ) 1 := hgmaps hzero
  have ha : ‖g 0‖ < 1 := by simpa [mem_ball_zero_iff] using ha_mem
  let F : ℂ → ℂ := f ∘ fun z =>
    (z - (-(g 0))) / (1 - (starRingEnd ℂ) (-(g 0)) * z)
  let G : ℂ → ℂ := (fun z =>
    (z - g 0) / (1 - (starRingEnd ℂ) (g 0) * z)) ∘ g
  have hneg : ‖-(g 0)‖ < 1 := by simpa using ha
  have hFdata : DifferentiableOn ℂ F (ball (0 : ℂ) 1) ∧
      MapsTo F (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) ∧ F 0 = 0 := by
    -- The target factor is centered at `f (g 0) = 0`, so it simplifies to the identity.
    simpa [F, hfg0, Function.comp_def] using
      differentiableOn_and_mapsTo_ball_and_apply_zero_schwarzPickConjugate hf hfmaps ha
  obtain ⟨hFdiff, hFmaps, hFzero⟩ := hFdata
  have hGdiff : DifferentiableOn ℂ G (ball (0 : ℂ) 1) :=
    (differentiableOn_unitDiscMoebiusFormula_of_norm_lt_one ha).comp hg hgmaps
  have hGmaps : MapsTo G (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) :=
    (mapsTo_ball_unitDiscMoebiusFormula_of_norm_lt_one ha).comp hgmaps
  have hGF : LeftInvOn G F (ball (0 : ℂ) 1) := by
    intro z hz
    simp only [F, G, Function.comp_apply]
    rw [hgf ((mapsTo_ball_unitDiscMoebiusFormula_of_norm_lt_one hneg) hz)]
    simpa only [neg_neg] using
      leftInvOn_unitDiscMoebiusFormula_of_norm_lt_one (a := -(g 0)) hneg hz
  obtain ⟨u, hu, hFu⟩ :=
    exists_eqOn_const_mul_of_leftInvOn_ball_of_map_zero hFdiff hGdiff hFmaps hGmaps hGF hFzero
  refine ⟨⟨u, by
      have hmem : u ∈ (↑(Submonoid.unitSphere ℂ) : Set ℂ) := by
        rw [Submonoid.coe_unitSphere]
        exact mem_sphere_zero_iff_norm.mpr hu
      exact hmem⟩,
    Complex.UnitDisc.mk (g 0) ha, Complex.UnitDisc.coe_mk _ _, fun z => ?_⟩
  have hz : (z : ℂ) ∈ ball (0 : ℂ) 1 := by
    simpa [mem_ball_zero_iff] using z.norm_lt_one
  have hMz : ((z : ℂ) - g 0) / (1 - (starRingEnd ℂ) (g 0) * (z : ℂ)) ∈
      ball (0 : ℂ) 1 := mapsTo_ball_unitDiscMoebiusFormula_of_norm_lt_one ha hz
  have hF := hFu hMz
  simp only [F, Function.comp_apply] at hF
  have hInv := leftInvOn_unitDiscMoebiusFormula_of_norm_lt_one ha hz
  -- Beta-reduce the two scalar Moebius formulas so the inverse equality rewrites `hF`.
  dsimp only at hInv
  rw [hInv] at hF
  erw [coe_unitDiscStandardAutomorphismEquiv_apply]
  simpa only [Complex.UnitDisc.coe_mk] using hF

end TauCeti
