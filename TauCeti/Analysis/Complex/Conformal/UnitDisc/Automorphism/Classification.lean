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
leanprover-community/mathlib4#33505, whose preceding human-curated work is
`Analysis/Complex/RiemannMapping.lean` and `Analysis/Complex/BranchLogRoot.lean`; none of it is
duplicated here, and this statement should be replaced by human-curated upstream API if a
disc-automorphism classification lands there.
-/

public section

namespace TauCeti

open _root_.Complex Metric Set
open scoped ComplexConjugate

variable {f g : ℂ → ℂ}

-- Conjugating `f` by the Moebius factor centred at `a` produces a disc self-map fixing the
-- origin, with `M_a ∘ g` as a left inverse; the origin-fixing rotation theorem then applies.
-- Only `f (a) = 0` is used, not the full right-inverse property that supplies it.
private lemma exists_norm_eq_one_eqOn_comp_unitDiscMoebiusFormula {a : ℂ} (ha : ‖a‖ < 1)
    (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1)) (hg : DifferentiableOn ℂ g (ball (0 : ℂ) 1))
    (hfmaps : MapsTo f (ball (0 : ℂ) 1) (ball (0 : ℂ) 1))
    (hgmaps : MapsTo g (ball (0 : ℂ) 1) (ball (0 : ℂ) 1))
    (hgf : LeftInvOn g f (ball (0 : ℂ) 1)) (hfa : f a = 0) :
    ∃ u : ℂ, ‖u‖ = 1 ∧
      EqOn (f ∘ fun z : ℂ => (z - -a) / (1 - (starRingEnd ℂ) (-a) * z))
        (fun z => u * z) (ball (0 : ℂ) 1) := by
  have hneg : ‖(-a : ℂ)‖ < 1 := by simpa using ha
  have hFdata : DifferentiableOn ℂ (f ∘ fun z : ℂ => (z - -a) /
        (1 - (starRingEnd ℂ) (-a) * z)) (ball (0 : ℂ) 1) ∧
      MapsTo (f ∘ fun z : ℂ => (z - -a) / (1 - (starRingEnd ℂ) (-a) * z))
        (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) ∧
      (f ∘ fun z : ℂ => (z - -a) / (1 - (starRingEnd ℂ) (-a) * z)) 0 = 0 := by
    -- The target factor is centred at `f a = 0`, so it simplifies to the identity.
    simpa [schwarzPickConjugate_def, hfa, Function.comp_def] using
      differentiableOn_and_mapsTo_ball_and_apply_zero_schwarzPickConjugate hf hfmaps ha
  obtain ⟨hFdiff, hFmaps, hFzero⟩ := hFdata
  -- The two Moebius factors invert one another, so `M_a ∘ g` inverts `f ∘ M₋ₐ` by composition.
  have hMinv : LeftInvOn (fun z : ℂ => (z - a) / (1 - (starRingEnd ℂ) a * z))
      (fun z : ℂ => (z - -a) / (1 - (starRingEnd ℂ) (-a) * z)) (ball (0 : ℂ) 1) := by
    simpa only [neg_neg] using leftInvOn_unitDiscMoebiusFormula_of_norm_lt_one hneg
  exact exists_eqOn_const_mul_of_leftInvOn_ball_of_map_zero hFdiff
    ((differentiableOn_unitDiscMoebiusFormula_of_norm_lt_one ha).comp hg hgmaps)
    hFmaps ((mapsTo_ball_unitDiscMoebiusFormula_of_norm_lt_one ha).comp hgmaps)
    (hMinv.comp hgf (mapsTo_ball_unitDiscMoebiusFormula_of_norm_lt_one hneg)) hFzero

-- Undo the conjugation: a rotation on the conjugate is the standard form on `f` itself.
private lemma forall_eq_const_mul_unitDiscMoebiusFormula_of_eqOn_comp {a u : ℂ} (ha : ‖a‖ < 1)
    (h : EqOn (f ∘ fun z : ℂ => (z - -a) / (1 - (starRingEnd ℂ) (-a) * z))
      (fun z => u * z) (ball (0 : ℂ) 1)) :
    ∀ z ∈ ball (0 : ℂ) 1, f z = u * ((z - a) / (1 - (starRingEnd ℂ) a * z)) := by
  intro z hz
  have hF := h (mapsTo_ball_unitDiscMoebiusFormula_of_norm_lt_one ha hz)
  simp only [Function.comp_apply] at hF
  have hInv := leftInvOn_unitDiscMoebiusFormula_of_norm_lt_one ha hz
  -- Beta-reduce the scalar Moebius formula so the inverse equality rewrites `hF`.
  dsimp only at hInv
  rwa [hInv] at hF

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
  have ha : ‖g 0‖ < 1 := by simpa [mem_ball_zero_iff] using hgmaps hzero
  obtain ⟨u, hu, hFu⟩ := exists_norm_eq_one_eqOn_comp_unitDiscMoebiusFormula ha hf hg hfmaps
    hgmaps hgf (hfg hzero)
  have hform := forall_eq_const_mul_unitDiscMoebiusFormula_of_eqOn_comp ha hFu
  refine ⟨⟨u, by
      have hmem : u ∈ (↑(Submonoid.unitSphere ℂ) : Set ℂ) := by
        rw [Submonoid.coe_unitSphere]
        exact mem_sphere_zero_iff_norm.mpr hu
      exact hmem⟩,
    Complex.UnitDisc.mk (g 0) ha, Complex.UnitDisc.coe_mk _ _, fun z => ?_⟩
  have hz : (z : ℂ) ∈ ball (0 : ℂ) 1 := by
    simpa [mem_ball_zero_iff] using z.norm_lt_one
  erw [coe_unitDiscStandardAutomorphismEquiv_apply]
  simpa only [Complex.UnitDisc.coe_mk] using hform (z : ℂ) hz

end TauCeti
