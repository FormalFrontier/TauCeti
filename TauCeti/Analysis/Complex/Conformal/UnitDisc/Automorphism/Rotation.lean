/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Complex.Schwarz
public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Data.Set.Function
public import TauCeti.Analysis.Complex.Conformal.SchwarzPick.Isometry
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# A holomorphic automorphism of the unit disc fixing the origin is a rotation

This file records the Schwarz-lemma rigidity for the complex unit disc: a holomorphic self-map
`f` of `Metric.ball (0 : ℂ) 1` that admits a holomorphic left inverse which is itself a self-map
of the disc, and that fixes the origin, is a rotation `z ↦ c * z` for a constant `c` of modulus
one.  Equivalently, the rotation factor is `deriv f 0`, and such a map with derivative `1` at
the origin is the identity.  (The left inverse gives injectivity; that `f` is in fact a genuine
automorphism is part of the conclusion, since a rotation is bijective.)

The proof is the classical two-sided Schwarz argument.  Applying Mathlib's Schwarz lemma
(`Complex.norm_le_norm_of_mapsTo_ball`) to `f` and to its inverse gives `‖f z‖ = ‖z‖` on the
whole disc; the equality case of the Schwarz lemma
(`Complex.affine_of_mapsTo_ball_of_norm_dslope_eq_div`) then forces `f` to be linear.

This advances the conformal-mapping roadmap's L2 disc-automorphism target
(`TauCetiRoadmap/ConformalMapping/README.md`, layer L2: "the disc automorphism group
`Aut(𝔻) = {e^{iθ}(z−a)/(1−āz)}`"); it is the rotation rigidity that pins down the automorphisms
fixing the origin, and is the step Mathlib's `Analysis/Complex/Schwarz.lean` lists as an open
TODO ("Prove that any diffeomorphism of the unit disk to itself is a Möbius map").  It reuses
Mathlib's Schwarz lemma throughout and adds no new complex-analytic input.  As with the rest of
the L0--L3 conformal-mapping material, it is coordinated with the upstream Mathlib RMT effort
leanprover-community/mathlib4#33505 and should be refactored to upstream API if that work lands a
human-curated disc-automorphism classification.
-/

public section

namespace TauCeti

open _root_.Complex Metric Set
open scoped ComplexConjugate Topology

variable {f g : ℂ → ℂ}

/--
A holomorphic self-map of the open unit disc fixing the origin and admitting a holomorphic left
inverse that is itself a self-map of the disc preserves the modulus: `‖f z‖ = ‖z‖` for every
`z` in the disc.

This is the `w = 0` case of the Schwarz--Pick equality `pseudoHyperbolicExpr_map_eq`, where the
pseudo-hyperbolic expression to the origin is just the norm.
-/
theorem norm_map_of_leftInvOn_ball_of_map_zero
    (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (hg : DifferentiableOn ℂ g (ball (0 : ℂ) 1))
    (hfmaps : MapsTo f (ball (0 : ℂ) 1) (ball (0 : ℂ) 1))
    (hgmaps : MapsTo g (ball (0 : ℂ) 1) (ball (0 : ℂ) 1))
    (hgf : ∀ z ∈ ball (0 : ℂ) 1, g (f z) = z) (hf0 : f 0 = 0)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) : ‖f z‖ = ‖z‖ := by
  have h := pseudoHyperbolicExpr_map_eq hf hfmaps hg hgmaps hgf hz (mem_ball_self one_pos)
  rwa [hf0, pseudoHyperbolicExpr_zero_right, pseudoHyperbolicExpr_zero_right] at h

/--
**Rotation rigidity for the unit disc.** A holomorphic self-map `f` of the open unit disc with a
holomorphic left inverse `g` that is also a self-map of the disc, fixing the origin, is a
rotation: there is a constant `c` of modulus one with `f z = c * z` throughout the disc.
-/
theorem exists_eqOn_const_mul_of_leftInvOn_ball_of_map_zero
    (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (hg : DifferentiableOn ℂ g (ball (0 : ℂ) 1))
    (hfmaps : MapsTo f (ball (0 : ℂ) 1) (ball (0 : ℂ) 1))
    (hgmaps : MapsTo g (ball (0 : ℂ) 1) (ball (0 : ℂ) 1))
    (hgf : ∀ z ∈ ball (0 : ℂ) 1, g (f z) = z) (hf0 : f 0 = 0) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ EqOn f (fun z => c * z) (ball (0 : ℂ) 1) := by
  have hnorm : ∀ z ∈ ball (0 : ℂ) 1, ‖f z‖ = ‖z‖ := fun z hz =>
    norm_map_of_leftInvOn_ball_of_map_zero hf hg hfmaps hgmaps hgf hf0 hz
  -- Evaluate the derivative-slope at the interior point `1 / 2`.
  set z₀ : ℂ := 1 / 2 with hz₀_def
  have hz₀_mem : z₀ ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, hz₀_def]
    norm_num
  have hz₀_ne : z₀ ≠ 0 := by
    rw [hz₀_def]; norm_num
  -- The slope `dslope f 0 z₀ = f z₀ / z₀` has modulus one because `f` preserves the modulus.
  have hslope : dslope f 0 z₀ = f z₀ / z₀ := by
    rw [dslope_of_ne _ hz₀_ne, slope_def_field, hf0, sub_zero, sub_zero]
  have hkey : ‖dslope f 0 z₀‖ = 1 := by
    rw [hslope, norm_div, hnorm z₀ hz₀_mem]
    exact div_self (norm_ne_zero_iff.mpr hz₀_ne)
  -- The equality case of the Schwarz lemma makes `f` affine with this slope.
  set c : ℂ := dslope f 0 z₀ with hc_def
  have hmaps_closed : MapsTo f (ball (0 : ℂ) 1) (closedBall (f 0) 1) := by
    rw [hf0]; exact hfmaps.mono_right ball_subset_closedBall
  have haff := Complex.affine_of_mapsTo_ball_of_norm_dslope_eq_div hf hmaps_closed hz₀_mem
    (by rw [← hc_def, hkey]; norm_num)
  refine ⟨c, hkey, fun z hz => ?_⟩
  have h := haff hz
  simp only [hf0, sub_zero, zero_add, smul_eq_mul, ← hc_def] at h
  rw [mul_comm] at h
  simpa using h

/--
The rotation factor of an origin-fixing self-map of the disc with a holomorphic self-map left
inverse is its derivative at the origin: with the hypotheses of
`exists_eqOn_const_mul_of_leftInvOn_ball_of_map_zero`, the map equals `z ↦ deriv f 0 * z` on the
disc, and `‖deriv f 0‖ = 1`.
-/
theorem eqOn_deriv_zero_mul_of_leftInvOn_ball_of_map_zero
    (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (hg : DifferentiableOn ℂ g (ball (0 : ℂ) 1))
    (hfmaps : MapsTo f (ball (0 : ℂ) 1) (ball (0 : ℂ) 1))
    (hgmaps : MapsTo g (ball (0 : ℂ) 1) (ball (0 : ℂ) 1))
    (hgf : ∀ z ∈ ball (0 : ℂ) 1, g (f z) = z) (hf0 : f 0 = 0) :
    ‖deriv f 0‖ = 1 ∧ EqOn f (fun z => deriv f 0 * z) (ball (0 : ℂ) 1) := by
  obtain ⟨c, hc, hEqOn⟩ :=
    exists_eqOn_const_mul_of_leftInvOn_ball_of_map_zero hf hg hfmaps hgmaps hgf hf0
  -- `f` agrees with the linear map `z ↦ c * z` on a neighbourhood of `0`, so `deriv f 0 = c`.
  have hev : f =ᶠ[𝓝 (0 : ℂ)] fun z => c * z :=
    hEqOn.eventuallyEq_of_mem (isOpen_ball.mem_nhds (mem_ball_self one_pos))
  have hd : HasDerivAt (fun z : ℂ => c * z) c 0 := by
    simpa using (hasDerivAt_id (0 : ℂ)).const_mul c
  have hderiv : deriv f 0 = c := by
    rw [hev.deriv_eq, hd.deriv]
  rw [hderiv]
  exact ⟨hc, hEqOn⟩

/--
**Uniqueness of the identity.** An origin-fixing holomorphic self-map of the unit disc with a
holomorphic self-map left inverse, whose derivative at the origin is `1`, is the identity on the
disc.
-/
theorem eqOn_id_of_leftInvOn_ball_of_map_zero_of_deriv_zero_eq_one
    (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (hg : DifferentiableOn ℂ g (ball (0 : ℂ) 1))
    (hfmaps : MapsTo f (ball (0 : ℂ) 1) (ball (0 : ℂ) 1))
    (hgmaps : MapsTo g (ball (0 : ℂ) 1) (ball (0 : ℂ) 1))
    (hgf : ∀ z ∈ ball (0 : ℂ) 1, g (f z) = z) (hf0 : f 0 = 0)
    (hderiv : deriv f 0 = 1) : EqOn f id (ball (0 : ℂ) 1) := by
  obtain ⟨_, hEqOn⟩ :=
    eqOn_deriv_zero_mul_of_leftInvOn_ball_of_map_zero hf hg hfmaps hgmaps hgf hf0
  intro z hz
  have h := hEqOn hz
  simp only [hderiv, one_mul, id_eq] at h ⊢
  exact h

end TauCeti
