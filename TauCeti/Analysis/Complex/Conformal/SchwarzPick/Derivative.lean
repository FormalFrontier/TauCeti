/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Complex.UnitDisc.Basic
public import Mathlib.Data.Set.Function
import Mathlib.Analysis.Complex.Schwarz
import TauCeti.Analysis.Complex.Conformal.Moebius

/-!
# The infinitesimal Schwarz--Pick inequality

This file proves the differential (infinitesimal) form of the Schwarz--Pick lemma for
holomorphic self-maps of the complex unit disc: if `f` is holomorphic on `ball 0 1` and maps
it into itself, then at every point `z` of the disc
`‖deriv f z‖ / (1 - ‖f z‖ ^ 2) ≤ 1 / (1 - ‖z‖ ^ 2)`, i.e. `f` contracts the Poincaré
(hyperbolic) metric `|dz| / (1 - |z| ^ 2)`.  The bundled `Complex.UnitDisc` form is
`norm_deriv_div_one_sub_norm_sq_le_unitDisc`.

This advances the conformal-mapping roadmap's **L2 Schwarz--Pick** target
(`TauCetiRoadmap/ConformalMapping/README.md`, the L2 hyperbolic/Poincaré-metric contraction),
complementing Tau Ceti's finite Schwarz--Pick estimate `pseudoHyperbolicExpr_map_le`.  It
reuses Mathlib's Schwarz lemma (`Complex.norm_deriv_le_one_of_mapsTo_ball`) and Tau Ceti's
unit-disc Moebius API.  As with the rest of the L0--L3 conformal-mapping material, it is
coordinated with the upstream Mathlib RMT effort leanprover-community/mathlib4#33505 and
should be refactored to upstream API if that work lands a human-curated Schwarz--Pick theorem.
-/

public section

namespace TauCeti

open Complex Metric Set
open scoped ComplexConjugate

/-- **Chain rule for the infinitesimal Schwarz--Pick conjugate.** For the composite
`target ∘ f ∘ source` of two unit-disc Moebius factors around `f`, given the factor derivatives
`1 - conj z * z` (of `source` at `0`, where `source 0 = z`) and `1 / (1 - conj (f z) * f z)` (of
`target` at `f z`), the norm of the derivative of the composite at the origin equals the Poincaré
distortion `‖df‖ * (1 - ‖z‖ ^ 2) / (1 - ‖f z‖ ^ 2)`. -/
private lemma norm_deriv_schwarzPickConjugate_at_zero {source target f : ℂ → ℂ} {df z : ℂ}
    (hz : ‖z‖ ≤ 1) (hfz : ‖f z‖ ≤ 1)
    (hs : HasDerivAt source (1 - (starRingEnd ℂ) z * z) 0) (hsz : source 0 = z)
    (hf : HasDerivAt f df z)
    (ht : HasDerivAt target (1 / (1 - (starRingEnd ℂ) (f z) * f z)) (f z)) :
    ‖deriv (target ∘ f ∘ source) 0‖ = ‖df‖ * (1 - ‖z‖ ^ 2) / (1 - ‖f z‖ ^ 2) := by
  have hf' : HasDerivAt f df (source 0) := by rw [hsz]; exact hf
  have ht' : HasDerivAt target (1 / (1 - (starRingEnd ℂ) (f z) * f z)) ((f ∘ source) 0) := by
    rw [Function.comp_apply, hsz]; exact ht
  rw [(ht'.comp (0 : ℂ) (hf'.comp (0 : ℂ) hs)).deriv, norm_mul, norm_mul, norm_div, norm_one,
    norm_one_sub_conj_mul_self_of_norm_le_one hz,
    norm_one_sub_conj_mul_self_of_norm_le_one hfz]
  ring

/-- **The infinitesimal Schwarz--Pick inequality.** A holomorphic self-map `f` of the open
unit disc contracts the Poincaré metric: at every point `z` of the disc,
`‖deriv f z‖ / (1 - ‖f z‖ ^ 2) ≤ 1 / (1 - ‖z‖ ^ 2)`. -/
theorem norm_deriv_div_one_sub_norm_sq_le {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (hmaps : MapsTo f (ball (0 : ℂ) 1) (ball (0 : ℂ) 1))
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    ‖deriv f z‖ / (1 - ‖f z‖ ^ 2) ≤ 1 / (1 - ‖z‖ ^ 2) := by
  have hz1 : ‖z‖ < 1 := by simpa [mem_ball_zero_iff] using hz
  have hfz1 : ‖f z‖ < 1 := by simpa [mem_ball_zero_iff] using hmaps hz
  have hden_z : (0 : ℝ) < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have hden_fz : (0 : ℝ) < 1 - ‖f z‖ ^ 2 := by nlinarith [norm_nonneg (f z)]
  -- Conjugate `f` by the disc automorphisms centred at `-z` and `f z` so the conjugate fixes `0`.
  let source : ℂ → ℂ := fun ξ => (ξ - (-z)) / (1 - (starRingEnd ℂ) (-z) * ξ)
  let target : ℂ → ℂ := fun η => (η - f z) / (1 - (starRingEnd ℂ) (f z) * η)
  let g : ℂ → ℂ := target ∘ f ∘ source
  obtain ⟨hg_diff, hg_maps, hg_zero'⟩ :=
    differentiableOn_and_mapsTo_ball_and_apply_zero_schwarzPickConjugate hf hmaps hz1
  have hg_zero : g 0 = 0 := hg_zero'
  have hsource_zero : source 0 = z := by simp [source]
  -- Schwarz's lemma at `0` for the conjugate `g`.
  have hschwarz : ‖deriv g 0‖ ≤ 1 := by
    have hmaps' : MapsTo g (ball (0 : ℂ) 1) (closedBall (g 0) 1) := by
      rw [hg_zero]; exact fun ξ hξ => ball_subset_closedBall (hg_maps hξ)
    exact Complex.norm_deriv_le_one_of_mapsTo_ball hg_diff hmaps' (by norm_num)
  -- The chain rule turns Schwarz's bound `‖deriv g 0‖ ≤ 1` into the estimate for `f`.
  have hf_at : HasDerivAt f (deriv f z) z :=
    (hf.differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt
  have hp_outer : (1 : ℂ) - (starRingEnd ℂ) (f z) * f z ≠ 0 :=
    one_sub_conj_mul_ne_zero_of_norm_lt_one hfz1 hfz1
  -- The two Möbius factor derivatives, specialised from `hasDerivAt_unitDiscMoebiusFormula`.
  have hs : HasDerivAt source (1 - (starRingEnd ℂ) z * z) 0 := by
    have h := hasDerivAt_unitDiscMoebiusFormula (-z) 0 (by simp)
    have hval : (1 - (starRingEnd ℂ) (-z) * (-z)) / (1 - (starRingEnd ℂ) (-z) * 0) ^ 2
        = 1 - (starRingEnd ℂ) z * z := by simp [map_neg]
    rwa [hval] at h
  have ht : HasDerivAt target (1 / (1 - (starRingEnd ℂ) (f z) * f z)) (f z) := by
    have h := hasDerivAt_unitDiscMoebiusFormula (f z) (f z) hp_outer
    have hval : (1 - (starRingEnd ℂ) (f z) * f z) / (1 - (starRingEnd ℂ) (f z) * f z) ^ 2
        = 1 / (1 - (starRingEnd ℂ) (f z) * f z) := by rw [sq, ← div_div, div_self hp_outer]
    rwa [hval] at h
  have hnorm_dg : ‖deriv g 0‖ = ‖deriv f z‖ * (1 - ‖z‖ ^ 2) / (1 - ‖f z‖ ^ 2) :=
    norm_deriv_schwarzPickConjugate_at_zero hz1.le hfz1.le hs hsource_zero hf_at ht
  have hkey : ‖deriv f z‖ * (1 - ‖z‖ ^ 2) / (1 - ‖f z‖ ^ 2) ≤ 1 := hnorm_dg ▸ hschwarz
  rw [div_le_one hden_fz] at hkey
  rw [div_le_div_iff₀ hden_fz hden_z, one_mul]
  exact hkey

/-- Bundled unit-disc form of the infinitesimal Schwarz--Pick inequality: a holomorphic
self-map `f` of the open unit disc contracts the Poincaré metric at every disc point `z`. -/
theorem norm_deriv_div_one_sub_norm_sq_le_unitDisc {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (hmaps : MapsTo f (ball (0 : ℂ) 1) (ball (0 : ℂ) 1))
    (z : Complex.UnitDisc) :
    ‖deriv f (z : ℂ)‖ / (1 - ‖f (z : ℂ)‖ ^ 2) ≤ 1 / (1 - ‖(z : ℂ)‖ ^ 2) :=
  norm_deriv_div_one_sub_norm_sq_le hf hmaps z.property

end TauCeti
