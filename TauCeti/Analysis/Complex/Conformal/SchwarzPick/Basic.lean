/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Data.Set.Function
public import TauCeti.Analysis.Complex.Conformal.PseudoHyperbolic
import Mathlib.Analysis.Complex.Schwarz
import TauCeti.Analysis.Complex.Conformal.Moebius

/-!
# Schwarz--Pick for the pseudo-hyperbolic expression

This file proves the Schwarz--Pick contraction estimate for holomorphic self-maps of the
complex unit disc, stated using Tau Ceti's pseudo-hyperbolic expression
`pseudoHyperbolicExpr z w = ‖(z - w) / (1 - conj w * z)‖`.

It provides the pseudo-hyperbolic expression statement, plus a bundled `Complex.UnitDisc` form
for callers working directly with disc points.

This advances the conformal-mapping roadmap's L2 Schwarz--Pick target.  It reuses Mathlib's
Schwarz lemma and Tau Ceti's unit-disc Moebius API.  As with the rest of the L0--L3
conformal-mapping material, it is coordinated with the upstream Mathlib RMT effort
leanprover-community/mathlib4#33505 and should be refactored to upstream API if that work
lands a human-curated Schwarz--Pick theorem.
-/

public section

namespace TauCeti

open Complex Metric Set
open scoped ComplexConjugate

/--
The Schwarz--Pick contraction estimate for the pseudo-hyperbolic expression on the open unit
disc.
-/
theorem pseudoHyperbolicExpr_map_le {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (hmaps : MapsTo f (ball (0 : ℂ) 1) (ball (0 : ℂ) 1))
    {z w : ℂ} (hz : z ∈ ball (0 : ℂ) 1) (hw : w ∈ ball (0 : ℂ) 1) :
    pseudoHyperbolicExpr (f z) (f w) ≤ pseudoHyperbolicExpr z w := by
  -- Conjugate `f` by the disc automorphisms sending `w ↦ 0` and `f w ↦ 0`, so the conjugated
  -- map `g = target ∘ f ∘ source` fixes `0`.  Mathlib's Schwarz lemma at `0` then gives
  -- `‖g ξ‖ ≤ ‖ξ‖`, which unwinds to the pseudo-hyperbolic contraction at `z`, `w`.
  let source : ℂ → ℂ :=
    fun ξ => (ξ - (-(w : ℂ))) / (1 - (starRingEnd ℂ) (-(w : ℂ)) * ξ)
  let target : ℂ → ℂ :=
    fun η => (η - f w) / (1 - (starRingEnd ℂ) (f w) * η)
  let g : ℂ → ℂ := target ∘ f ∘ source
  have hw_norm : ‖w‖ < 1 := by
    simpa [mem_ball_zero_iff] using hw
  -- The conjugate `g` is a holomorphic self-map of the disc fixing the origin (shared scaffold).
  obtain ⟨hg_diff, hg_maps_ball, hg_zero⟩ :=
    differentiableOn_and_mapsTo_ball_and_apply_zero_schwarzPickConjugate hf hmaps hw_norm
  have hg_maps_closed : MapsTo g (ball (0 : ℂ) 1) (closedBall (0 : ℂ) 1) := by
    intro ξ hξ
    exact ball_subset_closedBall (hg_maps_ball hξ)
  let ξ : ℂ := (z - w) / (1 - (starRingEnd ℂ) w * z)
  have hξ_mem : ξ ∈ ball (0 : ℂ) 1 := by
    simpa [ξ] using mapsTo_ball_unitDiscMoebiusFormula_of_norm_lt_one
      (a := w) hw_norm hz
  have hz_norm : ‖z‖ < 1 := by
    simpa [mem_ball_zero_iff] using hz
  -- The conjugate sends the Moebius image of `z` to the Moebius image of `f z` (shared scaffold).
  have hg_ξ : g ξ = target (f z) :=
    apply_unitDiscMoebiusFormula_schwarzPickConjugate hw_norm hz_norm
  have hξ_norm : ‖ξ‖ < 1 := by
    simpa [mem_ball_zero_iff] using hξ_mem
  calc
    pseudoHyperbolicExpr (f z) (f w) = ‖g ξ‖ := by
      rw [hg_ξ, pseudoHyperbolicExpr_def]
    _ ≤ ‖ξ‖ := by
      exact Complex.norm_le_norm_of_mapsTo_ball hg_diff hg_maps_closed hg_zero hξ_norm
    _ = pseudoHyperbolicExpr z w := by
      rw [pseudoHyperbolicExpr_def]

/-- Bundled unit-disc form of the Schwarz--Pick contraction estimate. -/
theorem pseudoHyperbolicExpr_map_le_unitDisc {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (hmaps : MapsTo f (ball (0 : ℂ) 1) (ball (0 : ℂ) 1))
    (z w : Complex.UnitDisc) :
    pseudoHyperbolicExpr (f z) (f w) ≤ pseudoHyperbolicExpr (z : ℂ) (w : ℂ) :=
  pseudoHyperbolicExpr_map_le hf hmaps z.property w.property

end TauCeti
