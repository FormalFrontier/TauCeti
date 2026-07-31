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

It also sets up the Schwarz--Pick conjugate `schwarzPickConjugate f a`, the self-map of the disc
obtained by conjugating `f` by the Moebius factors centred at `a` and at `f a`, together with
the scaffold lemma saying it is a holomorphic self-map fixing the origin and the lemma computing
its value at a Moebius image.  This is the construction Schwarz's lemma is applied to, shared by
the contraction estimate here, the infinitesimal estimate in `SchwarzPick/Derivative.lean`, the
equality case in `SchwarzPick/Rigidity.lean` and the automorphism classification.

This advances the conformal-mapping roadmap's L2 Schwarz--Pick target.  It reuses Mathlib's
Schwarz lemma and Tau Ceti's unit-disc Moebius API.  As with the rest of the L0--L3
conformal-mapping material, it is coordinated with the upstream Mathlib RMT effort
leanprover-community/mathlib4#33505.  Mathlib already contains the preceding human-curated
work in `Analysis/Complex/RiemannMapping.lean` and `Analysis/Complex/BranchLogRoot.lean`; none
of it is duplicated here, and should that work land a human-curated Schwarz--Pick theorem this
file should be refactored onto it.
-/

public section

namespace TauCeti

open Complex Metric Set
open scoped ComplexConjugate

/-- **The Schwarz--Pick conjugate** of a self-map `f` of the open unit disc at a point `a`:
`f` conjugated by the scalar Moebius formulas centred at `-a` on the source and at `f a` on the
target.  When `f` is a holomorphic self-map of the disc and `‖a‖ < 1` the conjugate is again a
holomorphic self-map of the disc, but now fixing the origin
(`differentiableOn_and_mapsTo_ball_and_apply_zero_schwarzPickConjugate`), so Schwarz's lemma
applies to it at `0`.  This is the construction shared by the finite and infinitesimal
Schwarz--Pick estimates and by the equality case of the finite estimate. -/
noncomputable def schwarzPickConjugate (f : ℂ → ℂ) (a : ℂ) : ℂ → ℂ :=
  (fun η => (η - f a) / (1 - (starRingEnd ℂ) (f a) * η)) ∘ f ∘
    fun ξ => (ξ - (-a)) / (1 - (starRingEnd ℂ) (-a) * ξ)

/-- The Schwarz--Pick conjugate as a composite: the scalar Moebius formula centred at `-a` on the
source, then `f`, then the scalar Moebius formula centred at `f a` on the target.  The body of
`schwarzPickConjugate` is not `@[expose]`d, so downstream files rewrite with this lemma rather
than unfolding the definition. -/
lemma schwarzPickConjugate_def (f : ℂ → ℂ) (a : ℂ) :
    schwarzPickConjugate f a =
      (fun η => (η - f a) / (1 - (starRingEnd ℂ) (f a) * η)) ∘ f ∘
        fun ξ => (ξ - (-a)) / (1 - (starRingEnd ℂ) (-a) * ξ) := by
  rw [schwarzPickConjugate]

/-- The Schwarz--Pick conjugate of `f` at `a` fixes the origin: the source factor sends `0` to
`a`, and the target factor sends `f a` to `0`.  No hypothesis on `f` or `a` is needed. -/
@[simp]
lemma schwarzPickConjugate_apply_zero (f : ℂ → ℂ) (a : ℂ) :
    schwarzPickConjugate f a 0 = 0 := by
  simp [schwarzPickConjugate]

/-- **Schwarz--Pick conjugation scaffold.** For a holomorphic self-map `f` of the open unit
disc and a disc point `a`, conjugating `f` by the Moebius automorphisms centred at `a` (on the
source) and at `f a` (on the target) yields a holomorphic self-map of the disc that fixes the
origin.  This is the common scaffold of the finite and infinitesimal Schwarz--Pick estimates:
applying Schwarz's lemma at `0` to the conjugate unwinds to the contraction estimate for
`f`. -/
lemma differentiableOn_and_mapsTo_ball_and_apply_zero_schwarzPickConjugate {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (hmaps : MapsTo f (ball (0 : ℂ) 1) (ball (0 : ℂ) 1)) {a : ℂ} (ha : ‖a‖ < 1) :
    DifferentiableOn ℂ (schwarzPickConjugate f a) (ball (0 : ℂ) 1) ∧
      MapsTo (schwarzPickConjugate f a) (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) ∧
      schwarzPickConjugate f a 0 = 0 := by
  have ha_mem : a ∈ ball (0 : ℂ) 1 := by simpa [mem_ball_zero_iff] using ha
  have hfa_norm : ‖f a‖ < 1 := by simpa [mem_ball_zero_iff] using hmaps ha_mem
  have hsource_maps :
      MapsTo (fun ξ : ℂ => (ξ - (-a)) / (1 - (starRingEnd ℂ) (-a) * ξ))
        (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) :=
    mapsTo_ball_unitDiscMoebiusFormula_of_norm_lt_one (a := -a) (by simpa using ha)
  have htarget_maps :
      MapsTo (fun η : ℂ => (η - f a) / (1 - (starRingEnd ℂ) (f a) * η))
        (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) :=
    mapsTo_ball_unitDiscMoebiusFormula_of_norm_lt_one (a := f a) hfa_norm
  have hsource_diff :
      DifferentiableOn ℂ (fun ξ : ℂ => (ξ - (-a)) / (1 - (starRingEnd ℂ) (-a) * ξ))
        (ball (0 : ℂ) 1) :=
    differentiableOn_unitDiscMoebiusFormula_of_norm_lt_one (a := -a) (by simpa using ha)
  have htarget_diff :
      DifferentiableOn ℂ (fun η : ℂ => (η - f a) / (1 - (starRingEnd ℂ) (f a) * η))
        (ball (0 : ℂ) 1) :=
    differentiableOn_unitDiscMoebiusFormula_of_norm_lt_one (a := f a) hfa_norm
  refine ⟨htarget_diff.comp (hf.comp hsource_diff hsource_maps) (hmaps.comp hsource_maps),
    fun ξ hξ => htarget_maps (hmaps (hsource_maps hξ)), schwarzPickConjugate_apply_zero f a⟩

/-- **Value of the Schwarz--Pick conjugate at a Moebius image.** The Schwarz--Pick conjugate
`schwarzPickConjugate f a` sends the Moebius image of a disc point `z` to the Moebius image of
`f z`.  Taking norms turns a Schwarz-lemma estimate for the conjugate at `0` into a
pseudo-hyperbolic statement about `f` at `z`, `a`, so this is the evaluation step shared by the
Schwarz--Pick contraction estimate and its equality case. -/
lemma schwarzPickConjugate_apply_unitDiscMoebiusFormula {f : ℂ → ℂ} {a z : ℂ}
    (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) :
    schwarzPickConjugate f a ((z - a) / (1 - (starRingEnd ℂ) a * z))
      = (f z - f a) / (1 - (starRingEnd ℂ) (f a) * f z) := by
  have hsource : ((z - a) / (1 - (starRingEnd ℂ) a * z) - -a) /
      (1 - (starRingEnd ℂ) (-a) * ((z - a) / (1 - (starRingEnd ℂ) a * z))) = z :=
    leftInvOn_unitDiscMoebiusFormula_of_norm_lt_one ha (by simpa [mem_ball_zero_iff] using hz)
  simp only [schwarzPickConjugate, Function.comp_apply, hsource]

/--
The Schwarz--Pick contraction estimate for the pseudo-hyperbolic expression on the open unit
disc.
-/
theorem pseudoHyperbolicExpr_map_le {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (hmaps : MapsTo f (ball (0 : ℂ) 1) (ball (0 : ℂ) 1))
    {z w : ℂ} (hz : z ∈ ball (0 : ℂ) 1) (hw : w ∈ ball (0 : ℂ) 1) :
    pseudoHyperbolicExpr (f z) (f w) ≤ pseudoHyperbolicExpr z w := by
  -- Conjugate `f` by the disc automorphisms sending `w ↦ 0` and `f w ↦ 0`, so the conjugate
  -- `schwarzPickConjugate f w` fixes `0`.  Mathlib's Schwarz lemma at `0` then bounds its norm
  -- by the identity, which unwinds to the pseudo-hyperbolic contraction at `z`, `w`.
  have hw_norm : ‖w‖ < 1 := by
    simpa [mem_ball_zero_iff] using hw
  -- The conjugate is a holomorphic self-map of the disc fixing the origin (shared scaffold).
  obtain ⟨hg_diff, hg_maps_ball, hg_zero⟩ :=
    differentiableOn_and_mapsTo_ball_and_apply_zero_schwarzPickConjugate hf hmaps hw_norm
  have hg_maps_closed :
      MapsTo (schwarzPickConjugate f w) (ball (0 : ℂ) 1) (closedBall (0 : ℂ) 1) := by
    intro ξ hξ
    exact ball_subset_closedBall (hg_maps_ball hξ)
  let ξ : ℂ := (z - w) / (1 - (starRingEnd ℂ) w * z)
  have hξ_mem : ξ ∈ ball (0 : ℂ) 1 := by
    simpa [ξ] using mapsTo_ball_unitDiscMoebiusFormula_of_norm_lt_one
      (a := w) hw_norm hz
  have hz_norm : ‖z‖ < 1 := by
    simpa [mem_ball_zero_iff] using hz
  -- The conjugate sends the Moebius image of `z` to the Moebius image of `f z` (shared scaffold).
  have hg_ξ : schwarzPickConjugate f w ξ
      = (f z - f w) / (1 - (starRingEnd ℂ) (f w) * f z) :=
    schwarzPickConjugate_apply_unitDiscMoebiusFormula hw_norm hz_norm
  have hξ_norm : ‖ξ‖ < 1 := by
    simpa [mem_ball_zero_iff] using hξ_mem
  calc
    pseudoHyperbolicExpr (f z) (f w) = ‖schwarzPickConjugate f w ξ‖ := by
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
