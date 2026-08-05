/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Complex.Conformal.SchwarzPick.Basic
public import TauCeti.Analysis.Complex.Conformal.UnitDisc.Automorphism.Basic

/-!
# Disc automorphisms are pseudo-hyperbolic isometries

The Schwarz--Pick contraction estimate `pseudoHyperbolicExpr_map_le` says a holomorphic
self-map of the unit disc does not increase the pseudo-hyperbolic expression
`pseudoHyperbolicExpr z w = ‖(z - w) / (1 - conj w * z)‖`.  A holomorphic self-map that
additionally has a holomorphic self-map inverse must then *preserve* the expression: applying
the estimate to the map and to its inverse forces equality.  This file records that equality
and specializes it to the concrete disc automorphisms.

The results are:

* `pseudoHyperbolicExpr_map_eq` — the Schwarz--Pick equality for any holomorphic self-map of
  the disc with a holomorphic self-map left inverse;
* `pseudoHyperbolicExpr_unitDiscMoebiusFormula_of_norm_lt_one` /
  `pseudoHyperbolicExpr_unitDiscMoebius` — the Moebius factor `z ↦ (z - a) / (1 - conj a * z)`
  is a pseudo-hyperbolic isometry, in scalar and bundled `Complex.UnitDisc` form;
* `pseudoHyperbolicExpr_unitDiscStandardAutomorphismEquiv` — every standard disc automorphism
  `z ↦ u * (z - a) / (1 - conj a * z)` is a pseudo-hyperbolic isometry.

Together these say that the pseudo-hyperbolic expression is preserved by holomorphic
self-maps of the disc with a holomorphic self-map left inverse, and by the standard
automorphisms bundled as `unitDiscStandardAutomorphismEquiv`.

This advances the conformal-mapping roadmap's L2 Schwarz--Pick / disc-automorphism target,
building directly on Tau Ceti's `pseudoHyperbolicExpr_map_le` (Mathlib's Schwarz lemma) and
the unit-disc Moebius / automorphism API.  As with the rest of the L0--L3 conformal-mapping
material, it is coordinated with the upstream Mathlib RMT effort
leanprover-community/mathlib4#33505 and should be refactored to upstream API if that work
lands a human-curated Schwarz--Pick theorem.
-/

public section

namespace TauCeti

open _root_.Complex Metric Set
open scoped ComplexConjugate

/-- **Schwarz--Pick equality.** A holomorphic self-map of the unit disc that admits a
holomorphic self-map left inverse preserves the pseudo-hyperbolic expression: the Schwarz--Pick
contraction, applied to the map and to its inverse, forces equality. -/
theorem pseudoHyperbolicExpr_map_eq {f g : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1)) (hfmaps : MapsTo f (ball 0 1) (ball 0 1))
    (hg : DifferentiableOn ℂ g (ball (0 : ℂ) 1)) (hgmaps : MapsTo g (ball 0 1) (ball 0 1))
    (hgf : LeftInvOn g f (ball 0 1))
    {z w : ℂ} (hz : z ∈ ball (0 : ℂ) 1) (hw : w ∈ ball (0 : ℂ) 1) :
    pseudoHyperbolicExpr (f z) (f w) = pseudoHyperbolicExpr z w := by
  refine le_antisymm (pseudoHyperbolicExpr_map_le hf hfmaps hz hw) ?_
  have h := pseudoHyperbolicExpr_map_le hg hgmaps (hfmaps hz) (hfmaps hw)
  rwa [hgf hz, hgf hw] at h

/-- **Moebius invariance (scalar form).** The Moebius factor `z ↦ (z - a) / (1 - conj a * z)`
with `‖a‖ < 1` is a pseudo-hyperbolic isometry of the open unit disc. -/
@[simp]
theorem pseudoHyperbolicExpr_unitDiscMoebiusFormula_of_norm_lt_one {a : ℂ} (ha : ‖a‖ < 1)
    {z w : ℂ} (hz : z ∈ ball (0 : ℂ) 1) (hw : w ∈ ball (0 : ℂ) 1) :
    pseudoHyperbolicExpr ((z - a) / (1 - (starRingEnd ℂ) a * z))
        ((w - a) / (1 - (starRingEnd ℂ) a * w))
      = pseudoHyperbolicExpr z w := by
  have ha' : ‖-a‖ < 1 := by rwa [norm_neg]
  refine pseudoHyperbolicExpr_map_eq
    (f := fun z => (z - a) / (1 - (starRingEnd ℂ) a * z))
    (g := fun z => (z - (-a)) / (1 - (starRingEnd ℂ) (-a) * z))
    (differentiableOn_unitDiscMoebiusFormula_of_norm_lt_one ha)
    (mapsTo_ball_unitDiscMoebiusFormula_of_norm_lt_one ha)
    (differentiableOn_unitDiscMoebiusFormula_of_norm_lt_one ha')
    (mapsTo_ball_unitDiscMoebiusFormula_of_norm_lt_one ha') ?_ hz hw
  exact leftInvOn_unitDiscMoebiusFormula_of_norm_lt_one ha

/-- **Moebius invariance (bundled form).** The bundled unit-disc Moebius factor
`unitDiscMoebius a` preserves the pseudo-hyperbolic expression. -/
@[simp]
theorem pseudoHyperbolicExpr_unitDiscMoebius (a z w : Complex.UnitDisc) :
    pseudoHyperbolicExpr (((z : ℂ) - (a : ℂ)) / (1 - (starRingEnd ℂ) (a : ℂ) * (z : ℂ)))
        (((w : ℂ) - (a : ℂ)) / (1 - (starRingEnd ℂ) (a : ℂ) * (w : ℂ)))
      = pseudoHyperbolicExpr (z : ℂ) (w : ℂ) := by
  exact pseudoHyperbolicExpr_unitDiscMoebiusFormula_of_norm_lt_one a.norm_lt_one
    z.property w.property

/-- **Standard automorphism invariance.** Every standard disc automorphism bundled as
`unitDiscStandardAutomorphismEquiv u a` preserves the pseudo-hyperbolic expression. -/
theorem pseudoHyperbolicExpr_unitDiscStandardAutomorphismEquiv
    (u : Circle) (a z w : Complex.UnitDisc) :
    pseudoHyperbolicExpr (unitDiscStandardAutomorphismEquiv u a z : ℂ)
        (unitDiscStandardAutomorphismEquiv u a w : ℂ)
      = pseudoHyperbolicExpr (z : ℂ) (w : ℂ) := by
  rw [coe_unitDiscStandardAutomorphismEquiv_apply,
    coe_unitDiscStandardAutomorphismEquiv_apply,
    pseudoHyperbolicExpr_const_mul (Circle.norm_coe u)]
  exact pseudoHyperbolicExpr_unitDiscMoebiusFormula_of_norm_lt_one a.norm_lt_one
    z.property w.property

end TauCeti
