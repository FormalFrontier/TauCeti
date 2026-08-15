/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.NumberTheory.ModularForms.BoundedAtCusp
public import TauCeti.NumberTheory.ModularForms.Cusps.Rat
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Basic

/-!
# The Hecke slash sum vanishes, and is bounded, at the cusps

`heckeSlashSum` is a finite sum of slashes, so its behaviour at a cusp follows from that of its
summands. A slash is zero at `c` exactly when the original function is zero at `g • c`
(`OnePoint.IsZeroAt.smul_iff`), and `g • c` is again a cusp because the representatives are
rational (`IsCusp.smul_map_ratCast`). So a function vanishing at every cusp has a slash sum
vanishing at every cusp, whatever representatives were chosen.

This is the step the Layer 2 statement "`Tₙ` preserves `S_k`" rests on.

Both are stated for an arbitrary arithmetic `Γ`, which is the hypothesis a `CuspForm Γ k`
supplies through `zero_at_cusps'`. `IsCusp.smul_map_ratCast` reduces to `𝒮ℒ` internally via
`Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z`, so no comparison is left for the caller.

## Main results

* `HeckeRing.GL2.isZeroAt_heckeSlashSum`: the slash sum of a function vanishing at every cusp
  vanishes at every cusp.
* `HeckeRing.GL2.isBoundedAt_heckeSlashSum`: the same for boundedness.

## Provenance

The shape is AINTLIB's `heckeT_p_ut_zero_at_cusps`
([`LeanModularForms/HeckeRIngs/GL2/AdjointTheory.lean`](https://github.com/CBirkbeck/AINTLIB)
lines 62-71, commit `2baa76f742bdb4fb8ee323fabba41203bd390e08`, Apache-2.0, Chris Birkbeck),
which runs the same argument by hand with `Finset.sum_induction` over its own representatives.
Here the induction is `OnePoint.IsZeroAt.sum`, and the statement is about this repository's
`heckeSlashSum`.
-/

public section

namespace HeckeRing.GL2

open UpperHalfPlane DoubleCoset HeckeRing.GLn

open scoped MatrixGroups ModularForm

variable (k : ℤ) (D : HeckeCoset (posDetInt 2) (SLnZ 2) (SLnZ 2))

/-- **The slash sum vanishes at every cusp** when the function does. -/
lemma isZeroAt_heckeSlashSum {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic] {f : ℍ → ℂ}
    (hf : ∀ c : OnePoint ℝ, IsCusp c Γ → c.IsZeroAt f k) {c : OnePoint ℝ} (hc : IsCusp c Γ) :
    c.IsZeroAt (heckeSlashSum k D f) k := by
  rw [heckeSlashSum_def]
  refine OnePoint.IsZeroAt.sum fun i _ ↦ ?_
  rw [ModularForm.rat_slash]
  exact OnePoint.IsZeroAt.smul_iff.mp (hf _ (hc.smul_map_ratCast _))

/-- **The slash sum is bounded at every cusp** when the function is. -/
lemma isBoundedAt_heckeSlashSum {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic] {f : ℍ → ℂ}
    (hf : ∀ c : OnePoint ℝ, IsCusp c Γ → c.IsBoundedAt f k) {c : OnePoint ℝ}
    (hc : IsCusp c Γ) : c.IsBoundedAt (heckeSlashSum k D f) k := by
  rw [heckeSlashSum_def]
  refine OnePoint.IsBoundedAt.sum fun i _ ↦ ?_
  rw [ModularForm.rat_slash]
  exact OnePoint.IsBoundedAt.smul_iff.mp (hf _ (hc.smul_map_ratCast _))

end HeckeRing.GL2

end
