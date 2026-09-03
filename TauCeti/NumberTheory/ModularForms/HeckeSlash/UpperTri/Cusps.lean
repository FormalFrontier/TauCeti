/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.Cusps.Rat.Slash
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.UpperTri.Sum

/-!
# The upper-triangular Hecke slash sum vanishes, and is bounded, at the cusps

`heckeSlashUpperTri` is a finite sum of slashes by rational matrices `upperTriRep p b` of positive
determinant. A slash is zero at a cusp `c` exactly when the original function is zero at `g • c`
(`OnePoint.IsZeroAt.smul_iff`), and for an arithmetic subgroup `Γ` the rational transform `g • c`
is again a cusp of `Γ` (`IsCusp.smul_map_ratCast`). Consequently, a function vanishing at every
cusp of `Γ` has an upper-triangular slash sum vanishing at every cusp of `Γ`. The same transport
holds for boundedness at every cusp.

This supplies the cusp-vanishing and cusp-boundedness properties of the upper-triangular part of
the Hecke operator at general level.

## Main results

* `HeckeRing.GL2.isZeroAt_heckeSlashUpperTri`: `heckeSlashUpperTri k p f` vanishes at every cusp
  when `f` does.
* `HeckeRing.GL2.isBoundedAt_heckeSlashUpperTri`: `heckeSlashUpperTri k p f` is bounded at every
  cusp when `f` is.

## Provenance

The shape corresponds to `heckeT_p_ut_zero_at_cusps` in the AINTLIB `LeanModularForms` project
(Chris Birkbeck, Apache-2.0), `LeanModularForms/HeckeRIngs/GL2/AdjointTheory.lean` at commit
`2baa76f742bdb4fb8ee323fabba41203bd390e08`. Restated for this repository's `upperTriRep` and
general arithmetic subgroups `Γ` via `OnePoint.IsZeroAt.sum` and `IsCusp.smul_map_ratCast`.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.4.
-/

public section

namespace HeckeRing.GL2

open UpperHalfPlane HeckeRing.GLn

open scoped MatrixGroups ModularForm

variable (k : ℤ) (p : ℕ)

/-- **The upper-triangular slash sum vanishes at every cusp** when the function does. -/
lemma isZeroAt_heckeSlashUpperTri {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic] {f : ℍ → ℂ}
    (hf : ∀ c : OnePoint ℝ, IsCusp c Γ → c.IsZeroAt f k) {c : OnePoint ℝ} (hc : IsCusp c Γ) :
    c.IsZeroAt (heckeSlashUpperTri k p f) k := by
  rw [heckeSlashUpperTri_def]
  exact OnePoint.isZeroAt_sum_rat_slash k _ _ hf hc

/-- **The upper-triangular slash sum is bounded at every cusp** when the function is. -/
lemma isBoundedAt_heckeSlashUpperTri {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic] {f : ℍ → ℂ}
    (hf : ∀ c : OnePoint ℝ, IsCusp c Γ → c.IsBoundedAt f k) {c : OnePoint ℝ} (hc : IsCusp c Γ) :
    c.IsBoundedAt (heckeSlashUpperTri k p f) k := by
  rw [heckeSlashUpperTri_def]
  exact OnePoint.isBoundedAt_sum_rat_slash k _ _ hf hc

end HeckeRing.GL2

end
