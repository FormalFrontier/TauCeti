/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.NumberTheory.HeckeRing.GL2.CosetDecomposition
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.UpperTri.Sum
public import TauCeti.NumberTheory.ModularForms.SlashActionRat
public import TauCeti.Order.Filter.ZeroAndBoundedAtFilter

/-!
# Slashing by an upper-triangular representative preserves behaviour at `i∞`

Mathlib's `UpperHalfPlane.IsBoundedAtImInfty.slash` and `IsZeroAtImInfty.slash` carry the
hypothesis `g 1 0 = 0`, so they apply when `g` is upper triangular. (The hypothesis is sufficient,
not necessary — the zero function stays bounded and vanishing after slashing by any matrix.)
`SlashActionRat.lean` states their rational forms; this file discharges the hypothesis for this
repository's coset representatives `upperTriRep` and assembles the operator-level statement for
`heckeSlashUpperTri`.

That operator is the merged `∑ b < p, f ∣[k] !![1, b; 0, p]` of `UpperTri/Sum.lean`, which had no
statement about its behaviour at `i∞`. The cusp-level results for the *general* double-coset sum
live in `HeckeSlash/Cusps.lean` and are about a different operator; neither implies the other.

## Main results

* `HeckeRing.GL2.isBoundedAtImInfty_slash_upperTriRep`,
  `HeckeRing.GL2.isZeroAtImInfty_slash_upperTriRep`: slashing by a representative preserves
  boundedness, resp. vanishing, at `i∞`.
* `HeckeRing.GL2.isBoundedAtImInfty_heckeSlashUpperTri`,
  `HeckeRing.GL2.isZeroAtImInfty_heckeSlashUpperTri`: the same for the whole sum
  `heckeSlashUpperTri`.

## Provenance

No code is transcribed. The step corresponds to the analytic core of the AINTLIB
`LeanModularForms` project (Chris Birkbeck, Apache-2.0),
`LeanModularForms/HeckeRIngs/GL2/AdjointTheory.lean` at commit
`2baa76f742bdb4fb8ee323fabba41203bd390e08`, whose `heckeT_p_ut_zero_at_cusps` (lines 62-70) needs
exactly this fact about each summand. Here it is stated for a single representative and for
`upperTriRep`, this repository's general-`n` family at `n = 2`, rather than for a transcribed
matrix.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.4.
-/

public section

open UpperHalfPlane Matrix

open scoped MatrixGroups ModularForm

namespace HeckeRing.GL2

variable (k : ℤ) (p : ℕ)

/-- **Slashing by a representative preserves boundedness at `i∞`.** -/
lemma isBoundedAtImInfty_slash_upperTriRep {f : ℍ → ℂ} (hf : IsBoundedAtImInfty f) (b : Fin p) :
    IsBoundedAtImInfty (f ∣[k] (upperTriRep p b : GL (Fin 2) ℚ)) :=
  UpperHalfPlane.IsBoundedAtImInfty.rat_slash k (upperTriRep_apply_one_zero p b) hf

/-- **Slashing by a representative preserves vanishing at `i∞`.** -/
lemma isZeroAtImInfty_slash_upperTriRep {f : ℍ → ℂ} (hf : IsZeroAtImInfty f) (b : Fin p) :
    IsZeroAtImInfty (f ∣[k] (upperTriRep p b : GL (Fin 2) ℚ)) :=
  UpperHalfPlane.IsZeroAtImInfty.rat_slash k (upperTriRep_apply_one_zero p b) hf

/-- **The upper-triangular sum is bounded at `i∞`** when the function is. Each summand is
handled by `isBoundedAtImInfty_slash_upperTriRep`, and the sum by `Filter.BoundedAtFilter.sum`. -/
lemma isBoundedAtImInfty_heckeSlashUpperTri {f : ℍ → ℂ} (hf : IsBoundedAtImInfty f) :
    IsBoundedAtImInfty (heckeSlashUpperTri k p f) := by
  rw [heckeSlashUpperTri_def]
  exact Filter.BoundedAtFilter.sum fun b _ ↦ isBoundedAtImInfty_slash_upperTriRep k p hf b

/-- **The upper-triangular sum vanishes at `i∞`** when the function does. -/
lemma isZeroAtImInfty_heckeSlashUpperTri {f : ℍ → ℂ} (hf : IsZeroAtImInfty f) :
    IsZeroAtImInfty (heckeSlashUpperTri k p f) := by
  rw [heckeSlashUpperTri_def]
  exact Filter.ZeroAtFilter.sum fun b _ ↦ isZeroAtImInfty_slash_upperTriRep k p hf b

end HeckeRing.GL2

end
