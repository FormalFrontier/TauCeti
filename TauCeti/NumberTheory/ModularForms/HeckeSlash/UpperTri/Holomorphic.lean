/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.HeckeSlash.UpperTri.Sum

/-!
# The upper-triangular Hecke slash sum preserves holomorphy

`heckeSlashUpperTri` is a finite sum of slashes by the upper-triangular representatives
`upperTriRep p b` for `b : Fin p`. Because each representative is a rational matrix of positive
determinant, each summand is holomorphic whenever the underlying function is, and hence so is the
entire sum.

This is one of the analytic requirements for descending the upper-triangular Hecke sum to modular
forms; the cusp conditions live in `UpperTri/Infty.lean` and `UpperTri/Cusps.lean`, and periodicity
under `τ ↦ τ + 1` lives in `UpperTri/Periodic.lean`.

## Main results

* `HeckeRing.GL2.mdifferentiable_slash_upperTriRep`: slashing by an upper-triangular representative
  preserves holomorphy.
* `HeckeRing.GL2.mdifferentiable_heckeSlashUpperTri`: `heckeSlashUpperTri k p f` is holomorphic
  when `f` is.

## Provenance

The shape corresponds to the holomorphy step of `heckeT_p_ut` in the AINTLIB `LeanModularForms`
project (Chris Birkbeck, Apache-2.0), `LeanModularForms/HeckeRIngs/GL2/AdjointTheory.lean` at
commit `2baa76f742bdb4fb8ee323fabba41203bd390e08`. Stated here for `upperTriRep`, this
repository's general-`n` family at `n = 2`.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.4.
-/

public section

open Matrix UpperHalfPlane HeckeRing.GLn

open scoped MatrixGroups ModularForm Manifold

namespace HeckeRing.GL2

variable (k : ℤ) (p : ℕ)

/-- **Slashing by an upper-triangular representative preserves holomorphy.** -/
lemma mdifferentiable_slash_upperTriRep {f : ℍ → ℂ} (hf : MDiff f) (b : Fin p) :
    MDiff (f ∣[k] (upperTriRep p b : GL (Fin 2) ℚ)) := by
  rw [ModularForm.rat_slash]
  exact hf.slash k _

/-- **The upper-triangular slash sum of a holomorphic function is holomorphic.** -/
lemma mdifferentiable_heckeSlashUpperTri {f : ℍ → ℂ} (hf : MDiff f) :
    MDiff (heckeSlashUpperTri k p f) := by
  rw [heckeSlashUpperTri_def]
  exact MDifferentiable.sum fun b _ ↦ mdifferentiable_slash_upperTriRep k p hf b

end HeckeRing.GL2

end
