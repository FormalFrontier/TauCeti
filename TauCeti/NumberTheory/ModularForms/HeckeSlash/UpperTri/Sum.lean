/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.NumberTheory.HeckeRing.GL2.CosetDecomposition
public import TauCeti.NumberTheory.ModularForms.SlashActionRat

/-!
# The upper-triangular part of the Hecke operator

The classical `T_p` contains a sum of slashes by the representatives `!![1, b; 0, p]` for
`b < p`, together with one further, diamond-twisted term when `p ∤ N`. This file defines the
triangular sum `heckeSlashUpperTri` and records its `ℂ`-linearity in `f`: zero, addition and
scalar multiplication are preserved. (Linearity in `f` only; it is not yet bundled as a
`LinearMap`.)

Why these representatives: mathlib's `IsBoundedAtImInfty.slash` requires `g 1 0 = 0`, so it
applies when `g` is upper triangular. (Sufficient, not necessary — the zero function stays
bounded after slashing by any matrix.) Having that hypothesis to hand is why the classical
arguments are organised around `!![1, b; 0, p]`. It is discharged by `upperTriRep_apply_one_zero`
in
`HeckeRing/GL2/CosetDecomposition.lean`, the `(1, 0)` case of `upperTriGL_apply_eq_zero_of_lt` —
the entrywise description of the representatives is not restated.

## Main definitions

* `HeckeRing.GL2.heckeSlashUpperTri`: the sum `∑ b < p, f ∣[k] !![1, b; 0, p]`.
## Main results

* `HeckeRing.GL2.heckeSlashUpperTri_def` and `heckeSlashUpperTri_apply`: the characteristic
  equation and its pointwise form, the convenient rewrites for turning the operator back into
  its sum.
* `HeckeRing.GL2.heckeSlashUpperTri_zero`, `heckeSlashUpperTri_add`,
  `heckeSlashUpperTri_smul`: linearity in `f`.
The representatives themselves, and their upper-triangularity and positive determinant, live in
`HeckeRing/GL2/CosetDecomposition.lean`; this file is only the slash sum built from them.

## Provenance

The shape is AINTLIB's `heckeT_p_ut`
([`LeanModularForms/HeckeRIngs/GL2/HeckeT_p.lean`](https://github.com/CBirkbeck/AINTLIB), commit
`2baa76f742bdb4fb8ee323fabba41203bd390e08`, Apache-2.0, Chris Birkbeck):
`∑ b ∈ Finset.range p, f ∣[k] T_p_upper p hp b`. Restated over this repository's own
representatives — `T_p_upper p _ b` is `upperTriGL` at `n = 2`, `a = ![1, p]` — so AINTLIB's
`T_p_upper` is not reproduced.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.4.
* [DS] Diamond–Shurman, *A first course in modular forms*, Proposition 5.2.1.
-/

public section

open Matrix UpperHalfPlane HeckeRing.GLn

open scoped MatrixGroups ModularForm

namespace HeckeRing.GL2

variable (k : ℤ) (p : ℕ)

/-- **The upper-triangular part of the Hecke operator**: `∑ b < p, f ∣[k] !![1, b; 0, p]`. -/
noncomputable def heckeSlashUpperTri (f : ℍ → ℂ) : ℍ → ℂ :=
  ∑ b : Fin p, f ∣[k] upperTriRep p b

/-- The defining equation of `heckeSlashUpperTri`: the convenient rewrite for turning the
operator back into its sum. -/
lemma heckeSlashUpperTri_def (f : ℍ → ℂ) :
    heckeSlashUpperTri k p f = ∑ b : Fin p, f ∣[k] upperTriRep p b := (rfl)

/-- The pointwise form of the defining equation: consumers working at a point of `ℍ` — cusp
and `q`-expansion arguments in particular — need the value, not the function. -/
lemma heckeSlashUpperTri_apply (f : ℍ → ℂ) (τ : ℍ) :
    heckeSlashUpperTri k p f τ = ∑ b : Fin p, (f ∣[k] upperTriRep p b) τ := by
  rw [heckeSlashUpperTri_def, Finset.sum_apply]

/-- The sum sends the zero function to zero. -/
@[simp] lemma heckeSlashUpperTri_zero : heckeSlashUpperTri k p 0 = 0 := by
  rw [heckeSlashUpperTri]
  exact Finset.sum_eq_zero fun b _ ↦ SlashAction.zero_slash k (upperTriRep p b)

/-- The sum is additive in `f`, since each slash is. -/
@[simp] lemma heckeSlashUpperTri_add (f g : ℍ → ℂ) :
    heckeSlashUpperTri k p (f + g) = heckeSlashUpperTri k p f + heckeSlashUpperTri k p g := by
  simp [heckeSlashUpperTri, Finset.sum_add_distrib]

/-- **Scalars pass through the sum.** With `heckeSlashUpperTri_add` and
`heckeSlashUpperTri_zero` this is the `ℂ`-linearity of `f ↦ heckeSlashUpperTri k p f`. The
scalar generality matches `ModularForm.rat_smul_slash_of_det_pos`. -/
@[simp] lemma heckeSlashUpperTri_smul {α : Type*} [DistribSMul α ℂ] [IsScalarTower α ℂ ℂ] (c : α)
    (f : ℍ → ℂ) : heckeSlashUpperTri k p (c • f) = c • heckeSlashUpperTri k p f := by
  rw [heckeSlashUpperTri_def, heckeSlashUpperTri_def, Finset.smul_sum]
  exact Finset.sum_congr rfl fun b _ ↦
    ModularForm.rat_smul_slash_of_det_pos k (det_upperTriRep_pos p b) f c

end HeckeRing.GL2
