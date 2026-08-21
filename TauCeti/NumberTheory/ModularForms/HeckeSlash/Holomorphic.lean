/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Basic

/-!
# The slash sum preserves holomorphy

`heckeSlashSum` is a finite sum of slashes, so it is holomorphic whenever its argument is. This
is one of the two conditions separating `SlashInvariantForm` from `ModularForm`; the other,
boundedness at the cusps, is not addressed here.

Holomorphy is one of the two conditions a `ModularForm` carries over a `SlashInvariantForm`. A
consumer building the descent needs this together with boundedness at the cusps; only the former
is available here, and nothing in this file assumes `f` is slash-invariant, so it applies to any
holomorphic `f : ℍ → ℂ`.

## Main results

* `HeckeRing.GL2.mdifferentiable_heckeSlashSum`: `heckeSlashSum k D f` is holomorphic when `f` is.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.4.
-/

public section

open Matrix UpperHalfPlane DoubleCoset HeckeRing.GLn

open scoped MatrixGroups ModularForm Manifold

namespace HeckeRing.GL2

variable (k : ℤ) {Δ : Submonoid (GL (Fin 2) ℚ)} {Γ₁ Γ₂ : Subgroup (GL (Fin 2) ℚ)}
  (D : HeckeCoset Δ Γ₁ Γ₂) [Finite (DecompQuotient Γ₂ Γ₁ (D.out : GL (Fin 2) ℚ)⁻¹)]

/-- **The slash sum of a holomorphic function is holomorphic.** Together with slash-invariance
(`heckeSlashSum_slash_invariant`) this supplies one of the two extra conditions a
`ModularForm` carries over a `SlashInvariantForm`; boundedness at the cusps is separate and is
not proved here. -/
lemma mdifferentiable_heckeSlashSum {f : ℍ → ℂ} (hf : MDiff f) : MDiff (heckeSlashSum k D f) := by
  -- `heckeSlashSum` is not `@[expose]`, so `heckeSlashSum_def` is what makes the sum visible;
  -- `MDifferentiable.sum` then reduces to one summand. That summand slashes by a *rational*
  -- matrix, and `rat_slash` restates it at the real image, which is the form mathlib's
  -- `MDifferentiable.slash` applies to.
  rw [heckeSlashSum_def]
  refine MDifferentiable.sum fun i _ ↦ ?_
  rw [ModularForm.rat_slash]
  exact hf.slash k _

end HeckeRing.GL2
