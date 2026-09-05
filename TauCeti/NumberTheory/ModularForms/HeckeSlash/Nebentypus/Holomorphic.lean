/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Holomorphic
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Nebentypus.Basic

/-!
# The twisted slash sum of a holomorphic function is holomorphic

`HeckeSlash/Holomorphic.lean` proves `mdifferentiable_heckeSlashSum` for the unweighted sum.
This file is the nebentypus-twisted counterpart.

The twisted sum runs over the *same* slashes as the unweighted one, each scaled by the constant
`nebentypusWeight χ D v`. Holomorphy is closed under scaling by a constant, so no property of
the character is used here — only that its value is a scalar — and the proof is the untwisted
one with `MDifferentiable.const_smul` inserted at the summand.

## Main results

* `HeckeRing.GL2.mdifferentiable_twistedHeckeSlashSum`: the twisted slash sum of a holomorphic
  function is holomorphic.
-/

public section

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup DoubleCoset
  HeckeRing.GLn

open scoped MatrixGroups ModularForm Manifold

namespace HeckeRing.GL2

variable {N : ℕ} (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
  (D : HeckeCoset (Delta0 N) ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ)))

variable [NeZero N]

-- The enumeration `∑` needs, supplied exactly as in `HeckeSlash/Nebentypus/Independence.lean`
-- so that the sums are the same term. Taken as an attribute rather than a fresh anonymous
-- instance: two sibling modules declaring one independently collide on its generated name when
-- a third imports both.
attribute [local instance] Fintype.ofFinite

/-- **The twisted slash sum of a holomorphic function is holomorphic.** Together with the twisted
invariance of `HeckeSlash/Nebentypus/Invariance.lean` this supplies one of the two extra
conditions a `ModularForm` carries over a `SlashInvariantForm`; boundedness at the cusps is
`isBoundedAt_twistedHeckeSlashSum`. -/
lemma mdifferentiable_twistedHeckeSlashSum {f : ℍ → ℂ} (hf : MDiff f) :
    MDiff (twistedHeckeSlashSum k χ D f) := by
  -- `twistedHeckeSlashSum` is not `@[expose]`, so `twistedHeckeSlashSum_def` is what makes the
  -- sum visible; the weight is then peeled off by `const_smul`, and what remains is exactly the
  -- summand of the untwisted proof — a *rational* slash, restated at the real image by
  -- `rat_slash` so that mathlib's `MDifferentiable.slash` applies.
  rw [twistedHeckeSlashSum_def]
  refine MDifferentiable.sum fun v _ ↦ MDifferentiable.const_smul _ ?_
  rw [ModularForm.rat_slash]
  exact hf.slash k _

end HeckeRing.GL2

end
