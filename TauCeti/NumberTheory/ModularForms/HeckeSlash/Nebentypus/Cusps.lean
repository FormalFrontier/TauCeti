/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Cusps
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Nebentypus.Basic

/-!
# The twisted slash sum at the cusps

`HeckeSlash/Cusps.lean` proves `isZeroAt_heckeSlashSum` and `isBoundedAt_heckeSlashSum` for the
unweighted sum. This file is the nebentypus-twisted counterpart.

As in `HeckeSlash/Nebentypus/Holomorphic.lean`, the summands are the unweighted ones scaled by
the constant `nebentypusWeight χ D v`, so nothing about the character is used — only that its
value is a scalar. The summand-wise statements are the existing `OnePoint.isZeroAt_rat_slash`
and `OnePoint.isBoundedAt_rat_slash`, closed under `OnePoint.IsZeroAt.const_smul` and
`OnePoint.IsBoundedAt.const_smul` for the weight and then under `OnePoint.IsZeroAt.sum` and
`OnePoint.IsBoundedAt.sum` for the sum.

## Main results

* `HeckeRing.GL2.isZeroAt_twistedHeckeSlashSum`: the twisted slash sum vanishes at every cusp
  when the function does.
* `HeckeRing.GL2.isBoundedAt_twistedHeckeSlashSum`: the twisted slash sum is bounded at every
  cusp when the function is.
-/

public section

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup DoubleCoset
  HeckeRing.GLn

open scoped MatrixGroups ModularForm

namespace HeckeRing.GL2

variable {N : ℕ} (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
  (D : HeckeCoset (Delta0 N) ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ)))

variable [NeZero N]

-- The enumeration `∑` needs, supplied exactly as in `HeckeSlash/Nebentypus/Independence.lean`
-- so that the sums are the same term. Taken as an attribute rather than a fresh anonymous
-- instance: two sibling modules declaring one independently collide on its generated name when
-- a third imports both.
attribute [local instance] Fintype.ofFinite

/-- **The twisted slash sum vanishes at every cusp** when the function does. -/
lemma isZeroAt_twistedHeckeSlashSum {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic] {f : ℍ → ℂ}
    (hf : ∀ c : OnePoint ℝ, IsCusp c Γ → c.IsZeroAt f k) {c : OnePoint ℝ} (hc : IsCusp c Γ) :
    c.IsZeroAt (twistedHeckeSlashSum k χ D f) k := by
  rw [twistedHeckeSlashSum_def]
  exact OnePoint.IsZeroAt.sum fun v _ ↦
    (OnePoint.isZeroAt_rat_slash k (rightCosetRep D v) hf hc).const_smul _

/-- **The twisted slash sum is bounded at every cusp** when the function is. -/
lemma isBoundedAt_twistedHeckeSlashSum {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic] {f : ℍ → ℂ}
    (hf : ∀ c : OnePoint ℝ, IsCusp c Γ → c.IsBoundedAt f k) {c : OnePoint ℝ} (hc : IsCusp c Γ) :
    c.IsBoundedAt (twistedHeckeSlashSum k χ D f) k := by
  rw [twistedHeckeSlashSum_def]
  exact OnePoint.IsBoundedAt.sum fun v _ ↦
    (OnePoint.isBoundedAt_rat_slash k (rightCosetRep D v) hf hc).const_smul _

end HeckeRing.GL2

end
