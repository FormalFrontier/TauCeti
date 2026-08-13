/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Lie.Weights.StructureConstant.Basic

/-!
# Symmetries of root-vector structure constants

Let `x` be an `IsSl2System`, so that its root vectors satisfy
`⁅x α, x (-α)⁆ = α∨`. The structure constants of `x` were defined in
`TauCeti.Algebra.Lie.Weights.StructureConstant.Basic` by

```text
⁅x α, x β⁆ = N(α, β) x(α + β).
```

This file proves two symmetries of these constants. First, a Lie endomorphism exchanging each of the
three root vectors with the negative of its opposite sends `N(α, β)` to `-N(-α, -β)`. This is the
abstract form of the symmetry supplied by the Chevalley involution. Second, invariance of the
Killing form gives the cyclic relation

```text
N(α, β) B(x(α + β), x(-α - β))
  = N(β, -α - β) B(x α, x(-α)).
```

The Killing factors are nonzero, so this is a genuine relation between the two constants rather
than a vacuous equality. Together these are the symmetry relations used when a normalized
root-vector system is rescaled coherently to a Chevalley basis. They advance the explicit
Chevalley--Demazure construction in Layer 9 of `TauCetiRoadmap/ReductiveGroups/README.md`; the
existence of the coherent rescaling is not asserted here.

## Main results

* `TauCeti.IsSl2System.structureConstant_neg_neg_of_hom`: compatibility with a Lie endomorphism
  exchanging root vectors with the negatives of their opposites.
* `TauCeti.IsSl2System.killingForm_root_neg_ne_zero`: opposite normalized root vectors have
  nonzero Killing pairing.
* `TauCeti.IsSl2System.structureConstant_mul_killingForm_eq`: the cyclic Killing-form symmetry.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §25.2.
* R. W. Carter, *Simple Groups of Lie Type*, §4.1.
-/

public section

namespace TauCeti

open LieAlgebra LieModule LieAlgebra.IsKilling

universe u v

variable {K : Type u} {L : Type v} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [LieAlgebra.IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [LieModule.IsTriangularizable K H L]

namespace IsSl2System

variable {x : Weight K H L → L} (hx : IsSl2System x)
  (α β γ : Weight K H L) (hγ : γ.IsNonZero)
  (hαβ : (γ : H → K) = (α : H → K) + β)

include hx

/-- If a Lie endomorphism sends the root vectors at `α`, `β`, and `γ = α + β` to the negatives of
their opposite root vectors, then it sends the corresponding structure constant to the negative
of the structure constant at `-α`, `-β`, and `-γ`.

Only the three values used in the equation are hypotheses. A later Chevalley involution supplies
them uniformly for every root. -/
theorem structureConstant_neg_neg_of_hom (e : L →ₗ⁅K⁆ L)
    (heα : e (x α) = -x (-α)) (heβ : e (x β) = -x (-β))
    (heγ : e (x γ) = -x (-γ)) :
    hx.structureConstant (-α) (-β) (-γ) hγ.neg (by
        rw [Weight.coe_neg, Weight.coe_neg, Weight.coe_neg, hαβ]
        abel) =
      -hx.structureConstant α β γ hγ hαβ := by
  symm
  rw [hx.eq_structureConstant_iff (-α) (-β) (-γ) hγ.neg]
  calc
    ⁅x (-α), x (-β)⁆ = ⁅-x (-α), -x (-β)⁆ := by simp
    _ = ⁅e (x α), e (x β)⁆ := by rw [heα, heβ]
    _ = e ⁅x α, x β⁆ := (e.map_lie (x α) (x β)).symm
    _ = e (hx.structureConstant α β γ hγ hαβ • x γ) := by
      rw [hx.lie_eq_structureConstant_smul α β γ hγ hαβ]
    _ = hx.structureConstant α β γ hγ hαβ • e (x γ) := e.map_smul _ _
    _ = hx.structureConstant α β γ hγ hαβ • -x (-γ) := by rw [heγ]
    _ = -hx.structureConstant α β γ hγ hαβ • x (-γ) := by
      rw [smul_neg, neg_smul]

/-- Opposite root vectors in a normalized root-vector system have nonzero Killing pairing.

Indeed, their bracket is the nonzero coroot, while Mathlib's root-space formula expresses that
same bracket as their Killing pairing times the vector dual to the root. -/
theorem killingForm_root_neg_ne_zero (hα : α.IsNonZero) :
    killingForm K L (x α) (x (-α)) ≠ 0 := by
  intro hzero
  have hlie := lie_eq_killingForm_smul_of_mem_rootSpace_of_mem_rootSpace_neg
    (hx.mem_rootSpace α) (hx.mem_rootSpace (-α))
  rw [hzero, zero_smul, hx.lie_neg α hα] at hlie
  have hcoroot : (coroot α : L) ≠ 0 := by
    simpa only [ne_eq, ZeroMemClass.coe_eq_zero, coroot_eq_zero_iff] using hα
  exact hcoroot hlie

/-- **Cyclic symmetry of normalized structure constants.** If `γ = α + β`, invariance of the
Killing form relates the constants of `(α, β, γ)` and `(β, -γ, -α)` after weighting by the
Killing pairings of opposite root vectors.

Both Killing factors are nonzero by
`TauCeti.IsSl2System.killingForm_root_neg_ne_zero`, so the equality can safely be cancelled or
divided by either factor downstream. -/
theorem structureConstant_mul_killingForm_eq (hα : α.IsNonZero) :
    hx.structureConstant α β γ hγ hαβ * killingForm K L (x γ) (x (-γ)) =
      hx.structureConstant β (-γ) (-α) hα.neg (by
          rw [Weight.coe_neg, Weight.coe_neg, hαβ]
          abel) * killingForm K L (x α) (x (-α)) := by
  calc
    hx.structureConstant α β γ hγ hαβ * killingForm K L (x γ) (x (-γ)) =
        killingForm K L ⁅x α, x β⁆ (x (-γ)) := by
      rw [hx.lie_eq_structureConstant_smul α β γ hγ hαβ]
      simp
    _ = killingForm K L (x α) ⁅x β, x (-γ)⁆ :=
      LieModule.traceForm_apply_lie_apply K L L (x α) (x β) (x (-γ))
    _ = killingForm K L (x α)
        (hx.structureConstant β (-γ) (-α) hα.neg (by
            rw [Weight.coe_neg, Weight.coe_neg, hαβ]
            abel) • x (-α)) := by
      rw [hx.lie_eq_structureConstant_smul β (-γ) (-α) hα.neg]
    _ = hx.structureConstant β (-γ) (-α) hα.neg (by
          rw [Weight.coe_neg, Weight.coe_neg, hαβ]
          abel) * killingForm K L (x α) (x (-α)) := by
      simp

end IsSl2System

end TauCeti
