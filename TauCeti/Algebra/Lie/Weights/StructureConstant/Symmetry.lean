/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Weights.Killing
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
three root vectors with the negative of its opposite sends `N(α, β)` to `-N(-α, -β)`. These
hypotheses hold when the normalized family is a Chevalley system, chosen compatibly with the
Chevalley involution. Second, invariance of the Killing form gives the cyclic relation

```text
N(α, β) B(x(α + β), x(-α - β))
  = N(β, -α - β) B(x α, x(-α)).
```

The Killing factors are nonzero and explicitly evaluated by the preceding `IsSl2System` API, so
this is a genuine relation between the two constants rather than a vacuous equality. Together
these are the symmetry relations used when a normalized root-vector system is rescaled coherently
to a Chevalley basis. They advance the explicit Chevalley--Demazure construction in Layer 9 of
`TauCetiRoadmap/ReductiveGroups/README.md`; the existence of the coherent rescaling is not asserted
here.

## Main results

* `TauCeti.IsSl2System.mul_structureConstant_eq_of_map_eq_smul_neg`: the general scalar relation
  induced by a Lie endomorphism carrying three root vectors to their opposites.
* `TauCeti.IsSl2System.structureConstant_neg_neg_of_hom`: compatibility with a Lie endomorphism
  exchanging root vectors with the negatives of their opposites.
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

/-- **The scalars are multiplicative along a root sum, up to the structure constants.** Applying a
Lie endomorphism to `⁅x α, x β⁆ = N(α, β) • x γ` turns it into the bracket at the opposite
roots. -/
theorem mul_structureConstant_eq_of_map_eq_smul_neg (e : L →ₗ⁅K⁆ L) {a b c : K}
    (heα : e (x α) = a • x (-α)) (heβ : e (x β) = b • x (-β))
    (heγ : e (x γ) = c • x (-γ)) :
    c * hx.structureConstant α β γ hγ hαβ = a * b *
      hx.structureConstant (-α) (-β) (-γ) hγ.neg (by
        rw [Weight.coe_neg, Weight.coe_neg, Weight.coe_neg, hαβ]
        abel) := by
  have hneg : ((-γ : Weight K H L) : H → K) =
      ((-α : Weight K H L) : H → K) + ((-β : Weight K H L) : H → K) := by
    rw [Weight.coe_neg, Weight.coe_neg, Weight.coe_neg, hαβ]
    abel
  refine smul_left_injective K (hx.ne_zero (-γ) hγ.neg) ?_
  calc (c * hx.structureConstant α β γ hγ hαβ) • x (-γ)
      = hx.structureConstant α β γ hγ hαβ • (c • x (-γ)) := by
        rw [smul_smul, mul_comm]
    _ = hx.structureConstant α β γ hγ hαβ • e (x γ) := by rw [heγ]
    _ = e (hx.structureConstant α β γ hγ hαβ • x γ) := (map_smul _ _ _).symm
    _ = e ⁅x α, x β⁆ := by rw [← hx.lie_eq_structureConstant_smul α β γ hγ hαβ]
    _ = ⁅e (x α), e (x β)⁆ := e.map_lie (x α) (x β)
    _ = ⁅a • x (-α), b • x (-β)⁆ := by rw [heα, heβ]
    _ = (a * b) • ⁅x (-α), x (-β)⁆ := by rw [smul_lie, lie_smul, smul_smul]
    _ = (a * b) • (hx.structureConstant (-α) (-β) (-γ) hγ.neg hneg • x (-γ)) := by
        rw [hx.lie_eq_structureConstant_smul (-α) (-β) (-γ) hγ.neg]
    _ = (a * b * hx.structureConstant (-α) (-β) (-γ) hγ.neg hneg) • x (-γ) := by
        rw [smul_smul]

/-- If a Lie endomorphism sends the root vectors at `α`, `β`, and `γ = α + β` to the negatives of
their opposite root vectors, then it sends the corresponding structure constant to the negative
of the structure constant at `-α`, `-β`, and `-γ`.

Only the three values used in the equation are hypotheses. They are supplied uniformly when `x` is
a Chevalley system: a normalized family chosen compatibly with a Chevalley involution. -/
theorem structureConstant_neg_neg_of_hom (e : L →ₗ⁅K⁆ L)
    (heα : e (x α) = -x (-α)) (heβ : e (x β) = -x (-β))
    (heγ : e (x γ) = -x (-γ)) :
    hx.structureConstant (-α) (-β) (-γ) hγ.neg (by
        rw [Weight.coe_neg, Weight.coe_neg, Weight.coe_neg, hαβ]
        abel) =
      -hx.structureConstant α β γ hγ hαβ := by
  have h := hx.mul_structureConstant_eq_of_map_eq_smul_neg α β γ hγ hαβ e
    (a := -1) (b := -1) (c := -1) (by simpa using heα) (by simpa using heβ) (by simpa using heγ)
  linear_combination -h

/-- **Cyclic symmetry of normalized structure constants.** If `γ = α + β`, invariance of the
Killing form relates the constants of `(α, β, γ)` and `(β, -γ, -α)` after weighting by the
Killing pairings of opposite root vectors.

Both Killing factors are nonzero by `TauCeti.killingForm_ne_zero_of_mem_rootSpace`, and their exact
values are given by `TauCeti.IsSl2System.killingForm_root_neg_eq`, so the equality can safely be
cancelled or rewritten as a ratio downstream. -/
theorem structureConstant_mul_killingForm_eq (hα : α.IsNonZero) :
    hx.structureConstant α β γ hγ hαβ * killingForm K L (x γ) (x (-γ)) =
      hx.structureConstant β (-γ) (-α) hα.neg (by
          rw [Weight.coe_neg, Weight.coe_neg, hαβ]
          abel) * killingForm K L (x α) (x (-α)) := by
  have hβγ : ((-α : Weight K H L) : H → K) =
      (β : H → K) + ((-γ : Weight K H L) : H → K) := by
    rw [Weight.coe_neg, Weight.coe_neg, hαβ]
    abel
  calc
    hx.structureConstant α β γ hγ hαβ * killingForm K L (x γ) (x (-γ)) =
        killingForm K L ⁅x α, x β⁆ (x (-γ)) := by
      rw [hx.lie_eq_structureConstant_smul α β γ hγ hαβ]
      simp
    _ = killingForm K L (x α) ⁅x β, x (-γ)⁆ :=
      LieModule.traceForm_apply_lie_apply K L L (x α) (x β) (x (-γ))
    _ = killingForm K L (x α)
        (hx.structureConstant β (-γ) (-α) hα.neg hβγ • x (-α)) := by
      rw [hx.lie_eq_structureConstant_smul β (-γ) (-α) hα.neg hβγ]
    _ = hx.structureConstant β (-γ) (-α) hα.neg hβγ *
        killingForm K L (x α) (x (-α)) := by
      simp

end IsSl2System

end TauCeti
