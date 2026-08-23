/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Weights.StructureConstant.Symmetry

/-!
# The square of a Chevalley structure constant

Let `x` be an `IsSl2System`, so its opposite root vectors are normalized by

```text
⁅x α, x (-α)⁆ = α∨.
```

Suppose also that a Lie endomorphism sends the root vectors at `α`, `β`, and
`γ = α + β` to the negatives of their opposite root vectors. This is the local part of the
Chevalley-involution compatibility required of a Chevalley system. Writing

```text
⁅x α, x β⁆ = N x γ,
⁅x (-α), x γ⁆ = M x β,
```

the Chevalley-involution and cyclic Killing-form symmetries give

```text
M B(x β, x (-β)) = N B(x γ, x (-γ)).
```

The root-string calculation gives `N M = q (p + 1)`, where
`β - pα, ..., β, ..., β + qα` is the `α`-string through `β`. Combining them determines the
square of `N`:

```text
N² B(x γ, x (-γ)) = q (p + 1) B(x β, x (-β)).
```

This weighted square identity is the local normalization calculation in the Chevalley basis
theorem. The usual root-length identity

```text
q B(x β, x (-β)) = (p + 1) B(x γ, x (-γ))
```

then gives `N = ±(p + 1)`. The last two theorems expose precisely that cancellation step, so the
remaining global construction only has to supply a compatible Chevalley system and the standard
root-length identity; it does not have to repeat the structure-constant algebra.

## Main results

* `TauCeti.IsSl2System.structureConstant_neg_add_mul_killingForm_eq`: the two consecutive
  structure constants in the root string are related by the Killing pairings.
* `TauCeti.IsSl2System.structureConstant_sq_mul_killingForm_eq`: the weighted square identity.
* `TauCeti.IsSl2System.structureConstant_sq_eq_natCast_sq_of_killingForm_ratio`: the square is
  `(p + 1)²` once the root-length ratio is supplied.
* `TauCeti.IsSl2System.structureConstant_eq_natCast_or_eq_neg_natCast_of_killingForm_ratio`: the
  resulting Chevalley normalization `N = ±(p + 1)`.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §25.2.
* R. W. Carter, *Simple Groups of Lie Type*, §4.1.

This advances the Chevalley-basis input to the explicit Chevalley--Demazure construction in Layer
9 of `TauCetiRoadmap/ReductiveGroups/README.md`, consumed by milestone L0 of the
`CFSGStatement` roadmap.
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
  (α β γ : Weight K H L) (hα : α.IsNonZero) (hβ : β.IsNonZero) (hγ : γ.IsNonZero)
  (hαβ : (γ : H → K) = (α : H → K) + β)
  (e : L →ₗ⁅K⁆ L)
  (heα : e (x α) = -x (-α)) (heβ : e (x β) = -x (-β))
  (heγ : e (x γ) = -x (-γ))

include hx hβ hγ hαβ heα heβ heγ

/-- The structure constant for `⁅x (-α), x γ⁆` times the Killing pairing at `β` equals the
structure constant for `⁅x α, x β⁆` times the Killing pairing at `γ`, provided the three root
vectors are compatible with a Chevalley involution.

This is the relation that lets the root-string product formula determine a square rather than only
a product of two a priori unrelated constants. -/
theorem structureConstant_neg_add_mul_killingForm_eq :
    hx.structureConstant (-α) γ β hβ (by
        rw [Weight.coe_neg, hαβ]
        abel) * killingForm K L (x β) (x (-β)) =
      hx.structureConstant α β γ hγ hαβ * killingForm K L (x γ) (x (-γ)) := by
  have hγα : (β : H → K) = (γ : H → K) + (-α : Weight K H L) := by
    rw [Weight.coe_neg, hαβ]
    abel
  have hαγ : (β : H → K) = (-α : Weight K H L) + (γ : H → K) := by
    rw [Weight.coe_neg, hαβ]
    abel
  have hcyclic := hx.structureConstant_mul_killingForm_eq γ (-α) β hβ hγα hγ
  have hskew := hx.structureConstant_skew (-α) γ β hβ hαγ
  have hneg := hx.structureConstant_neg_neg_of_hom α β γ hγ hαβ e heα heβ heγ
  rw [hskew, hneg] at hcyclic
  simpa only [neg_mul, neg_inj] using hcyclic

include hα

/-- **Weighted square formula for a Chevalley structure constant.** If `γ = α + β` and the root
vectors at `α`, `β`, and `γ` are compatible with a Chevalley involution, then

```text
N(α, β)² B(x γ, x (-γ)) = q (p + 1) B(x β, x (-β)),
```

where `p = chainBotCoeff α β` and `q = chainTopCoeff α β`.

Unlike the product formula in `TauCeti.IsSl2System.structureConstant_mul_structureConstant`, this
determines the square of the single constant attached to `⁅x α, x β⁆`. -/
theorem structureConstant_sq_mul_killingForm_eq :
    hx.structureConstant α β γ hγ hαβ ^ 2 * killingForm K L (x γ) (x (-γ)) =
      (chainTopCoeff α β * (chainBotCoeff α β + 1) : ℕ) *
        killingForm K L (x β) (x (-β)) := by
  have hratio := hx.structureConstant_neg_add_mul_killingForm_eq α β γ hβ hγ hαβ
    e heα heβ heγ
  have hproduct := hx.structureConstant_mul_structureConstant α β γ hγ hαβ hα hβ
  calc
    hx.structureConstant α β γ hγ hαβ ^ 2 * killingForm K L (x γ) (x (-γ)) =
        hx.structureConstant α β γ hγ hαβ *
          (hx.structureConstant α β γ hγ hαβ *
            killingForm K L (x γ) (x (-γ))) := by ring
    _ = hx.structureConstant α β γ hγ hαβ *
          (hx.structureConstant (-α) γ β hβ (by
              rw [Weight.coe_neg, hαβ]
              abel) * killingForm K L (x β) (x (-β))) := by rw [hratio]
    _ = (hx.structureConstant α β γ hγ hαβ *
          hx.structureConstant (-α) γ β hβ (by
            rw [Weight.coe_neg, hαβ]
            abel)) * killingForm K L (x β) (x (-β)) := by ring
    _ = (chainTopCoeff α β * (chainBotCoeff α β + 1) : ℕ) *
          killingForm K L (x β) (x (-β)) := by rw [hproduct]

/-- If the Killing pairings along a root string satisfy the standard root-length ratio, then the
square of the corresponding Chevalley-compatible structure constant is `(p + 1)²`.

The hypothesis is separated from the structure-constant calculation because it is a statement
about the invariant form of the root system, independent of the choice of root vectors. -/
theorem structureConstant_sq_eq_natCast_sq_of_killingForm_ratio
    (hlength : (chainTopCoeff α β : K) * killingForm K L (x β) (x (-β)) =
      (chainBotCoeff α β + 1 : ℕ) * killingForm K L (x γ) (x (-γ))) :
    hx.structureConstant α β γ hγ hαβ ^ 2 =
      ((chainBotCoeff α β + 1 : ℕ) : K) ^ 2 := by
  have hsquare := hx.structureConstant_sq_mul_killingForm_eq α β γ hα hβ hγ hαβ
    e heα heβ heγ
  have hkill : killingForm K L (x γ) (x (-γ)) ≠ 0 :=
    killingForm_ne_zero_of_mem_rootSpace hγ (hx.mem_rootSpace γ) (hx.ne_zero γ hγ)
      (hx.mem_rootSpace (-γ)) (hx.ne_zero (-γ) hγ.neg)
  apply mul_right_cancel₀ hkill
  rw [hsquare]
  calc
    (chainTopCoeff α β * (chainBotCoeff α β + 1) : ℕ) *
        killingForm K L (x β) (x (-β)) =
      ((chainBotCoeff α β + 1 : ℕ) : K) *
        ((chainTopCoeff α β : K) * killingForm K L (x β) (x (-β))) := by
          push_cast
          ring
    _ = ((chainBotCoeff α β + 1 : ℕ) : K) *
        (((chainBotCoeff α β + 1 : ℕ) : K) *
          killingForm K L (x γ) (x (-γ))) := by rw [hlength]
    _ = ((chainBotCoeff α β + 1 : ℕ) : K) ^ 2 *
        killingForm K L (x γ) (x (-γ)) := by ring

/-- Under the standard root-length ratio, a Chevalley-compatible structure constant is
`p + 1` or its negative. This is the integral normalization used by the Kostant form. -/
theorem structureConstant_eq_natCast_or_eq_neg_natCast_of_killingForm_ratio
    (hlength : (chainTopCoeff α β : K) * killingForm K L (x β) (x (-β)) =
      (chainBotCoeff α β + 1 : ℕ) * killingForm K L (x γ) (x (-γ))) :
    hx.structureConstant α β γ hγ hαβ = ((chainBotCoeff α β + 1 : ℕ) : K) ∨
      hx.structureConstant α β γ hγ hαβ = -((chainBotCoeff α β + 1 : ℕ) : K) :=
  sq_eq_sq_iff_eq_or_eq_neg.mp <|
    hx.structureConstant_sq_eq_natCast_sq_of_killingForm_ratio α β γ hα hβ hγ hαβ
      e heα heβ heγ hlength

end IsSl2System

end TauCeti
