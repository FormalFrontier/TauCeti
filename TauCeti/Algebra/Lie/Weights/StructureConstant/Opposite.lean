/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Weights.Root.String
public import TauCeti.Algebra.Lie.Weights.StructureConstant.Symmetry

/-!
# Opposite structure constants multiply to `-(p + 1)²`

Let `x` be an `IsSl2System` in a finite-dimensional Lie algebra with non-degenerate Killing form
over a field of characteristic zero, so that `⁅x α, x (-α)⁆ = α∨`, and let `γ = α + β` be a root.
Writing

```text
⁅x α, x β⁆ = N(α, β) x γ,
```

this file proves the identity

```text
N(α, β) * N(-α, -β) = -(p + 1)²,      p = chainBotCoeff α β.
```

Nothing beyond the normalisation `⁅x α, x (-α)⁆ = α∨` is assumed: no Chevalley involution, and no
integrality of the constants. The proof combines the root-string product formula, the cyclic
Killing-form symmetry applied to the triple `(γ, -α, β)`, and the invariant root-length ratio.

The identity is exactly the rescaling invariant of a normalised system. Replacing `x` by
`c α • x α` with `c α * c (-α) = 1` multiplies `N(α, β)` by `c α * c β / c γ` and `N(-α, -β)` by
its inverse, so the product is the same for every normalised system, and the two constants
determine each other. The consequence recorded here is that the Chevalley-involution symmetry
`N(-α, -β) = -N(α, β)` holds precisely when `N(α, β)` is one of the Chevalley integers `±(p + 1)`.
That equivalence turns the compatibility with a Chevalley involution, which is data, into a
property of the structure constants alone.

## Main results

* `TauCeti.IsSl2System.structureConstant_mul_structureConstant_neg_neg`: the product identity.
* `TauCeti.IsSl2System.structureConstant_neg_neg_eq_neg_iff`: the Chevalley-involution symmetry
  holds exactly when the constant is `±(p + 1)`.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §25.2.
* R. W. Carter, *Simple Groups of Lie Type*, §4.1.

This advances the Chevalley-basis input to the explicit Chevalley--Demazure construction in Layer
9 of `TauCetiRoadmap/ReductiveGroups/README.md`, consumed by milestone L0 of the `CFSGStatement`
roadmap.
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

include hx hα hβ hγ hαβ

/-- **Opposite structure constants multiply to `-(p + 1)²`.** For a normalised root-vector system
and a root `γ = α + β`,

```text
N(α, β) * N(-α, -β) = -(p + 1)²,
```

where `p = chainBotCoeff α β`. No compatibility with a Chevalley involution is assumed: the
identity holds for every normalised system, and is invariant under the rescalings that relate two
of them.

The proof multiplies the root-string product formula `N(α, β) N(-α, γ) = q (p + 1)` by the cyclic
Killing-form symmetry of the triple `(γ, -α, β)`, which rewrites `N(-α, γ)` in terms of
`N(-α, -β)`, and then cancels `q` against the invariant root-length ratio
`q B(x β, x (-β)) = (p + 1) B(x γ, x (-γ))`. -/
theorem structureConstant_mul_structureConstant_neg_neg :
    hx.structureConstant α β γ hγ hαβ *
        hx.structureConstant (-α) (-β) (-γ) hγ.neg (by
          rw [Weight.coe_neg, Weight.coe_neg, Weight.coe_neg, hαβ]
          abel) =
      -(((chainBotCoeff α β + 1 : ℕ) : K) ^ 2) := by
  -- `β` is the sum of `γ` and `-α`, in both orders.
  have hβγ : (β : H → K) = ((-α : Weight K H L) : H → K) + γ := by
    rw [Weight.coe_neg, hαβ]
    abel
  have hγα : (β : H → K) = (γ : H → K) + ((-α : Weight K H L) : H → K) := by
    rw [Weight.coe_neg, hαβ]
    abel
  -- The three inputs.
  have hprod := hx.structureConstant_mul_structureConstant α β γ hγ hαβ hα hβ
  have hskew := hx.structureConstant_skew (-α) γ β hβ hβγ
  have hcyc := hx.structureConstant_mul_killingForm_eq γ (-α) β hβ hγα hγ
  have hlen := hx.chainTopCoeff_mul_killingForm_root_neg_eq α β γ hα hβ hγ hαβ
  -- The Killing pairing of opposite root vectors at `γ` is non-zero, so it can be cancelled.
  have hkill : killingForm K L (x γ) (x (-γ)) ≠ 0 :=
    killingForm_ne_zero_of_mem_rootSpace hγ (hx.mem_rootSpace γ) (hx.ne_zero γ hγ)
      (hx.mem_rootSpace (-γ)) (hx.ne_zero (-γ) hγ.neg)
  apply mul_right_cancel₀ hkill
  calc
    hx.structureConstant α β γ hγ hαβ *
          hx.structureConstant (-α) (-β) (-γ) hγ.neg _ *
          killingForm K L (x γ) (x (-γ)) =
        hx.structureConstant α β γ hγ hαβ *
          (hx.structureConstant (-α) (-β) (-γ) hγ.neg _ *
            killingForm K L (x γ) (x (-γ))) := by ring
    _ = hx.structureConstant α β γ hγ hαβ *
          (hx.structureConstant γ (-α) β hβ hγα * killingForm K L (x β) (x (-β))) := by
        rw [hcyc]
    _ = hx.structureConstant α β γ hγ hαβ *
          (-hx.structureConstant (-α) γ β hβ hβγ * killingForm K L (x β) (x (-β))) := by
        rw [hskew]
    _ = -(hx.structureConstant α β γ hγ hαβ * hx.structureConstant (-α) γ β hβ hβγ) *
          killingForm K L (x β) (x (-β)) := by ring
    _ = -((chainTopCoeff α β * (chainBotCoeff α β + 1) : ℕ) : K) *
          killingForm K L (x β) (x (-β)) := by rw [hprod]
    _ = -((chainBotCoeff α β + 1 : ℕ) : K) *
          ((chainTopCoeff α β : K) * killingForm K L (x β) (x (-β))) := by
        push_cast
        ring
    _ = -((chainBotCoeff α β + 1 : ℕ) : K) *
          (((chainBotCoeff α β + 1 : ℕ) : K) * killingForm K L (x γ) (x (-γ))) := by
        rw [hlen]
    _ = -(((chainBotCoeff α β + 1 : ℕ) : K) ^ 2) * killingForm K L (x γ) (x (-γ)) := by ring

/-- **The Chevalley-involution symmetry is integrality.** For a normalised root-vector system and
a root `γ = α + β`, the structure constants at `(α, β)` and `(-α, -β)` are negatives of each other
exactly when the constant at `(α, β)` is one of the Chevalley integers `±(p + 1)`.

The forward direction is the reason a Chevalley system has integral structure constants; the
reverse direction is what lets a Chevalley involution be built from an integrally normalised
system rather than assumed alongside it. -/
theorem structureConstant_neg_neg_eq_neg_iff :
    hx.structureConstant (-α) (-β) (-γ) hγ.neg (by
        rw [Weight.coe_neg, Weight.coe_neg, Weight.coe_neg, hαβ]
        abel) =
      -hx.structureConstant α β γ hγ hαβ ↔
    hx.structureConstant α β γ hγ hαβ = ((chainBotCoeff α β + 1 : ℕ) : K) ∨
      hx.structureConstant α β γ hγ hαβ = -((chainBotCoeff α β + 1 : ℕ) : K) := by
  have hmul := hx.structureConstant_mul_structureConstant_neg_neg α β γ hα hβ hγ hαβ
  have hne : hx.structureConstant α β γ hγ hαβ ≠ 0 :=
    hx.structureConstant_ne_zero α β γ hγ hαβ hα hβ
  rw [← sq_eq_sq_iff_eq_or_eq_neg]
  constructor
  · intro h
    rw [h] at hmul
    have : -hx.structureConstant α β γ hγ hαβ ^ 2 =
        -(((chainBotCoeff α β + 1 : ℕ) : K) ^ 2) := by
      rw [← hmul]; ring
    exact neg_injective this
  · intro h
    apply mul_left_cancel₀ hne
    rw [hmul, ← h]
    ring

end IsSl2System

end TauCeti
