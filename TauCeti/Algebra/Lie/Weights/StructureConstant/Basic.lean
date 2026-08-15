/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Lie.Weights.Root.String
public import TauCeti.Algebra.Lie.Weights.Sl2System

/-!
# Structure constants of a normalised root-vector system

Let `x` be an `IsSl2System` in a finite-dimensional Lie algebra with non-degenerate Killing form.
Thus `x α` is a root vector of `α`, and opposite root vectors are normalised by

```text
⁅x α, x (-α)⁆ = α∨.
```

When `γ = α + β` is a non-zero root, the root space of `γ` is the line spanned by `x γ`.
Consequently there is a unique scalar `N` such that

```text
⁅x α, x β⁆ = N • x γ.
```

This file packages that scalar as `TauCeti.IsSl2System.structureConstant`. Its characteristic
equation and uniqueness theorem keep downstream arguments independent of its choice-based
implementation. The constants are non-zero when all three weights are roots, are skew-symmetric in
`α` and `β`, transform by the expected ratio when a normalised system is rescaled, and satisfy the
root-string product formula proved in `TauCeti/Algebra/Lie/Weights/Root/String.lean`.

These are the scalar identities needed before a coherent choice of signs can upgrade an
`IsSl2System` to a Chevalley basis with constants `±(p + 1)`. This advances the explicit
Chevalley--Demazure construction in Layer 9 of `TauCetiRoadmap/ReductiveGroups/README.md`; it does
not assert that an arbitrary normalised system already has integral structure constants.

## Main definitions and results

* `TauCeti.IsSl2System.structureConstant`: the coefficient of `x γ` in `⁅x α, x β⁆` when
  `γ = α + β`.
* `TauCeti.IsSl2System.lie_eq_structureConstant_smul` and
  `TauCeti.IsSl2System.eq_structureConstant_iff`: the characteristic equation and uniqueness.
* `TauCeti.IsSl2System.structureConstant_ne_zero`: nonvanishing when `α`, `β`, and `γ` are roots.
* `TauCeti.IsSl2System.structureConstant_skew`: skew-symmetry in the first two roots.
* `TauCeti.IsSl2System.mul_structureConstant_eq_of_eq_smul`: transformation under a rescaling of
  the root vectors.
* `TauCeti.IsSl2System.structureConstant_mul_structureConstant`: the root-string product formula.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§25.1--25.2.
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

variable {x y : Weight K H L → L} (hx : IsSl2System x)
  (α β γ : Weight K H L) (hγ : γ.IsNonZero)
  (hαβ : (γ : H → K) = (α : H → K) + β)

include hx

/-- The structure constant of a normalised root-vector system: the unique scalar `N` satisfying
`⁅x α, x β⁆ = N • x γ` when the non-zero root `γ` is the sum of `α` and `β`.

The public interface is the characteristic equation
`TauCeti.IsSl2System.lie_eq_structureConstant_smul` and its uniqueness restatement
`TauCeti.IsSl2System.eq_structureConstant_iff`; consumers need not unfold this choice. -/
noncomputable def structureConstant : K :=
  Classical.choose (hx.exists_lie_eq_smul_of_coe_eq_add α β γ hγ hαβ)

/-- The bracket equation defining the structure constant of a normalised root-vector system. -/
theorem lie_eq_structureConstant_smul :
    ⁅x α, x β⁆ = hx.structureConstant α β γ hγ hαβ • x γ :=
  Classical.choose_spec (hx.exists_lie_eq_smul_of_coe_eq_add α β γ hγ hαβ)

/-- A scalar is the structure constant exactly when it gives the bracket of the corresponding root
vectors. -/
@[simp]
theorem eq_structureConstant_iff (N : K) :
    N = hx.structureConstant α β γ hγ hαβ ↔ ⁅x α, x β⁆ = N • x γ := by
  constructor
  · rintro rfl
    exact hx.lie_eq_structureConstant_smul α β γ hγ hαβ
  · intro hN
    exact smul_left_injective K (hx.ne_zero γ hγ)
      (hN.symm.trans (hx.lie_eq_structureConstant_smul α β γ hγ hαβ))

/-- The structure constant is non-zero when both input weights and their sum are roots. -/
theorem structureConstant_ne_zero (hα : α.IsNonZero) (hβ : β.IsNonZero) :
    hx.structureConstant α β γ hγ hαβ ≠ 0 := by
  have hxγ : x γ ∈ rootSpace H ((α : H → K) + β) := by
    rw [← hαβ]
    exact hx.mem_rootSpace γ
  have hroot : rootSpace H ((α : H → K) + β) ≠ ⊥ := by
    intro hbot
    exact hx.ne_zero γ hγ (by simpa [hbot] using hxγ)
  exact ne_zero_of_lie_eq_smul hα hβ hroot (hx.mem_rootSpace α) (hx.ne_zero α hα)
    (hx.mem_rootSpace β) (hx.ne_zero β hβ)
    (hx.lie_eq_structureConstant_smul α β γ hγ hαβ)

/-- Swapping the two input roots negates their structure constant. -/
theorem structureConstant_skew :
    hx.structureConstant β α γ hγ (hαβ.trans (add_comm _ _)) =
      -hx.structureConstant α β γ hγ hαβ := by
  symm
  rw [hx.eq_structureConstant_iff β α γ hγ (hαβ.trans (add_comm _ _))]
  calc
    ⁅x β, x α⁆ = -⁅x α, x β⁆ := (lie_skew (x β) (x α)).symm
    _ = -(hx.structureConstant α β γ hγ hαβ • x γ) :=
      congrArg Neg.neg (hx.lie_eq_structureConstant_smul α β γ hγ hαβ)
    _ = -hx.structureConstant α β γ hγ hαβ • x γ := (neg_smul _ _).symm

variable (hy : IsSl2System y)

include hy

/-- Structure constants transform by the expected ratio under a rescaling of a normalised
root-vector system. If `y α = a • x α`, `y β = b • x β`, and `y γ = c • x γ`, then
`c * N_y(α, β) = a * b * N_x(α, β)`.

The division-free form is valid over the ambient field without asking callers to supply the
already implied fact `c ≠ 0`. -/
theorem mul_structureConstant_eq_of_eq_smul (a b c : K)
    (ha : y α = a • x α) (hb : y β = b • x β) (hc : y γ = c • x γ) :
    c * hy.structureConstant α β γ hγ hαβ =
      a * b * hx.structureConstant α β γ hγ hαβ := by
  apply smul_left_injective K (hx.ne_zero γ hγ)
  calc
    (c * hy.structureConstant α β γ hγ hαβ) • x γ =
        hy.structureConstant α β γ hγ hαβ • (c • x γ) := by
          rw [smul_smul, mul_comm]
    _ = hy.structureConstant α β γ hγ hαβ • y γ := by rw [hc]
    _ = ⁅y α, y β⁆ := (hy.lie_eq_structureConstant_smul α β γ hγ hαβ).symm
    _ = ⁅a • x α, b • x β⁆ := by rw [← ha, ← hb]
    _ = (a * b) • ⁅x α, x β⁆ := by rw [smul_lie, lie_smul, smul_smul]
    _ = (a * b) • (hx.structureConstant α β γ hγ hαβ • x γ) := by
      rw [hx.lie_eq_structureConstant_smul α β γ hγ hαβ]
    _ = (a * b * hx.structureConstant α β γ hγ hαβ) • x γ := by rw [smul_smul]

omit hy in
/-- The two structure constants in one root string multiply to the combinatorial root-string
coefficient. If `γ = α + β`, then

```text
N(α, β) * N(-α, γ) = q * (p + 1),
```

where `β - pα, …, β, …, β + qα` is the `α`-string through `β`. -/
theorem structureConstant_mul_structureConstant (hα : α.IsNonZero) (hβ : β.IsNonZero) :
    hx.structureConstant α β γ hγ hαβ *
        hx.structureConstant (-α) γ β hβ (by
          rw [Weight.coe_neg, hαβ]
          abel) =
      (chainTopCoeff α β * (chainBotCoeff α β + 1) : ℕ) := by
  apply mul_eq_of_lie_eq_smul hα hβ (hx.isSl2Triple α hα) (hx.mem_rootSpace α)
    (hx.mem_rootSpace (-α)) (hx.mem_rootSpace β) (hx.ne_zero β hβ)
    (hx.lie_eq_structureConstant_smul α β γ hγ hαβ)
    (hx.lie_eq_structureConstant_smul (-α) γ β hβ (by
      rw [Weight.coe_neg, hαβ]
      abel))

end IsSl2System

end TauCeti
