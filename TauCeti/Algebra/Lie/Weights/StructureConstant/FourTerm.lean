/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.TraceForm
public import TauCeti.Algebra.Lie.Weights.InvariantForm
public import TauCeti.Algebra.Lie.Weights.Killing
public import TauCeti.Algebra.Lie.Weights.StructureConstant.Basic

/-!
# The four-term relation among root-vector structure constants

Let `x` be a `TauCeti.IsSl2System` in a Lie algebra `L` with non-degenerate Killing form, so that
`⁅x α, x β⁆ = N(α, β) x(α + β)` whenever `α + β` is a root. This file proves the relation between
the structure constants of four roots summing to zero.

Write `B` for the Killing form. Pairing the brackets of root vectors in twos, rather than iterating
them, is what makes the Jacobi identity readable at the level of structure constants: if
`α + β + γ + δ = 0` then `⁅x γ, x δ⁆` lies in the root space of `-(α + β)`, so `B ⁅x α, x β⁆
⁅x γ, x δ⁆` is `N(α, β) N(γ, δ)` weighted by `B (x μ) (x (-μ))` for `μ = α + β`, and it vanishes
outright when `α + β` is not a root. The cyclic identity
`TauCeti.traceForm_lie_lie_cyclic_eq_zero` therefore reads

```text
N(α, β) N(γ, δ) B(x μ, x (-μ)) + N(β, γ) N(α, δ) B(x ν, x (-ν))
  + N(γ, α) N(β, δ) B(x ρ, x (-ρ)) = 0
```

for `μ = α + β`, `ν = β + γ` and `ρ = γ + α`. Since `B (x μ) (x (-μ))` is `2 / ⟨μ, μ⟩` for the
invariant form `TauCeti.invForm` on weights, this is Carter's displayed relation

```text
N(α, β) N(γ, δ) / ⟨γ + δ, γ + δ⟩ + N(β, γ) N(α, δ) / ⟨α + δ, α + δ⟩
  + N(γ, α) N(β, δ) / ⟨β + δ, β + δ⟩ = 0,
```

recorded here as `TauCeti.IsSl2System.structureConstant_four_term_invForm`, whose denominators
are those of `μ`, `ν` and `ρ`: they agree with Carter's because `γ + δ = -(α + β)` and the form is
even, and likewise in the other two summands.

A summand drops out when its pair of roots does not sum to a root, and the resulting shorter
relations are the ones Carter's recursion over extraspecial pairs actually runs on: with one
summand absent the other two are negatives of each other, and with two absent the remaining pair
cannot sum to a root at all, which
`TauCeti.IsSl2System.rootSpace_add_eq_bot_of_rootSpace_add_eq_bot` reads off as a statement about
the root system.

Nothing here normalises the structure constants: the relation holds for every normalised family,
and the choice of a family whose constants are the Chevalley integers `±(p + 1)` is exactly what
it is an input to.

## Main results

* `TauCeti.IsSl2System.killingForm_lie_lie_eq_mul_mul` and
  `TauCeti.IsSl2System.killingForm_lie_lie_eq_zero_of_rootSpace_add_eq_bot`: the evaluation of a
  paired Killing bracket, in the case where the first pair sums to a root and in the case where it
  does not.
* `TauCeti.IsSl2System.structureConstant_four_term`: the four-term relation.
* `TauCeti.IsSl2System.structureConstant_four_term_of_rootSpace_add_eq_bot`: its two-summand form
  when one of the three pairs does not sum to a root.
* `TauCeti.IsSl2System.rootSpace_add_eq_bot_of_rootSpace_add_eq_bot`: two absent summands force
  the third pair not to sum to a root either.
* `TauCeti.IsSl2System.structureConstant_four_term_invForm`: Carter's displayed form of the
  relation, with the root lengths of the invariant form as denominators.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §4.1, Proposition 4.1.2.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §25.1.

## Roadmap

Layer 9 of `TauCetiRoadmap/ReductiveGroups/README.md` builds the split reductive group scheme over
`ℤ` "via a Chevalley basis and the Kostant `ℤ`-form of the enveloping algebra", and
`TauCeti.IsChevalleySystem` is that Chevalley basis. Producing one reduces, by
`TauCeti.IsSl2System.isChevalleyNormalized_iff_exists_isChevalleySystem`, to normalising the
structure constants of some family to `±(p + 1)`, which Carter performs in §4.2 by a recursion over
the extraspecial pairs enumerated in `TauCeti/LinearAlgebra/RootSystem/ExtraspecialPair.lean`. The
relation proved here is the identity that recursion propagates. Milestone L0 of
`TauCetiRoadmap/CFSGStatement/README.md` is the downstream consumer of the assembled pinned group
scheme.
-/

public section

namespace TauCeti

open LieAlgebra LieModule LieAlgebra.IsKilling Module

universe u v

variable {K : Type u} {L : Type v} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [LieAlgebra.IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [LieModule.IsTriangularizable K H L]

namespace IsSl2System

variable {x : Weight K H L → L} (hx : IsSl2System x) (α β γ δ : Weight K H L)

include hx

/-! ## Evaluating a pair of brackets against the Killing form -/

/-- The Killing pairing of two brackets of root vectors, when the first pair sums to the root `μ`
and the second to its opposite. Both brackets are then multiples of opposite root vectors, so the
pairing is the product of the two structure constants weighted by the Killing pairing of that
opposite pair. -/
theorem killingForm_lie_lie_eq_mul_mul (μ : Weight K H L) (hμ : μ.IsNonZero)
    (hμαβ : (μ : H → K) = (α : H → K) + β)
    (hμγδ : ((-μ : Weight K H L) : H → K) = (γ : H → K) + δ) :
    killingForm K L ⁅x α, x β⁆ ⁅x γ, x δ⁆ =
      hx.structureConstant α β μ hμ hμαβ * hx.structureConstant γ δ (-μ) hμ.neg hμγδ *
        killingForm K L (x μ) (x (-μ)) := by
  rw [hx.lie_eq_structureConstant_smul α β μ hμ hμαβ,
    hx.lie_eq_structureConstant_smul γ δ (-μ) hμ.neg hμγδ]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  ring

omit [CharZero K] in
/-- The Killing pairing of two brackets of root vectors vanishes when the first pair does not sum
to a root, since the first bracket is then already zero. -/
theorem killingForm_lie_lie_eq_zero_of_rootSpace_add_eq_bot
    (h : rootSpace H ((α : H → K) + β) = ⊥) :
    killingForm K L ⁅x α, x β⁆ ⁅x γ, x δ⁆ = 0 := by
  rw [hx.lie_eq_zero_of_rootSpace_add_eq_bot α β h, map_zero, LinearMap.zero_apply]

/-! ## The relation -/

/-- **The four-term relation.** Let `α`, `β`, `γ`, `δ` be weights whose sum is zero, and suppose
that `μ = α + β`, `ν = β + γ` and `ρ = γ + α` are roots, so that the six structure constants below
are defined. Then the three products, each weighted by the Killing pairing of the opposite pair of
root vectors it belongs to, sum to zero.

Requiring `μ`, `ν` and `ρ` to be roots already excludes the degenerate configurations in which two
of the four weights are opposite, since a `Weight` is a root exactly when it is non-zero. -/
theorem structureConstant_four_term (μ ν ρ : Weight K H L)
    (hμ : μ.IsNonZero) (hν : ν.IsNonZero) (hρ : ρ.IsNonZero)
    (hsum : (α : H → K) + β + γ + δ = 0)
    (hμαβ : (μ : H → K) = (α : H → K) + β)
    (hνβγ : (ν : H → K) = (β : H → K) + γ)
    (hργα : (ρ : H → K) = (γ : H → K) + α) :
    hx.structureConstant α β μ hμ hμαβ * hx.structureConstant γ δ (-μ) hμ.neg
          (Weight.coe_neg_eq_add_of_coe_eq_add hsum hμαβ) *
          killingForm K L (x μ) (x (-μ)) +
        hx.structureConstant β γ ν hν hνβγ * hx.structureConstant α δ (-ν) hν.neg
          (Weight.coe_neg_eq_add_of_coe_eq_add (a := (β : H → K)) (b := γ) (c := α) (d := δ)
            (by simpa only [add_comm, add_left_comm, add_assoc] using hsum) hνβγ) *
          killingForm K L (x ν) (x (-ν)) +
        hx.structureConstant γ α ρ hρ hργα * hx.structureConstant β δ (-ρ) hρ.neg
          (Weight.coe_neg_eq_add_of_coe_eq_add (a := (γ : H → K)) (b := α) (c := β) (d := δ)
            (by simpa only [add_comm, add_left_comm, add_assoc] using hsum) hργα) *
          killingForm K L (x ρ) (x (-ρ)) = 0 := by
  have hμγδ := Weight.coe_neg_eq_add_of_coe_eq_add hsum hμαβ
  have hναδ := Weight.coe_neg_eq_add_of_coe_eq_add
    (a := (β : H → K)) (b := γ) (c := α) (d := δ)
    (by simpa only [add_comm, add_left_comm, add_assoc] using hsum) hνβγ
  have hρβδ := Weight.coe_neg_eq_add_of_coe_eq_add
    (a := (γ : H → K)) (b := α) (c := β) (d := δ)
    (by simpa only [add_comm, add_left_comm, add_assoc] using hsum) hργα
  rw [← hx.killingForm_lie_lie_eq_mul_mul α β γ δ μ hμ hμαβ hμγδ,
    ← hx.killingForm_lie_lie_eq_mul_mul β γ α δ ν hν hνβγ hναδ,
    ← hx.killingForm_lie_lie_eq_mul_mul γ α β δ ρ hρ hργα hρβδ]
  exact traceForm_lie_lie_cyclic_eq_zero K L L (x α) (x β) (x γ) (x δ)

/-- The four-term relation when one of the three pairs does not sum to a root: the remaining two
summands are then negatives of one another. The pair left out is `γ + α`, which is the shape the
recursion of Carter's §4.2 uses, where one decomposition of a root is compared with another. -/
theorem structureConstant_four_term_of_rootSpace_add_eq_bot (μ ν : Weight K H L)
    (hμ : μ.IsNonZero) (hν : ν.IsNonZero)
    (hsum : (α : H → K) + β + γ + δ = 0)
    (hμαβ : (μ : H → K) = (α : H → K) + β)
    (hνβγ : (ν : H → K) = (β : H → K) + γ)
    (hρ : rootSpace H ((γ : H → K) + α) = ⊥) :
    hx.structureConstant α β μ hμ hμαβ * hx.structureConstant γ δ (-μ) hμ.neg
          (Weight.coe_neg_eq_add_of_coe_eq_add hsum hμαβ) *
          killingForm K L (x μ) (x (-μ)) +
        hx.structureConstant β γ ν hν hνβγ * hx.structureConstant α δ (-ν) hν.neg
          (Weight.coe_neg_eq_add_of_coe_eq_add (a := (β : H → K)) (b := γ) (c := α) (d := δ)
            (by simpa only [add_comm, add_left_comm, add_assoc] using hsum) hνβγ) *
          killingForm K L (x ν) (x (-ν)) = 0 := by
  have hμγδ := Weight.coe_neg_eq_add_of_coe_eq_add hsum hμαβ
  have hναδ := Weight.coe_neg_eq_add_of_coe_eq_add
    (a := (β : H → K)) (b := γ) (c := α) (d := δ)
    (by simpa only [add_comm, add_left_comm, add_assoc] using hsum) hνβγ
  rw [← hx.killingForm_lie_lie_eq_mul_mul α β γ δ μ hμ hμαβ hμγδ,
    ← hx.killingForm_lie_lie_eq_mul_mul β γ α δ ν hν hνβγ hναδ]
  have hzero := hx.killingForm_lie_lie_eq_zero_of_rootSpace_add_eq_bot γ α β δ hρ
  have hcyc := traceForm_lie_lie_cyclic_eq_zero K L L (x α) (x β) (x γ) (x δ)
  rw [hzero, add_zero] at hcyc
  exact hcyc

/-- Two absent summands force the third pair not to sum to a root either. If four roots sum to
zero, if `α + β` is not itself zero, and if neither `β + γ` nor `γ + α` is a root, then `α + β` is
not a root.

This is a root-system statement, obtained from the relation because a structure constant of two
roots whose sum is a root is non-zero and the Killing pairing of an opposite pair of root vectors
is non-zero. The hypothesis `α + β ≠ 0` cannot be dropped: for `β = -α` and `δ = -γ` the two
brackets are the coroots of `α` and `γ`, whose Killing pairing has no reason to vanish. -/
theorem rootSpace_add_eq_bot_of_rootSpace_add_eq_bot (hα : α.IsNonZero) (hβ : β.IsNonZero)
    (hγ : γ.IsNonZero) (hδ : δ.IsNonZero) (hsum : (α : H → K) + β + γ + δ = 0)
    (hαβ : (α : H → K) + β ≠ 0)
    (hν : rootSpace H ((β : H → K) + γ) = ⊥) (hρ : rootSpace H ((γ : H → K) + α) = ⊥) :
    rootSpace H ((α : H → K) + β) = ⊥ := by
  by_contra hbot
  -- The sum `α + β` is a non-zero weight of `L`, hence a root `μ`.
  set μ : Weight K H L := ⟨(α : H → K) + β, hbot⟩
  have hμαβ : (μ : H → K) = (α : H → K) + β := rfl
  have hμ : μ.IsNonZero := fun h0 ↦ hαβ (hμαβ ▸ h0)
  have hμγδ : ((-μ : Weight K H L) : H → K) = (γ : H → K) + δ :=
    Weight.coe_neg_eq_add_of_coe_eq_add hsum hμαβ
  -- The two vanishing pairs remove two of the three summands of the cyclic identity.
  have hcyc := traceForm_lie_lie_cyclic_eq_zero K L L (x α) (x β) (x γ) (x δ)
  rw [hx.killingForm_lie_lie_eq_zero_of_rootSpace_add_eq_bot β γ α δ hν,
    hx.killingForm_lie_lie_eq_zero_of_rootSpace_add_eq_bot γ α β δ hρ, add_zero, add_zero,
    hx.killingForm_lie_lie_eq_mul_mul α β γ δ μ hμ hμαβ hμγδ] at hcyc
  -- What is left is a product of three non-zero factors.
  have hN₁ := hx.structureConstant_ne_zero α β μ hμ hμαβ hα hβ
  have hN₂ := hx.structureConstant_ne_zero γ δ (-μ) hμ.neg hμγδ hγ hδ
  have hB : killingForm K L (x μ) (x (-μ)) ≠ 0 :=
    killingForm_ne_zero_of_mem_rootSpace hμ (hx.mem_rootSpace μ) (hx.ne_zero μ hμ)
      (hx.mem_rootSpace (-μ)) (hx.ne_zero (-μ) hμ.neg)
  exact (mul_ne_zero (mul_ne_zero hN₁ hN₂) hB) hcyc

/-! ## Carter's form, with the root lengths of the invariant form -/

/-- **Carter's form of the four-term relation.** The three products of structure constants,
divided by the lengths of the roots their pairs sum to, add to zero.

This is `TauCeti.IsSl2System.structureConstant_four_term` after replacing each Killing pairing by
`2 / ⟨μ, μ⟩` and cancelling the common factor `2`. The lengths appearing here are those of
`α + β`, `β + γ` and `γ + α`; Carter writes the relation with the lengths of `γ + δ`, `α + δ` and
`β + δ`, which are the same because those weights are the negatives of these and the form is
even. -/
theorem structureConstant_four_term_invForm (μ ν ρ : Weight K H L)
    (hμ : μ.IsNonZero) (hν : ν.IsNonZero) (hρ : ρ.IsNonZero)
    (hsum : (α : H → K) + β + γ + δ = 0)
    (hμαβ : (μ : H → K) = (α : H → K) + β)
    (hνβγ : (ν : H → K) = (β : H → K) + γ)
    (hργα : (ρ : H → K) = (γ : H → K) + α) :
    hx.structureConstant α β μ hμ hμαβ * hx.structureConstant γ δ (-μ) hμ.neg
          (Weight.coe_neg_eq_add_of_coe_eq_add hsum hμαβ) *
          (invForm (μ : Dual K H) μ)⁻¹ +
        hx.structureConstant β γ ν hν hνβγ * hx.structureConstant α δ (-ν) hν.neg
          (Weight.coe_neg_eq_add_of_coe_eq_add (a := (β : H → K)) (b := γ) (c := α) (d := δ)
            (by simpa only [add_comm, add_left_comm, add_assoc] using hsum) hνβγ) *
          (invForm (ν : Dual K H) ν)⁻¹ +
        hx.structureConstant γ α ρ hρ hργα * hx.structureConstant β δ (-ρ) hρ.neg
          (Weight.coe_neg_eq_add_of_coe_eq_add (a := (γ : H → K)) (b := α) (c := β) (d := δ)
            (by simpa only [add_comm, add_left_comm, add_assoc] using hsum) hργα) *
          (invForm (ρ : Dual K H) ρ)⁻¹ = 0 := by
  have hrel := hx.structureConstant_four_term α β γ δ μ ν ρ hμ hν hρ hsum hμαβ hνβγ hργα
  rw [hx.killingForm_root_neg_eq μ hμ, hx.killingForm_root_neg_eq ν hν,
    hx.killingForm_root_neg_eq ρ hρ] at hrel
  simp only [invForm_apply_apply, Weight.toLinear_apply]
  have htwo : (2 : K) ≠ 0 := two_ne_zero
  apply mul_left_cancel₀ htwo
  rw [mul_zero]
  linear_combination hrel

end IsSl2System

end TauCeti
