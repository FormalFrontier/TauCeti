/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-!
# Vanishing of exterior powers above the rank

This file records that the `d`th exterior power of a finite free module over a nontrivial
commutative ring vanishes as soon as `d` exceeds the rank of the module.

## Main results

* `exteriorPower.eq_zero_of_finrank_lt` states that every element of `⋀[R]^d M` is zero when
  `Module.finrank R M < d`.

## References

The exterior-power basis used in the proof is Mathlib's `Module.Basis.exteriorPower` from
`Mathlib.LinearAlgebra.ExteriorPower.Basis`, by Sophie Morel and Daniel Morrison.
-/

public section

universe u w

variable {R : Type u} {M : Type w}

namespace exteriorPower

variable [CommRing R] [Nontrivial R] [AddCommGroup M] [Module R M]
variable [Module.Free R M] [Module.Finite R M]

/-- An exterior power above the rank of a finite free module is zero. -/
theorem eq_zero_of_finrank_lt (d : ℕ) (h : Module.finrank R M < d) (x : ⋀[R]^d M) :
    x = 0 := by
  classical
  let _ : LinearOrder (Module.Free.ChooseBasisIndex R M) := linearOrderOfSTO WellOrderingRel
  -- No subset of a basis indexed by fewer than `d` elements has cardinality `d`, so the basis
  -- of `⋀[R]^d M` induced by a basis of `M` is indexed by the empty type.
  have : IsEmpty (Set.powersetCard (Module.Free.ChooseBasisIndex R M) d) := by
    refine ⟨fun s => ?_⟩
    have hs : (s : Finset _).card ≤ Fintype.card (Module.Free.ChooseBasisIndex R M) :=
      Finset.card_le_univ _
    rw [Set.powersetCard.card_eq, ← Module.finrank_eq_card_chooseBasisIndex] at hs
    omega
  refine ((Module.Free.chooseBasis R M).exteriorPower d).repr.injective ?_
  ext i
  exact isEmptyElim i

end exteriorPower
