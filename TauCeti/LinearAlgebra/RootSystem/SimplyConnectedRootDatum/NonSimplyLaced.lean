/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.Reduced
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Assembly

/-!
# Reducedness of the non-simply-laced pinned root data

The pinned simply connected root data of types `B`, `C`, `F₄`, and `G₂` are reduced. For `B`,
`C`, and `F₄`, the proof uses a criterion tailored to crystallographic root data over `ℤ`: if
every Cartan integer has absolute value at most two, then two dependent roots have equal or
opposite signs. Indeed, dependence forces the product of the two Cartan integers to be four, and
the bound leaves only the pairs `(2, 2)` and `(-2, -2)`. Type `G₂` also has Cartan integers of
absolute value three, so its small explicit coordinate table is checked directly instead.

For the classical families, the bound follows uniformly from their signed-coordinate models. For
`F₄`, it is checked against the explicit coordinate table that defines its root datum. These
instances provide the remaining reducedness hypotheses needed to apply
Mathlib's Geck construction to the rational scalar extensions of the pinned data.

## Main results

* `DynkinType.instIsReducedTypeBSimplyConnectedRootDatum` and
  `DynkinType.instIsReducedTypeCSimplyConnectedRootDatum`: reducedness in every rank.
* `DynkinType.instIsReducedF4SimplyConnectedRootDatum` and
  `DynkinType.instIsReducedG2SimplyConnectedRootDatum`: reducedness of the exceptional data.
* `DynkinType.isReduced_simplyConnectedRootDatum_of_not_isSimplyLaced`: the uniform theorem for
  every valid non-simply-laced Dynkin type.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plates II, III, VIII, and IX.
* M. Geck, *On the construction of semisimple Lie algebras and Chevalley groups*.
-/

public section

open Module

namespace RootPairing

variable {M N : Type*} [AddCommGroup M] [Module ℤ M] [Module.IsTorsionFree ℤ M]
  [AddCommGroup N] [Module ℤ N]

/-- A finite integral root pairing is reduced when all its Cartan integers have absolute value at
most two. -/
private theorem isReduced_of_abs_pairing_le_two {i : Type*} [Finite i]
    (P : RootPairing i ℤ M N) (hbound : ∀ a b, |P.pairing a b| ≤ 2) : P.IsReduced := by
  constructor
  intro a b hdependent
  have hproduct : P.pairing a b * P.pairing b a = 4 := by
    simpa only [coxeterWeight] using
      (P.coxeterWeight_eq_four_iff_not_linearIndependent.mpr hdependent)
  obtain ⟨hab_lower, hab_upper⟩ := abs_le.mp (hbound a b)
  obtain ⟨hba_lower, hba_upper⟩ := abs_le.mp (hbound b a)
  have hvalues :
      (P.pairing a b = 2 ∧ P.pairing b a = 2) ∨
        (P.pairing a b = -2 ∧ P.pairing b a = -2) := by
    interval_cases hab : P.pairing a b <;>
      interval_cases hba : P.pairing b a <;> omega
  rcases hvalues with hpos | hneg
  · left
    exact congrArg P.root ((P.pairing_two_two_iff a b).mp hpos)
  · right
    exact (P.pairing_neg_two_neg_two_iff a b).mp hneg

end RootPairing

namespace TauCeti.DynkinType

/-- The pinned simply connected root datum of type `B` is reduced. -/
instance instIsReducedTypeBSimplyConnectedRootDatum (n : ℕ) :
    (typeBSimplyConnectedRootDatum n).IsReduced :=
  RootPairing.isReduced_of_abs_pairing_le_two _
    abs_pairing_typeBSimplyConnectedRootDatum_le_two

/-- The pinned simply connected root datum of type `C` is reduced. -/
instance instIsReducedTypeCSimplyConnectedRootDatum (n : ℕ) :
    (typeCSimplyConnectedRootDatum n).IsReduced :=
  RootPairing.isReduced_of_abs_pairing_le_two _
    abs_pairing_typeCSimplyConnectedRootDatum_le_two

/-- The pinned simply connected root datum of type `F₄` is reduced. -/
instance instIsReducedF4SimplyConnectedRootDatum : f4SimplyConnectedRootDatum.IsReduced :=
  RootPairing.isReduced_of_abs_pairing_le_two _ abs_pairing_f4SimplyConnectedRootDatum_le_two

/-- The pinned simply connected root datum of every valid non-simply-laced Dynkin type is
reduced. -/
theorem isReduced_simplyConnectedRootDatum_of_not_isSimplyLaced (t : DynkinType) (ht : t.Valid)
    (hs : ¬ t.IsSimplyLaced) : (t.simplyConnectedRootDatum ht).IsReduced := by
  cases t with
  | A n => simp at hs
  | B n =>
      rw [simplyConnectedRootDatum_B]
      exact instIsReducedTypeBSimplyConnectedRootDatum n
  | C n =>
      rw [simplyConnectedRootDatum_C]
      exact instIsReducedTypeCSimplyConnectedRootDatum n
  | D n => simp at hs
  | E6 => simp at hs
  | E7 => simp at hs
  | E8 => simp at hs
  | F4 =>
      rw [simplyConnectedRootDatum_F4]
      exact instIsReducedF4SimplyConnectedRootDatum
  | G2 =>
      rw [simplyConnectedRootDatum_G2]
      exact instIsReducedG2SimplyConnectedRootDatum

end TauCeti.DynkinType
