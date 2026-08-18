/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.Reduced

/-!
# A symmetry criterion for reduced root pairings

A finite root pairing over a characteristic-zero domain is reduced as soon as its pairing is
symmetric on roots and coroots. Indeed, two linearly dependent roots have Coxeter weight four.
Symmetry makes this weight the square of one pairing value, so that value is `2` or `-2`; the
root-pairing axioms then identify the two roots up to sign.

This criterion is useful for root data presented in dual coordinate bases. Their roots and
coroots need not be equal as coordinate vectors, while the pairing can still visibly be the
symmetric form of a simply-laced Cartan matrix.

## Main result

* `RootPairing.isReduced_of_pairing_comm`: a finite root pairing with symmetric pairings is
  reduced.
-/

public section

open Module

namespace RootPairing

variable {ι R M N : Type*} [CommRing R] [CharZero R] [IsDomain R]
  [AddCommGroup M] [Module R M] [Module.IsTorsionFree R M]
  [AddCommGroup N] [Module R N] (P : RootPairing ι R M N)

/-- A finite root pairing whose root--coroot pairing is symmetric is reduced. -/
theorem isReduced_of_pairing_comm [Finite ι]
    (hcomm : ∀ i j, P.pairing i j = P.pairing j i) : P.IsReduced := by
  constructor
  intro i j hdependent
  have hweight : P.coxeterWeight i j = 4 :=
    (P.coxeterWeight_eq_four_iff_not_linearIndependent).2 hdependent
  have hsquare : P.pairing i j * P.pairing i j = 4 := by
    simpa only [coxeterWeight, hcomm i j] using hweight
  have hfactor : (P.pairing i j - 2) * (P.pairing i j + 2) = 0 := by
    calc
      (P.pairing i j - 2) * (P.pairing i j + 2) =
          P.pairing i j * P.pairing i j - 4 := by ring
      _ = 0 := by rw [hsquare, sub_self]
  rcases mul_eq_zero.mp hfactor with htwo | hnegTwo
  · left
    have hij : P.pairing i j = 2 := sub_eq_zero.mp htwo
    have hji : P.pairing j i = 2 := (hcomm i j).symm.trans hij
    exact congrArg P.root ((P.pairing_two_two_iff i j).mp ⟨hij, hji⟩)
  · right
    have hij : P.pairing i j = -2 := eq_neg_of_add_eq_zero_left hnegTwo
    have hji : P.pairing j i = -2 := (hcomm i j).symm.trans hij
    exact (P.pairing_neg_two_neg_two_iff i j).mp ⟨hij, hji⟩

end RootPairing
