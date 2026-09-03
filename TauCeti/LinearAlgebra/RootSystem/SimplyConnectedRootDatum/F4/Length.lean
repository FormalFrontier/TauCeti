/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.RootLength
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.F4.Basic

/-!
# Squared lengths of the pinned `F₄` roots

`TauCeti.DynkinType.f4SimplyConnectedRootDatum` tabulates its forty-eight roots in the
fundamental-weight basis and its forty-eight coroots in the simple-coroot basis. Neither table
displays how long a root is, and a consumer that has to distinguish long roots from short ones
needs that: a characteristic-two special isogeny of type `F₄` attaches one field exponent to the
long root subgroups and another to the short ones.

This file supplies the missing table. `TauCeti.DynkinType.f4Length` is normalised as
`TauCeti.DynkinType.rootLength` normalises the simple roots, so it is `1` on the twenty-four short
roots and `2` on the twenty-four long ones. Mathlib's
`RootPairing.RootPositiveForm.rootLength` is not that table: it is the value of a chosen invariant
form, so it carries whatever scale that form has, whereas the exponent convention of a special
isogeny is stated against the normalisation in which a shortest root has length `1`.

The normalisation is not a stipulation. Because the invariant form is symmetric,
`ℓ(α) ⟨β, α∨⟩ = 2 (β, α) = 2 (α, β) = ℓ(β) ⟨α, β∨⟩` for every pair of roots, and
`TauCeti.DynkinType.f4Length_mul_pairing_comm` records exactly that identity for the tabulated
values. Together with the value on the four simple roots those equations pin the whole table,
which is `TauCeti.DynkinType.eq_f4Length_of_mul_pairing`.

## Main definitions

* `TauCeti.DynkinType.f4Length`: the squared length of each of the forty-eight pinned roots.

## Main results

* `TauCeti.DynkinType.f4Length_mul_pairing_comm` and
  `TauCeti.DynkinType.eq_f4Length_of_mul_pairing`: the table symmetrises the Cartan integers, and
  it is the only table doing so with the prescribed values on the simple roots.
* `TauCeti.DynkinType.f4Length_castAdd`: on the four simple roots it is
  `TauCeti.DynkinType.rootLength`.
* `TauCeti.DynkinType.isLongSimpleRoot_iff_f4Length_eq_two` and
  `TauCeti.DynkinType.f4Length_castAdd_eq_one_iff`: the two long simple roots are the ones of
  length two and the two short ones the ones of length one.

## References

The coordinates and the node numbering follow Bourbaki, *Lie Groups and Lie Algebras, Chapters
4--6*, Plate VIII. The table is the type `F₄` input asked for by the "special isogenies in
characteristics two and three" bullet of Layer 9 of `TauCetiRoadmap/ReductiveGroups/README.md`,
matching the rank-two type `B` table of
`TauCeti/LinearAlgebra/RootSystem/SimplyConnectedRootDatum/B/RankTwo.lean`.
-/

public section

namespace TauCeti.DynkinType

open scoped _root_.Matrix

/-- The squared lengths of the forty-eight roots of the pinned `F₄` datum, in the index order of
`TauCeti.DynkinType.f4Root` and normalised as `TauCeti.DynkinType.rootLength` normalises the
simple ones: `1` on a short root and `2` on a long one. -/
def f4Length : Fin 48 → ℤ :=
  ![2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1,
    1, 2, 1, 2, 2, 1, 2, 1, 1, 2, 2, 2,
    2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1,
    1, 2, 1, 2, 2, 1, 2, 1, 1, 2, 2, 2]

/-- The explicit squared lengths of the roots in the pinned `F₄` table. -/
theorem f4Length_def :
    f4Length =
      ![2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1,
        1, 2, 1, 2, 2, 1, 2, 1, 1, 2, 2, 2,
        2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1,
        1, 2, 1, 2, 2, 1, 2, 1, 1, 2, 2, 2] := (rfl)

/-- On the four simple roots the length table is `TauCeti.DynkinType.rootLength`: the first two
Bourbaki nodes of `F₄` are long and the last two are short. -/
@[simp] theorem f4Length_castAdd (i : Fin 4) :
    f4Length (Fin.castAdd 44 i) = F4.rootLength i := by
  rw [rootLength_F4]
  decide +revert

/-- A root and its negative have the same squared length. -/
@[simp] theorem f4Length_add_twentyFour (i : Fin 48) : f4Length (i + 24) = f4Length i := by
  decide +revert

/-- Every root of the pinned `F₄` datum is short or long, of squared length `1` or `2`. -/
theorem f4Length_eq_one_or_eq_two (i : Fin 48) : f4Length i = 1 ∨ f4Length i = 2 := by
  decide +revert

/-- Every root of the pinned `F₄` datum has positive squared length. -/
theorem f4Length_pos (i : Fin 48) : 0 < f4Length i := by
  decide +revert

private theorem f4Length_mul_dotProduct (i j : Fin 48) :
    f4Length i * (f4Root j ⬝ᵥ f4Coroot i) = f4Length j * (f4Root i ⬝ᵥ f4Coroot j) := by
  decide +revert

/-- **The length table symmetrises the Cartan integers.** Expanding `α∨ = 2 α / (α, α)` on both
sides, the identity `ℓ(α) ⟨β, α∨⟩ = ℓ(β) ⟨α, β∨⟩` is the symmetry of the invariant form. -/
theorem f4Length_mul_pairing_comm (i j : Fin 48) :
    f4Length i * f4SimplyConnectedRootDatum.pairing j i =
      f4Length j * f4SimplyConnectedRootDatum.pairing i j := by
  simp only [f4SimplyConnectedRootDatum_pairing]
  exact f4Length_mul_dotProduct i j

private theorem f4_exists_pairing_castAdd_ne_zero (k : Fin 48) :
    ∃ i : Fin 4, f4Root (Fin.castAdd 44 i) ⬝ᵥ f4Coroot k ≠ 0 := by
  decide +revert

/-- **The symmetry equations against the simple roots determine the length table.** No root is
orthogonal to every simple root, so the value at an arbitrary index is forced by the four
values `TauCeti.DynkinType.f4Length_castAdd` prescribes. -/
theorem eq_f4Length_of_mul_pairing {k : Fin 48} {c : ℤ}
    (h : ∀ i : Fin 4, c * f4SimplyConnectedRootDatum.pairing (Fin.castAdd 44 i) k =
      F4.rootLength i * f4SimplyConnectedRootDatum.pairing k (Fin.castAdd 44 i)) :
    c = f4Length k := by
  obtain ⟨i, hi⟩ := f4_exists_pairing_castAdd_ne_zero k
  rw [← f4SimplyConnectedRootDatum_pairing] at hi
  refine mul_right_cancel₀ hi ((h i).trans ?_)
  rw [← f4Length_castAdd i]
  exact (f4Length_mul_pairing_comm k (Fin.castAdd 44 i)).symm

/-- **A simple root of the pinned `F₄` datum is long exactly when its squared length is two**,
which is the convention `TauCeti.DynkinType.rootLength` fixes and the one a length-exchanging map
is pinned against. -/
theorem isLongSimpleRoot_iff_f4Length_eq_two (i : Fin 4) :
    F4.IsLongSimpleRoot i ↔ f4Length (Fin.castAdd 44 i) = 2 := by
  rw [f4Length_castAdd, rootLength_F4, isLongSimpleRoot_F4]
  fin_cases i <;> norm_num

/-- **A simple root of the pinned `F₄` datum is short exactly when its squared length is one.**
This is the form in which a characteristic-two special isogeny states which of its two rescaling
exponents it attaches to which node. -/
theorem f4Length_castAdd_eq_one_iff (i : Fin 4) :
    f4Length (Fin.castAdd 44 i) = 1 ↔ ¬ F4.IsLongSimpleRoot i := by
  rw [isLongSimpleRoot_iff_f4Length_eq_two]
  rcases f4Length_eq_one_or_eq_two (Fin.castAdd 44 i) with h | h <;> rw [h] <;> norm_num

end TauCeti.DynkinType
