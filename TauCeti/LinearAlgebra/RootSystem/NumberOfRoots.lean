/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.DynkinType

public section

/-!
# Numbers of roots of Dynkin types

This file records the number of roots in each irreducible crystallographic Dynkin type. The value
`TauCeti.DynkinType.numRoots` fixes `Fin t.numRoots` as the root-index type intended for the
pinned simply connected root datum, which is not constructed here: unlike an abstract finite index
type, this makes that index type explicit for every family.

The classical formulas are `n(n+1)` for `Aₙ`, `2n²` for `Bₙ` and `Cₙ`, and `2n(n-1)` for `Dₙ`.
The exceptional types have respectively `72`, `126`, `240`, `48`, and `12` roots. For a valid
Dynkin type, `TauCeti.DynkinType.rank_le_numRoots` ensures that the simple roots can occupy the
first `t.rank` indices of `Fin t.numRoots`, as that future datum will require.

## Main definitions

* `TauCeti.DynkinType.numRoots`: the number of roots of a Dynkin type.

## Main results

* `TauCeti.DynkinType.rank_le_numRoots`: a valid type has at least as many roots as simple roots.
* `TauCeti.DynkinType.numRoots_pos`: a valid type has a positive number of roots.

## References

This is the `DynkinType.numRoots` target of Layer 6 of
`TauCetiRoadmap/RepresentationTheory/RootSystems/README.md`. The formulas follow N. Bourbaki,
*Lie Groups and Lie Algebras, Chapters 4--6*, plates I--IX, and J. E. Humphreys,
*Introduction to Lie Algebras and Representation Theory*, Chapter 11.
-/

namespace TauCeti.DynkinType

/-- The number of roots of a Dynkin type. This is exposed because it is meant to appear in the
root-index type `Fin t.numRoots` of the future pinned simply connected root datum, whose
construction must reduce to the explicit family data rather than an abstract finite type. -/
@[expose] def numRoots : DynkinType → ℕ
  | .A n => n * (n + 1)
  | .B n | .C n => 2 * n ^ 2
  | .D n => 2 * n * (n - 1)
  | .E6 => 72
  | .E7 => 126
  | .E8 => 240
  | .F4 => 48
  | .G2 => 12

@[simp] lemma numRoots_A (n : ℕ) : (A n).numRoots = n * (n + 1) := rfl
@[simp] lemma numRoots_B (n : ℕ) : (B n).numRoots = 2 * n ^ 2 := rfl
@[simp] lemma numRoots_C (n : ℕ) : (C n).numRoots = 2 * n ^ 2 := rfl
@[simp] lemma numRoots_D (n : ℕ) : (D n).numRoots = 2 * n * (n - 1) := rfl
@[simp] lemma numRoots_E6 : E6.numRoots = 72 := rfl
@[simp] lemma numRoots_E7 : E7.numRoots = 126 := rfl
@[simp] lemma numRoots_E8 : E8.numRoots = 240 := rfl
@[simp] lemma numRoots_F4 : F4.numRoots = 48 := rfl
@[simp] lemma numRoots_G2 : G2.numRoots = 12 := rfl

/-- A valid Dynkin type has at least as many roots as simple roots. This is the bound needed to
regard the Bourbaki-numbered simple nodes as the first indices of `Fin t.numRoots`. -/
lemma rank_le_numRoots {t : DynkinType} (ht : t.Valid) : t.rank ≤ t.numRoots := by
  cases t with
  | A n => simp_all; nlinarith
  | B n => simp_all; nlinarith
  | C n => simp_all; nlinarith
  | D n =>
      have hvalid : 4 ≤ n := valid_D.mp ht
      have hn : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
      simp only [rank_D, numRoots_D]
      nlinarith [Nat.zero_le (n - 1)]
  | E6 | E7 | E8 | F4 | G2 => norm_num

/-- A valid Dynkin type has at least one root. -/
lemma numRoots_pos {t : DynkinType} (ht : t.Valid) : 0 < t.numRoots :=
  lt_of_lt_of_le (rank_pos ht) (rank_le_numRoots ht)

end TauCeti.DynkinType
