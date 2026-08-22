/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `TauCeti.frobeniusFixedSubring`, its membership criterion and its behaviour under divisibility
-- of the exponent; this module also supplies Mathlib's `iterateFrobenius`.
public import TauCeti.Algebra.CharP.FrobeniusFixed
-- `TauCeti.fixedSubgroup` and `TauCeti.fixedSubgroup_eq_top_iff`.
public import TauCeti.GroupTheory.FixedSubgroup
-- The `GL` notation, `Matrix.GeneralLinearGroup.map` and its entrywise description.
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Invertible matrices fixed by the entrywise Frobenius

Let `A` be a commutative ring of exponential characteristic `p`. Raising every entry to the
`p ^ k`-th power is a group endomorphism `Matrix.GeneralLinearGroup.map (iterateFrobenius A p k)`
of `GL ι A`, and this file describes its fixed points: an invertible matrix is fixed exactly when
all of its entries lie in `TauCeti.frobeniusFixedSubring A p k`. In the motivating case, `p` prime,
`0 < k`, `A` an algebraic closure of `ZMod p` and `q = p ^ k`, the fixed subgroup is `GLₙ(𝔽_q)`
inside `GLₙ(A)`, and the divisibility statement below is the inclusion
`GLₙ(𝔽_{p ^ m}) ⊆ GLₙ(𝔽_{p ^ l})`.

Nothing here needs `A` to be a field, algebraically closed, or finite, and no coordinate ring or
Hopf-algebra theory is involved; the group-scheme reading of these statements is
`TauCeti/Algebra/AlgebraicGroup/Frobenius/GeneralLinear.lean`.

## Main results

* `Matrix.GeneralLinearGroup.map_iterateFrobenius_eq_self_iff`: an invertible matrix is
  fixed by the entrywise Frobenius exactly when all of its entries are.
* `Matrix.GeneralLinearGroup.fixedSubgroup_map_iterateFrobenius_zero`: the zeroth iterate
  fixes everything.
* `Matrix.GeneralLinearGroup.fixedSubgroup_map_iterateFrobenius_le_of_dvd`: the fixed
  subgroups grow along divisibility of the exponent.

## References

These are the matrix-coordinate form of the Frobenius-fixed points used to construct the finite
groups of Lie type; see R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex
Characters*, §1.17.
-/

public section

open TauCeti

namespace Matrix.GeneralLinearGroup

variable {ι : Type*} [DecidableEq ι] [Fintype ι]
variable (p : ℕ) {A : Type*} [CommRing A] [ExpChar A p]

/-- An invertible matrix is fixed by the entrywise `p ^ k`-power Frobenius exactly when every one
of its entries lies in the Frobenius-fixed subring.

Stated as the equation `Matrix.GeneralLinearGroup.map (iterateFrobenius A p k) g = g` rather than
as membership in `TauCeti.fixedSubgroup`, because `TauCeti.mem_fixedSubgroup` is a `simp` lemma
that rewrites such a membership to this equation; this is the form `simp` reaches, matching
`TauCeti.Bialgebra.iterateFrobeniusPoints_eq_self_iff`. -/
@[simp]
theorem map_iterateFrobenius_eq_self_iff (k : ℕ) (g : Matrix.GeneralLinearGroup ι A) :
    Matrix.GeneralLinearGroup.map (iterateFrobenius A p k) g = g ↔
      ∀ i j, (g : Matrix ι ι A) i j ∈ frobeniusFixedSubring A p k := by
  constructor
  · intro hg i j
    rw [mem_frobeniusFixedSubring, ← iterateFrobenius_def,
      ← Matrix.GeneralLinearGroup.map_apply, hg]
  · intro hg
    refine Matrix.GeneralLinearGroup.ext fun i j => ?_
    rw [Matrix.GeneralLinearGroup.map_apply, iterateFrobenius_def]
    exact mem_frobeniusFixedSubring.mp (hg i j)

/-- The zeroth Frobenius iterate fixes every invertible matrix.

Deliberately not `@[simp]`: `iterateFrobenius_zero` already rewrites the ring homomorphism to the
identity, after which `Matrix.GeneralLinearGroup.map_id` and `TauCeti.fixedSubgroup_eq_top_iff`
close the goal, so a `simp` attribute here would be redundant. -/
theorem fixedSubgroup_map_iterateFrobenius_zero :
    fixedSubgroup (Matrix.GeneralLinearGroup.map (n := ι) (iterateFrobenius A p 0)) = ⊤ := by
  rw [iterateFrobenius_zero, Matrix.GeneralLinearGroup.map_id]
  exact fixedSubgroup_eq_top_iff.mpr rfl

/-- The subgroups of entrywise Frobenius-fixed matrices grow along divisibility of the exponent.
In the motivating case this is the inclusion `GLₙ(𝔽_{p ^ m}) ⊆ GLₙ(𝔽_{p ^ l})`. -/
theorem fixedSubgroup_map_iterateFrobenius_le_of_dvd {m l : ℕ} (hml : m ∣ l) :
    fixedSubgroup (Matrix.GeneralLinearGroup.map (n := ι) (iterateFrobenius A p m)) ≤
      fixedSubgroup (Matrix.GeneralLinearGroup.map (n := ι) (iterateFrobenius A p l)) :=
  fun g hg =>
  mem_fixedSubgroup.mpr ((map_iterateFrobenius_eq_self_iff p l g).mpr fun i j =>
    frobeniusFixedSubring_le_of_dvd hml
      ((map_iterateFrobenius_eq_self_iff p m g).mp (mem_fixedSubgroup.mp hg) i j))

end Matrix.GeneralLinearGroup
