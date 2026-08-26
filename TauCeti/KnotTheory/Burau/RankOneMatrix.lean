/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.Braid
public import TauCeti.LinearAlgebra.Matrix.RankOne

/-!
# Braid-group representations from rank-one matrix families

This file constructs a braid-group representation from a rank-one matrix family whose pairings
have the values occurring in the Burau representation. The braid-independent matrix calculus is in
`TauCeti/LinearAlgebra/Matrix/RankOne.lean`.

## Main definitions

* `TauCeti.RankOneMatrix.representation`: the braid-group representation defined by a family with
  the Burau pairings.

## Main results

* `TauCeti.RankOneMatrix.det_representation`: the determinant character of the representation.
-/

public section

open Matrix

namespace TauCeti

variable {R : Type*} {n : ℕ}

namespace RankOneMatrix

variable {α : Type*}

section CommRing

variable [CommRing R] [Fintype α] [DecidableEq α]

/-- The braid-group representation associated to a rank-one matrix family with the Burau
pairings. -/
def representation (n : ℕ) (t : Rˣ) (u v : Fin (n - 1) → α → R)
    (hself : ∀ i, v i ⬝ᵥ u i = (t : R) + 1)
    (hcomm : ∀ {i j : Fin (n - 1)}, (i : ℕ) + 2 ≤ j ∨ (j : ℕ) + 2 ≤ i →
      v i ⬝ᵥ u j = 0)
    (hforward : ∀ {i j : Fin (n - 1)}, (i : ℕ) + 1 = j → v i ⬝ᵥ u j = -(t : R))
    (hreverse : ∀ {i j : Fin (n - 1)}, (i : ℕ) + 1 = j → v j ⬝ᵥ u i = -1) :
    BraidGroup n →* GL α R :=
  BraidGroup.lift (unit t u v hself)
    (fun h => Units.ext (by
      simp only [Units.val_mul, coe_unit]
      exact family_mul_comm u v (hcomm h) (hcomm h.symm)))
    (fun h => Units.ext (by
      simp only [Units.val_mul, coe_unit]
      exact family_braid_of_adjacent (t : R) u v hself hforward hreverse h))

/-- A rank-one braid-group representation takes an elementary braid to its corresponding unit. -/
@[simp]
theorem representation_sigma (n : ℕ) (t : Rˣ) (u v : Fin (n - 1) → α → R)
    (hself : ∀ i, v i ⬝ᵥ u i = (t : R) + 1)
    (hcomm : ∀ {i j : Fin (n - 1)}, (i : ℕ) + 2 ≤ j ∨ (j : ℕ) + 2 ≤ i →
      v i ⬝ᵥ u j = 0)
    (hforward : ∀ {i j : Fin (n - 1)}, (i : ℕ) + 1 = j → v i ⬝ᵥ u j = -(t : R))
    (hreverse : ∀ {i j : Fin (n - 1)}, (i : ℕ) + 1 = j → v j ⬝ᵥ u i = -1)
    (i : Fin (n - 1)) :
    representation n t u v hself hcomm hforward hreverse (BraidGroup.sigma i) =
      unit t u v hself i :=
  BraidGroup.lift_sigma _ _ _ i

/-- The determinant character of a rank-one braid-group representation with the Burau
pairings. -/
theorem det_representation (n : ℕ) (t : Rˣ) (u v : Fin (n - 1) → α → R)
    (hself : ∀ i, v i ⬝ᵥ u i = (t : R) + 1)
    (hcomm : ∀ {i j : Fin (n - 1)}, (i : ℕ) + 2 ≤ j ∨ (j : ℕ) + 2 ≤ i →
      v i ⬝ᵥ u j = 0)
    (hforward : ∀ {i j : Fin (n - 1)}, (i : ℕ) + 1 = j → v i ⬝ᵥ u j = -(t : R))
    (hreverse : ∀ {i j : Fin (n - 1)}, (i : ℕ) + 1 = j → v j ⬝ᵥ u i = -1)
    (b : BraidGroup n) :
    Matrix.GeneralLinearGroup.det (representation n t u v hself hcomm hforward hreverse b) =
      (-t) ^ Multiplicative.toAdd (ArtinGroup.exponentSum (CoxeterMatrix.A (n - 1)) b) := by
  have key : (Matrix.GeneralLinearGroup.det (n := α) (R := R)).comp
      (representation n t u v hself hcomm hforward hreverse) =
      (zpowersHom Rˣ (-t)).comp (ArtinGroup.exponentSum (CoxeterMatrix.A (n - 1))) := by
    refine BraidGroup.hom_ext fun i => ?_
    apply Units.ext
    simp [det_family, hself]
  exact congrArg (fun f : BraidGroup n →* Rˣ => f b) key

end CommRing

end RankOneMatrix

end TauCeti
