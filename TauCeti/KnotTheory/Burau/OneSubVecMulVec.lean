/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.Braid
public import TauCeti.LinearAlgebra.Matrix.OneSubVecMulVec

/-!
# Braid-group homomorphisms from the matrices `1 - u ⊗ v`

This file constructs a braid-group homomorphism into `GL` from a family of rank-one perturbations
of the identity `1 - vecMulVec (u i) (v i)`, indexed by the elementary braids, whose pairings have
the values occurring in the Burau representation. The calculus of a single such matrix, or of a
pair of them, is in `TauCeti/LinearAlgebra/Matrix/OneSubVecMulVec.lean`; the braid relation in the
form indexed by adjacent elementary braids is here, since it is the generator adjacency of
`Fin (n - 1)` that it is phrased in.

## Main definitions

* `TauCeti.KnotTheory.braidHomOfOneSubVecMulVec`: the braid-group homomorphism into `GL`
  defined by a family with the Burau pairings.

## Main results

* `TauCeti.KnotTheory.one_sub_vecMulVec_braid_of_adjacent`: the braid relation for two adjacent
  members of such a family.
* `TauCeti.KnotTheory.det_braidHomOfOneSubVecMulVec`: the determinant character of the homomorphism.
-/

public section

open Matrix

namespace TauCeti.KnotTheory

variable {R α : Type*} {n : ℕ} [CommRing R] [Fintype α] [DecidableEq α]

/-- The braid relation for two members of a family of rank-one perturbations of the identity
indexed by adjacent elementary braids, in the symmetric form: the two possible adjacency orders
are covered at once. -/
theorem one_sub_vecMulVec_braid_of_adjacent (t : R) (u v : Fin (n - 1) → α → R)
    (hself : ∀ i, v i ⬝ᵥ u i = t + 1)
    (hforward : ∀ {i j : Fin (n - 1)}, (i : ℕ) + 1 = j → v i ⬝ᵥ u j = -t)
    (hreverse : ∀ {i j : Fin (n - 1)}, (i : ℕ) + 1 = j → v j ⬝ᵥ u i = -1)
    {i j : Fin (n - 1)} (h : (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i) :
    (1 - vecMulVec (u i) (v i)) * (1 - vecMulVec (u j) (v j)) * (1 - vecMulVec (u i) (v i)) =
      (1 - vecMulVec (u j) (v j)) * (1 - vecMulVec (u i) (v i)) * (1 - vecMulVec (u j) (v j)) := by
  rcases h with h | h
  · apply one_sub_vecMulVec_braid
    · rw [hself, hforward h, hreverse h]
      ring
    · rw [hself, hforward h, hreverse h]
      ring
  · apply one_sub_vecMulVec_braid
    · rw [hself, hreverse h, hforward h]
      ring
    · rw [hself, hreverse h, hforward h]
      ring

/-- The braid-group homomorphism into `GL` associated to a family of rank-one perturbations of the
identity with the Burau pairings. -/
def braidHomOfOneSubVecMulVec (n : ℕ) (t : Rˣ) (u v : Fin (n - 1) → α → R)
    (hself : ∀ i, v i ⬝ᵥ u i = (t : R) + 1)
    (hcomm : ∀ {i j : Fin (n - 1)}, (i : ℕ) + 2 ≤ j ∨ (j : ℕ) + 2 ≤ i →
      v i ⬝ᵥ u j = 0)
    (hforward : ∀ {i j : Fin (n - 1)}, (i : ℕ) + 1 = j → v i ⬝ᵥ u j = -(t : R))
    (hreverse : ∀ {i j : Fin (n - 1)}, (i : ℕ) + 1 = j → v j ⬝ᵥ u i = -1) :
    BraidGroup n →* GL α R :=
  BraidGroup.lift (fun i => oneSubVecMulVecGL t (u i) (v i) (hself i))
    (fun h => Units.ext (by
      simp only [Units.val_mul, coe_oneSubVecMulVecGL]
      exact one_sub_vecMulVec_mul_comm (hcomm h) (hcomm h.symm)))
    (fun h => Units.ext (by
      simp only [Units.val_mul, coe_oneSubVecMulVecGL]
      exact one_sub_vecMulVec_braid_of_adjacent (t : R) u v hself hforward hreverse h))

/-- Such a braid-group homomorphism takes an elementary braid to its corresponding unit. -/
@[simp]
theorem braidHomOfOneSubVecMulVec_sigma (n : ℕ) (t : Rˣ) (u v : Fin (n - 1) → α → R)
    (hself : ∀ i, v i ⬝ᵥ u i = (t : R) + 1)
    (hcomm : ∀ {i j : Fin (n - 1)}, (i : ℕ) + 2 ≤ j ∨ (j : ℕ) + 2 ≤ i →
      v i ⬝ᵥ u j = 0)
    (hforward : ∀ {i j : Fin (n - 1)}, (i : ℕ) + 1 = j → v i ⬝ᵥ u j = -(t : R))
    (hreverse : ∀ {i j : Fin (n - 1)}, (i : ℕ) + 1 = j → v j ⬝ᵥ u i = -1)
    (i : Fin (n - 1)) :
    braidHomOfOneSubVecMulVec n t u v hself hcomm hforward hreverse
        (BraidGroup.sigma i) = oneSubVecMulVecGL t (u i) (v i) (hself i) :=
  BraidGroup.lift_sigma _ _ _ i

/-- The determinant character of a braid-group homomorphism by rank-one perturbations of the
identity with the Burau pairings. -/
theorem det_braidHomOfOneSubVecMulVec (n : ℕ) (t : Rˣ) (u v : Fin (n - 1) → α → R)
    (hself : ∀ i, v i ⬝ᵥ u i = (t : R) + 1)
    (hcomm : ∀ {i j : Fin (n - 1)}, (i : ℕ) + 2 ≤ j ∨ (j : ℕ) + 2 ≤ i →
      v i ⬝ᵥ u j = 0)
    (hforward : ∀ {i j : Fin (n - 1)}, (i : ℕ) + 1 = j → v i ⬝ᵥ u j = -(t : R))
    (hreverse : ∀ {i j : Fin (n - 1)}, (i : ℕ) + 1 = j → v j ⬝ᵥ u i = -1)
    (b : BraidGroup n) :
    Matrix.GeneralLinearGroup.det
        (braidHomOfOneSubVecMulVec n t u v hself hcomm hforward hreverse b) =
      (-t) ^ Multiplicative.toAdd (ArtinGroup.exponentSum (CoxeterMatrix.A (n - 1)) b) := by
  have key : (Matrix.GeneralLinearGroup.det (n := α) (R := R)).comp
      (braidHomOfOneSubVecMulVec n t u v hself hcomm hforward hreverse) =
      (zpowersHom Rˣ (-t)).comp (ArtinGroup.exponentSum (CoxeterMatrix.A (n - 1))) := by
    refine BraidGroup.hom_ext fun i => ?_
    apply Units.ext
    simp [det_one_sub_vecMulVec, hself]
  exact congrArg (fun f : BraidGroup n →* Rˣ => f b) key

end TauCeti.KnotTheory
