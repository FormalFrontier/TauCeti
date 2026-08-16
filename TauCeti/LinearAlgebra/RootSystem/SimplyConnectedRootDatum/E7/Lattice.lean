/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.E7.Basic
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.E8.Lattice

/-!
# Completeness of the E₇ coroot enumeration

The 126 coroots of type `E₇` are enumerated in
`TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.E7.Basic` as coordinate vectors in the
simple-coroot basis. This file proves that the enumeration is complete: a vector of `Fin 7 → ℤ`
whose `E₇` norm is two is one of the listed coroots.

The proof realizes the `E₇` lattice as the principal seven-node sublattice of the pinned `E₈`
lattice. Extending a coordinate vector by zero preserves its norm, so the existing completeness
theorem `TauCeti.DynkinType.exists_e8Coroot_eq` supplies an `E₈` root. The 63-entry map below checks
that the positive `E₈` roots with zero eighth coordinate are exactly the listed positive `E₇`
roots; the negative halves then agree automatically. This avoids a `126 × 126` reflection table.

## Main result

* `TauCeti.DynkinType.exists_e7Coroot_eq`: every norm-two vector of the `E₇` simple-coroot lattice
  occurs in the pinned enumeration.

## References

The principal-subsystem realization and coordinates follow Bourbaki, *Lie Groups and Lie
Algebras, Chapters 4--6*, Plates VI and VII. The counting argument reuses the formal `E₈` lattice
completeness development in
`TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.E8.Lattice`.
-/

public section

namespace TauCeti

open _root_.Matrix

namespace DynkinType

/-- Extend simple-coroot coordinates from the principal `E₇` subsystem to `E₈`. -/
private def e7Extend (v : Fin 7 → ℤ) : Fin 8 → ℤ :=
  fun i => if hi : (i : ℕ) < 7 then v ⟨i, hi⟩ else 0

/-- The positive `E₈` coroots with zero final coordinate are exactly the positive coroots of
the principal `E₇` subsystem, extended by zero. -/
private theorem e8PositiveCoroot_last_eq_zero_iff (j : Fin 120) :
    e8PositiveCoroot j 7 = 0 ↔
      ∃ i : Fin 63, e8PositiveCoroot j = e7Extend (e7PositiveCoroot i) := by
  fin_cases j <;> decide +kernel +revert

private theorem norm_e7Extend (v : Fin 7 → ℤ) :
    (e7Extend v ᵥ* CartanMatrix.E₈) ⬝ᵥ e7Extend v =
      (v ᵥ* CartanMatrix.E₇) ⬝ᵥ v := by
  simp only [dotProduct, Matrix.vecMul, Fin.sum_univ_succ]
  simp [e7Extend, CartanMatrix.E₈, CartanMatrix.E₇]

private theorem e7Extend_injective : Function.Injective e7Extend := by
  intro v w h
  funext i
  have hi := congrFun h (Fin.castAdd 1 i)
  simpa [e7Extend] using hi

private theorem e7Extend_neg (v : Fin 7 → ℤ) : e7Extend (-v) = -e7Extend v := by
  funext i
  simp only [e7Extend, Pi.neg_apply]
  split <;> simp_all

/-- **The listed `E₇` coroots are all the norm-two vectors of the simple-coroot lattice.** The
enumeration of 126 coroots is complete. -/
theorem exists_e7Coroot_eq {v : Fin 7 → ℤ}
    (hv : (v ᵥ* CartanMatrix.E₇) ⬝ᵥ v = 2) : ∃ k, e7Coroot k = v := by
  obtain ⟨j, hj⟩ := exists_e8Coroot_eq (norm_e7Extend v |>.trans hv)
  have hj0 : e8Coroot j 7 = 0 := by rw [hj]; rfl
  induction j using Fin.addCases (m := 120) (n := 120) with
  | left j =>
      rw [e8Coroot_castAdd] at hj hj0
      obtain ⟨i, hi⟩ := (e8PositiveCoroot_last_eq_zero_iff j).mp hj0
      have hi' : e8PositiveCoroot j = e7Extend (e7PositiveCoroot i) := by
        refine hi.trans ?_
        funext k
        simp only [e7Extend]
      refine ⟨Fin.castAdd 63 i, e7Extend_injective ?_⟩
      have he7 : e7Coroot (Fin.castAdd 63 i) = e7PositiveCoroot i := by
        simp only [e7Coroot_apply, Fin.val_castAdd, i.isLt, dite_true]
      rw [he7]
      exact hi'.symm.trans hj
  | right j =>
      rw [Fin.natAdd_eq_addNat, e8Coroot_addNat] at hj hj0
      have hj0' : e8PositiveCoroot j 7 = 0 := by simpa using hj0
      obtain ⟨i, hi⟩ := (e8PositiveCoroot_last_eq_zero_iff j).mp hj0'
      have hi' : e8PositiveCoroot j = e7Extend (e7PositiveCoroot i) := by
        refine hi.trans ?_
        funext k
        simp only [e7Extend]
      refine ⟨Fin.addNat i 63, e7Extend_injective ?_⟩
      have he7 : e7Coroot (Fin.castAdd 63 i) = e7PositiveCoroot i := by
        simp only [e7Coroot_apply, Fin.val_castAdd, i.isLt, dite_true]
      rw [e7Coroot_addNat, he7, e7Extend_neg, ← hi']
      exact hj

end DynkinType

end TauCeti
