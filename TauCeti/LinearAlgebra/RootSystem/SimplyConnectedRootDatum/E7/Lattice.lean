/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
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

private theorem e7PositiveCoroot_sum_pos (i : Fin 63) :
    0 < ∑ j, e7PositiveCoroot i j := by
  fin_cases i <;> decide

private theorem exists_e8PositiveCoroot_eq_e7Extend (i : Fin 63) :
    ∃ j : Fin 120, e8PositiveCoroot j = e7Extend (e7PositiveCoroot i) := by
  have hnorm :
      (e7PositiveCoroot i ᵥ* CartanMatrix.E₇) ⬝ᵥ e7PositiveCoroot i = 2 := by
    have h := e7Root_dotProduct_coroot (Fin.castAdd 63 i)
    rw [e7Root_apply] at h
    have he7 : e7Coroot (Fin.castAdd 63 i) = e7PositiveCoroot i := by
      simp only [e7Coroot_apply, Fin.val_castAdd, i.isLt, dite_true]
    simpa only [he7] using h
  obtain ⟨j, hj⟩ := exists_e8Coroot_eq (norm_e7Extend (e7PositiveCoroot i) |>.trans hnorm)
  induction j using Fin.addCases (m := 120) (n := 120) with
  | left j =>
      rw [e8Coroot_castAdd] at hj
      exact ⟨j, hj⟩
  | right j =>
      rw [Fin.natAdd_eq_addNat, e8Coroot_addNat] at hj
      have hnonneg : 0 ≤ ∑ k : Fin 7, e8PositiveCoroot j (Fin.castAdd 1 k) :=
        Finset.sum_nonneg fun k _ => e8PositiveCoroot_nonneg j (Fin.castAdd 1 k)
      have hsum := congrArg (fun x : Fin 8 → ℤ => ∑ k : Fin 7, x (Fin.castAdd 1 k)) hj
      simp only [Pi.neg_apply, Finset.sum_neg_distrib] at hsum
      simp [e7Extend] at hsum
      have := e7PositiveCoroot_sum_pos i
      omega

private noncomputable def e7PositiveToE8Index (i : Fin 63) : Fin 120 :=
  Classical.choose (exists_e8PositiveCoroot_eq_e7Extend i)

private theorem e8PositiveCoroot_e7PositiveToE8Index (i : Fin 63) :
    e8PositiveCoroot (e7PositiveToE8Index i) = e7Extend (e7PositiveCoroot i) :=
  Classical.choose_spec (exists_e8PositiveCoroot_eq_e7Extend i)

private theorem e7PositiveCoroot_injective : Function.Injective e7PositiveCoroot := by
  decide

private theorem e7PositiveToE8Index_injective : Function.Injective e7PositiveToE8Index := by
  intro i j hij
  apply e7PositiveCoroot_injective
  apply e7Extend_injective
  rw [← e8PositiveCoroot_e7PositiveToE8Index, ← e8PositiveCoroot_e7PositiveToE8Index, hij]

private def e8PositiveCorootLastZero : Finset (Fin 120) :=
  Finset.univ.filter fun j => e8PositiveCoroot j 7 = 0

private theorem card_e8PositiveCorootLastZero : e8PositiveCorootLastZero.card = 63 :=
  card_filter_e8PositiveCoroot_last_eq_zero

private theorem exists_e7PositiveToE8Index_of_last_eq_zero (j : Fin 120)
    (hj : e8PositiveCoroot j 7 = 0) : ∃ i, e7PositiveToE8Index i = j := by
  let C := Finset.univ.image e7PositiveToE8Index
  have hCT : C ⊆ e8PositiveCorootLastZero := by
    intro k hk
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hk
    rw [e8PositiveCorootLastZero, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by rw [e8PositiveCoroot_e7PositiveToE8Index]; rfl⟩
  have hCcard : C.card = 63 := by
    rw [Finset.card_image_of_injective _ e7PositiveToE8Index_injective,
      Finset.card_univ, Fintype.card_fin]
  have hCTeq : C = e8PositiveCorootLastZero :=
    Finset.eq_of_subset_of_card_le hCT (by rw [hCcard, card_e8PositiveCorootLastZero])
  have : j ∈ C := hCTeq ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩
  simpa [C] using Finset.mem_image.mp this

/-- **The listed `E₇` coroots are all the norm-two vectors of the simple-coroot lattice.** The
enumeration of 126 coroots is complete. -/
theorem exists_e7Coroot_eq {v : Fin 7 → ℤ}
    (hv : (v ᵥ* CartanMatrix.E₇) ⬝ᵥ v = 2) : ∃ k, e7Coroot k = v := by
  obtain ⟨j, hj⟩ := exists_e8Coroot_eq (norm_e7Extend v |>.trans hv)
  have hj0 : e8Coroot j 7 = 0 := by rw [hj]; rfl
  induction j using Fin.addCases (m := 120) (n := 120) with
  | left j =>
      rw [e8Coroot_castAdd] at hj hj0
      obtain ⟨i, rfl⟩ := exists_e7PositiveToE8Index_of_last_eq_zero j hj0
      refine ⟨Fin.castAdd 63 i, e7Extend_injective ?_⟩
      have he7 : e7Coroot (Fin.castAdd 63 i) = e7PositiveCoroot i := by
        simp only [e7Coroot_apply, Fin.val_castAdd, i.isLt, dite_true]
      rw [he7]
      exact (e8PositiveCoroot_e7PositiveToE8Index i).symm.trans hj
  | right j =>
      rw [Fin.natAdd_eq_addNat, e8Coroot_addNat] at hj hj0
      have hj0' : e8PositiveCoroot j 7 = 0 := by simpa using hj0
      obtain ⟨i, rfl⟩ := exists_e7PositiveToE8Index_of_last_eq_zero j hj0'
      refine ⟨Fin.addNat i 63, e7Extend_injective ?_⟩
      have he7 : e7Coroot (Fin.castAdd 63 i) = e7PositiveCoroot i := by
        simp only [e7Coroot_apply, Fin.val_castAdd, i.isLt, dite_true]
      rw [e7Coroot_addNat, he7, e7Extend_neg, ← e8PositiveCoroot_e7PositiveToE8Index]
      exact hj

end DynkinType

end TauCeti
