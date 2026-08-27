/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TensorCoalgebra.Basic

/-!
# Primitive elements of the reduced tensor coalgebra

For an `R`-module `M`, the reduced tensor words `⨁_{n ≥ 1} M^{⊗n}` carry the reduced
deconcatenation coproduct `Δ` built in `TauCeti.ReducedTensorWords.deconcatenation`.  This file
computes its primitive elements: a tensor word killed by deconcatenation is a single letter.

Indeed the `(1, n - 1)` bidegree part of `Δ` on a word of length `n` is the cut after its first
letter, and cutting is injective, so no component of length at least two can survive.

## Main definitions

* `TauCeti.ReducedTensorWords.letter`, `TauCeti.ReducedTensorWords.ofLetter`: the length-one
  component of a tensor word, and a single letter viewed as a tensor word.

## Main results

* `TauCeti.ReducedTensorWords.deconcatenation_eq_zero_iff`: the primitives of the reduced tensor
  coalgebra are exactly the single letters.

## References

* E. Getzler and J. D. S. Jones, *A-infinity algebras and the cyclic bar complex*, Sections 1--2.
* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.1 and 3.6.
-/

public section

open scoped BigOperators DirectSum TensorProduct

universe uR uM

namespace TauCeti

namespace ReducedTensorWords

section Semiring

variable (R : Type uR) (M : Type uM) [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- The letter of a reduced tensor word: its length-one component, read as an element of `M`. -/
noncomputable def letter : ReducedTensorWords R M →ₗ[R] M :=
  (TensorPower.oneEquiv R M).toLinearMap ∘ₗ component R M 1

/-- A single letter, viewed as a reduced tensor word of length one. -/
noncomputable def ofLetter : M →ₗ[R] ReducedTensorWords R M :=
  of R M 1 ∘ₗ (TensorPower.oneEquiv R M).symm.toLinearMap

/-- The length-one component of a single letter is that letter under the tensor-power
identification. -/
theorem component_ofLetter (a : M) :
    component R M 1 (ofLetter R M a) = (TensorPower.oneEquiv R M).symm a := by
  rw [ofLetter, LinearMap.comp_apply, component_of, LinearEquiv.coe_coe]

/-- Every component of a single letter away from length one vanishes. -/
@[simp]
theorem component_ofLetter_of_ne {n : {n : ℕ // 0 < n}} (hn : n ≠ 1) (a : M) :
    component R M n (ofLetter R M a) = 0 := by
  rw [ofLetter, LinearMap.comp_apply, component_of_of_ne R M hn.symm]

/-- The letter of a tensor word is its length-one component, read through the length-one
identification. -/
theorem letter_apply (x : ReducedTensorWords R M) :
    letter R M x = TensorPower.oneEquiv R M (component R M 1 x) :=
  (rfl)

/-- Reading off the letter of a single letter returns it. -/
@[simp]
theorem letter_ofLetter (a : M) : letter R M (ofLetter R M a) = a := by
  rw [letter_apply, ofLetter, LinearMap.comp_apply, component_of, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply]

/-- A single letter has no nontrivial cut. -/
@[simp]
theorem deconcatenation_ofLetter (a : M) : deconcatenation R M (ofLetter R M a) = 0 := by
  rw [ofLetter, LinearMap.comp_apply]
  exact deconcatenation_of_length_one R M _

/-- The `(1, n - 1)` bidegree part of reduced deconcatenation, evaluated on a pure tensor word of
length `m`: only the cut after the first letter can contribute, and it does so exactly when
`m = n`. -/
private theorem map_component_deconcatenation_tprod (n m : {n : ℕ // 0 < n}) (hn : 2 ≤ n.1)
    (x : Fin m.1 → M) :
    TensorProduct.map (component R M 1) (component R M ⟨n.1 - 1, by omega⟩)
        (deconcatenation R M (of R M m (PiTensorProduct.tprod R x))) =
      TensorPower.splitAt R M n.1 1 (by omega)
        (component R M n (of R M m (PiTensorProduct.tprod R x))) := by
  rw [deconcatenation_of, deconcatenationComponent_tprod]
  simp only [map_sum, TensorProduct.map_tmul]
  rcases eq_or_ne m n with rfl | hmn
  · rw [component_of, TensorPower.splitAt_tprod,
      Finset.sum_eq_single (⟨0, by omega⟩ : Fin (m.1 - 1))]
    · simp only [Fin.val_mk, Nat.zero_add]
      erw [component_of, component_of]
    · intro i _ hi
      have hi0 : i.1 ≠ 0 := fun h ↦ hi (Fin.ext h)
      rw [component_of_of_ne R M
        (by simp only [ne_eq, Subtype.ext_iff, Positive.val_one]; omega),
        TensorProduct.zero_tmul]
    · intro hi
      exact absurd (Finset.mem_univ _) hi
  · rw [component_of_of_ne R M hmn, map_zero]
    have hm : 0 < (m : ℕ) := m.2
    have hmn' : (m : ℕ) ≠ (n : ℕ) := fun h ↦ hmn (Subtype.ext h)
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    have hi1 : i.1 + 1 < (m : ℕ) := by have := i.isLt; omega
    rcases eq_or_ne i.1 0 with hi | hi
    · have h2 := component_of_of_ne R M
        (m := (⟨(m : ℕ) - (i.1 + 1), by omega⟩ : {n : ℕ // 0 < n}))
        (n := (⟨(n : ℕ) - 1, by omega⟩ : {n : ℕ // 0 < n}))
        (by simp only [ne_eq, Subtype.mk.injEq]; omega)
      rw [h2, TensorProduct.tmul_zero]
    · have h1 := component_of_of_ne R M
        (m := (⟨i.1 + 1, by omega⟩ : {n : ℕ // 0 < n})) (n := 1)
        (by simp only [ne_eq, Subtype.ext_iff, Positive.val_one]; omega)
      rw [h1, TensorProduct.zero_tmul]

/-- Reading off the `(1, n - 1)` bidegree part of reduced deconcatenation recovers the cut of a
word of length `n` after its first letter. -/
theorem map_component_deconcatenation (n : {n : ℕ // 0 < n}) (hn : 2 ≤ n.1) :
    TensorProduct.map (component R M 1) (component R M ⟨n.1 - 1, by omega⟩) ∘ₗ
        deconcatenation R M =
      TensorPower.splitAt R M n.1 1 (by omega) ∘ₗ component R M n := by
  refine linearMap_ext R M fun m x ↦ ?_
  simp only [LinearMap.comp_apply]
  exact map_component_deconcatenation_tprod R M n m hn x

/-- A reduced tensor word is determined by its deconcatenation together with its letter: the
components of length at least two are read off from the cut after the first letter, and the
length-one component is the letter. -/
theorem eq_of_deconcatenation_eq_of_letter_eq {x y : ReducedTensorWords R M}
    (hd : deconcatenation R M x = deconcatenation R M y) (hl : letter R M x = letter R M y) :
    x = y := by
  apply DirectSum.ext_component R
  intro n
  rw [← DirectSum.apply_eq_component R x n, ← DirectSum.apply_eq_component R y n]
  rw [apply_eq_component R M x n, apply_eq_component R M y n]
  rcases eq_or_ne n 1 with rfl | hn
  · have h := congrArg (TensorPower.oneEquiv R M).symm hl
    rwa [letter_apply, letter_apply, LinearEquiv.symm_apply_apply,
      LinearEquiv.symm_apply_apply] at h
  · have h2 : 2 ≤ n.1 := by
      have h1 := n.2
      rcases Nat.lt_or_ge n.1 2 with h | h
      · exact absurd (Subtype.ext (by omega : n.1 = 1)) hn
      · exact h
    refine TensorPower.splitAt_injective R M n.1 1 (by omega) ?_
    have hx := congrArg (fun f ↦ f x) (map_component_deconcatenation R M n h2)
    have hy := congrArg (fun f ↦ f y) (map_component_deconcatenation R M n h2)
    simp only [LinearMap.comp_apply] at hx hy
    rw [← hx, ← hy, hd]

/-- The primitive elements of the reduced tensor coalgebra are exactly the single letters. -/
theorem deconcatenation_eq_zero_iff {x : ReducedTensorWords R M} :
    deconcatenation R M x = 0 ↔ x ∈ LinearMap.range (ofLetter R M) := by
  refine ⟨fun hx ↦ ⟨letter R M x, ?_⟩, ?_⟩
  · refine (eq_of_deconcatenation_eq_of_letter_eq R M ?_ ?_).symm
    · rw [deconcatenation_ofLetter, hx]
    · rw [letter_ofLetter]
  · rintro ⟨a, rfl⟩
    exact deconcatenation_ofLetter R M a

end Semiring

end ReducedTensorWords

end TauCeti
