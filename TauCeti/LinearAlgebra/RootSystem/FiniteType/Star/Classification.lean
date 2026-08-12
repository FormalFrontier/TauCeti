/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Star.Basic
import TauCeti.LinearAlgebra.RootSystem.FiniteType.Classical
import TauCeti.LinearAlgebra.RootSystem.FiniteType.Dynkin

public section

/-!
# Classification of finite three-arm stars

The fork bound in `TauCeti.LinearAlgebra.RootSystem.FiniteType.Star.Basic` restricts an ordered
three-arm star of finite type to the shapes underlying `A`, `D`, `E₆`, `E₇`, and `E₈`.
This file identifies each surviving model star with its standard Cartan matrix and proves the
converse, completing the classification of the model stars themselves.

This is the simply-laced fork assembly step in Layer 5 of the root-systems roadmap. Extracting such
a star from an arbitrary connected finite-type diagram remains part of the assembly of the full
Cartan--Killing classification.

## References

The classification follows N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Chapter VI,
§4, and J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §11.4.
-/

open scoped Matrix

namespace TauCeti

/-! ## Chains -/

private def starAEmbedding (b c : ℕ) : StarIndex ![0, b, c] → Fin (b + c + 1)
  | none => ⟨b, by omega⟩
  | some ⟨i, s⟩ =>
      ⟨if i.val = 1 then b - 1 - s else if i.val = 2 then b + 1 + s else 0, by
        fin_cases i
        · exact Fin.elim0 s
        · simp at s ⊢; omega
        · simp at s ⊢; omega⟩

private theorem starAEmbedding_injective (b c : ℕ) : Function.Injective (starAEmbedding b c) := by
  intro v w h
  rcases v with _ | ⟨i, s⟩ <;> rcases w with _ | ⟨j, t⟩
  · rfl
  · fin_cases j
    · exact Fin.elim0 t
    · simp [starAEmbedding] at h
      omega
    · simp [starAEmbedding] at h
      omega
  · fin_cases i
    · exact Fin.elim0 s
    · simp [starAEmbedding] at h
      omega
    · simp [starAEmbedding] at h
      omega
  · fin_cases i <;> fin_cases j <;>
      simp [starAEmbedding] at h s t ⊢ <;> try omega
    all_goals try exact Fin.elim0 s
    all_goals try exact Fin.elim0 t
    all_goals congr 1
    all_goals exact Fin.ext (by omega)

private theorem starCartanMatrix_zero_eq_A (b c : ℕ) :
    starCartanMatrix ![0, b, c] =
      (CartanMatrix.A (b + c + 1)).submatrix (starAEmbedding b c) (starAEmbedding b c) := by
  ext v w
  rcases v with _ | ⟨i, s⟩ <;> rcases w with _ | ⟨j, t⟩
  · simp [Matrix.submatrix_apply, starAEmbedding, CartanMatrix.A]
  · fin_cases j <;> simp [Matrix.submatrix_apply, starAEmbedding, CartanMatrix.A] at t ⊢ <;>
      try split_ifs <;> try omega
  · fin_cases i <;> simp [Matrix.submatrix_apply, starAEmbedding, CartanMatrix.A] at s ⊢ <;>
      try split_ifs <;> try omega
  · fin_cases i
    · exact Fin.elim0 s
    · fin_cases j
      · exact Fin.elim0 t
      · simp [Matrix.submatrix_apply, starAEmbedding, CartanMatrix.A] at s t ⊢
        all_goals split_ifs
        all_goals omega
      · simp [Matrix.submatrix_apply, starAEmbedding, CartanMatrix.A] at s t ⊢
        all_goals split_ifs
        all_goals omega
    · fin_cases j
      · exact Fin.elim0 t
      · simp [Matrix.submatrix_apply, starAEmbedding, CartanMatrix.A] at s t ⊢
        all_goals split_ifs
        all_goals omega
      · simp [Matrix.submatrix_apply, starAEmbedding, CartanMatrix.A] at s t ⊢
        all_goals split_ifs
        all_goals omega

private theorem isFiniteType_starCartanMatrix_zero (b c : ℕ) :
    IsFiniteType (starCartanMatrix ![0, b, c]) := by
  rw [starCartanMatrix_zero_eq_A]
  exact (isFiniteType_cartanMatrix_A _).submatrix (starAEmbedding_injective b c)

/-! ## Forks -/

private def starDEmbedding (c : ℕ) : StarIndex ![1, 1, c] → Fin (c + 3)
  | none => ⟨c, by omega⟩
  | some ⟨i, s⟩ =>
      ⟨if i.val = 0 then c + 1 else if i.val = 1 then c + 2 else c - 1 - s, by
        fin_cases i <;> simp at s ⊢
        all_goals omega⟩

private theorem starDEmbedding_injective (c : ℕ) : Function.Injective (starDEmbedding c) := by
  intro v w h
  rcases v with _ | ⟨i, s⟩ <;> rcases w with _ | ⟨j, t⟩
  · rfl
  · fin_cases j <;> simp [starDEmbedding] at h t
    all_goals omega
  · fin_cases i <;> simp [starDEmbedding] at h s
    all_goals omega
  · fin_cases i <;> fin_cases j <;>
      simp [starDEmbedding] at h s t ⊢ <;> try omega
    all_goals congr 1
    all_goals exact Fin.ext (by omega)

private theorem starCartanMatrix_one_one_eq_D (c : ℕ) :
    starCartanMatrix ![1, 1, c] =
      (CartanMatrix.D (c + 3)).submatrix (starDEmbedding c) (starDEmbedding c) := by
  ext v w
  rcases v with _ | ⟨i, s⟩ <;> rcases w with _ | ⟨j, t⟩
  · simp [Matrix.submatrix_apply, starDEmbedding, CartanMatrix.D]
  · fin_cases j <;> simp [Matrix.submatrix_apply, starDEmbedding, CartanMatrix.D] at t ⊢
    all_goals split_ifs
    all_goals omega
  · fin_cases i <;> simp [Matrix.submatrix_apply, starDEmbedding, CartanMatrix.D] at s ⊢
    all_goals split_ifs
    all_goals omega
  · fin_cases i <;> fin_cases j <;>
      simp [Matrix.submatrix_apply, starDEmbedding, CartanMatrix.D] at s t ⊢ <;>
      split_ifs <;> omega

private theorem isFiniteType_starCartanMatrix_one_one (c : ℕ) :
    IsFiniteType (starCartanMatrix ![1, 1, c]) := by
  rw [starCartanMatrix_one_one_eq_D]
  exact (isFiniteType_cartanMatrix_D _).submatrix (starDEmbedding_injective c)

/-! ## Exceptional forks -/

private def starEEmbedding (c : ℕ) : StarIndex ![1, 2, c] → Fin (c + 4)
  | none => ⟨3, by omega⟩
  | some ⟨i, s⟩ =>
      ⟨if i.val = 0 then 1 else if i.val = 1 then 2 - 2 * s else 4 + s, by
        fin_cases i <;> simp at s ⊢
        all_goals omega⟩

private theorem starEEmbedding_injective (c : ℕ) : Function.Injective (starEEmbedding c) := by
  intro v w h
  rcases v with _ | ⟨i, s⟩ <;> rcases w with _ | ⟨j, t⟩
  · rfl
  · fin_cases j <;> simp [starEEmbedding] at h t
    all_goals omega
  · fin_cases i <;> simp [starEEmbedding] at h s
    all_goals omega
  · fin_cases i <;> fin_cases j <;>
      simp [starEEmbedding] at h s t ⊢ <;> try omega
    all_goals congr 1
    all_goals exact Fin.ext (by omega)

private theorem starCartanMatrix_one_two_two_eq_E6 :
    starCartanMatrix ![1, 2, 2] =
      CartanMatrix.E₆.submatrix (starEEmbedding 2) (starEEmbedding 2) := by
  ext v w
  rcases v with _ | ⟨i, s⟩ <;> rcases w with _ | ⟨j, t⟩
  · norm_num [Matrix.submatrix_apply, starEEmbedding, CartanMatrix.E₆]
  · fin_cases j <;> fin_cases t <;>
      norm_num [Matrix.submatrix_apply, starEEmbedding, CartanMatrix.E₆]
  · fin_cases i <;> fin_cases s <;>
      norm_num [Matrix.submatrix_apply, starEEmbedding, CartanMatrix.E₆]
  · fin_cases i <;> fin_cases j <;> fin_cases s <;> fin_cases t <;>
      norm_num [Matrix.submatrix_apply, starEEmbedding, CartanMatrix.E₆]

private theorem starCartanMatrix_one_two_three_eq_E7 :
    starCartanMatrix ![1, 2, 3] =
      CartanMatrix.E₇.submatrix (starEEmbedding 3) (starEEmbedding 3) := by
  ext v w
  rcases v with _ | ⟨i, s⟩ <;> rcases w with _ | ⟨j, t⟩
  · norm_num [Matrix.submatrix_apply, starEEmbedding, CartanMatrix.E₇]
  · fin_cases j <;> fin_cases t <;>
      norm_num [Matrix.submatrix_apply, starEEmbedding, CartanMatrix.E₇]
  · fin_cases i <;> fin_cases s <;>
      norm_num [Matrix.submatrix_apply, starEEmbedding, CartanMatrix.E₇]
  · fin_cases i <;> fin_cases j <;> fin_cases s <;> fin_cases t <;>
      norm_num [Matrix.submatrix_apply, starEEmbedding, CartanMatrix.E₇]

private theorem starCartanMatrix_one_two_four_eq_E8 :
    starCartanMatrix ![1, 2, 4] =
      CartanMatrix.E₈.submatrix (starEEmbedding 4) (starEEmbedding 4) := by
  ext v w
  rcases v with _ | ⟨i, s⟩ <;> rcases w with _ | ⟨j, t⟩
  · norm_num [Matrix.submatrix_apply, starEEmbedding, CartanMatrix.E₈]
  · fin_cases j <;> fin_cases t <;>
      norm_num [Matrix.submatrix_apply, starEEmbedding, CartanMatrix.E₈]
  · fin_cases i <;> fin_cases s <;>
      norm_num [Matrix.submatrix_apply, starEEmbedding, CartanMatrix.E₈]
  · fin_cases i <;> fin_cases j <;> fin_cases s <;> fin_cases t <;>
      norm_num [Matrix.submatrix_apply, starEEmbedding, CartanMatrix.E₈]

private theorem isFiniteType_starCartanMatrix_one_two_two :
    IsFiniteType (starCartanMatrix ![1, 2, 2]) := by
  rw [starCartanMatrix_one_two_two_eq_E6]
  exact (DynkinType.cartanMatrix_E6 ▸ DynkinType.isFiniteType_cartanMatrix_E6).submatrix
    (starEEmbedding_injective 2)

private theorem isFiniteType_starCartanMatrix_one_two_three :
    IsFiniteType (starCartanMatrix ![1, 2, 3]) := by
  rw [starCartanMatrix_one_two_three_eq_E7]
  exact (DynkinType.cartanMatrix_E7 ▸ DynkinType.isFiniteType_cartanMatrix_E7).submatrix
    (starEEmbedding_injective 3)

private theorem isFiniteType_starCartanMatrix_one_two_four :
    IsFiniteType (starCartanMatrix ![1, 2, 4]) := by
  rw [starCartanMatrix_one_two_four_eq_E8]
  exact (DynkinType.cartanMatrix_E8 ▸ DynkinType.isFiniteType_cartanMatrix_E8).submatrix
    (starEEmbedding_injective 4)

/-- An ordered three-arm star is of finite type exactly for the `A`, `D`, and exceptional `E`
shapes. Arm lengths count vertices beyond the centre, so an empty first arm gives an `A`-chain,
`![1, 1, c]` gives `D`, and `![1, 2, 2]`, `![1, 2, 3]`, `![1, 2, 4]` give `E₆`, `E₇`, `E₈`.

The forward implication is the fork bound. For the converse, the explicit reindexings above
identify every surviving model with a principal submatrix of its standard Cartan matrix. -/
theorem isFiniteType_starCartanMatrix_three_iff {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    IsFiniteType (starCartanMatrix ![a, b, c]) ↔
      a = 0 ∨ (a = 1 ∧ b = 1) ∨ (a = 1 ∧ b = 2 ∧ c ≤ 4) := by
  constructor
  · exact eq_zero_or_eq_one_one_or_eq_one_two_le_four_of_isFiniteType_star_three hab hbc
  · rintro (rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl, hc⟩)
    · exact isFiniteType_starCartanMatrix_zero b c
    · exact isFiniteType_starCartanMatrix_one_one c
    · have hc2 : 2 ≤ c := hbc
      interval_cases c
      · exact isFiniteType_starCartanMatrix_one_two_two
      · exact isFiniteType_starCartanMatrix_one_two_three
      · exact isFiniteType_starCartanMatrix_one_two_four

end TauCeti
