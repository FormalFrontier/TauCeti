/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Data.Fin.Tuple.Sort
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Star.Basic
import TauCeti.LinearAlgebra.RootSystem.FiniteType.Classical
import TauCeti.LinearAlgebra.RootSystem.FiniteType.Dynkin
import TauCeti.LinearAlgebra.RootSystem.Classification

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

## Main definitions

* `TauCeti.StarHasCartanType`: a star whose Cartan matrix agrees with a standard Dynkin Cartan
  matrix after simultaneously relabelling its rows and columns.

## Main results

* `TauCeti.isFiniteType_starCartanMatrix_three_iff`: the ordered finite stars are precisely the
  `A`, `D`, and exceptional `E` shapes.
* `TauCeti.starHasCartanType_D`, `TauCeti.starHasCartanType_E6`,
  `TauCeti.starHasCartanType_E7`, `TauCeti.starHasCartanType_E8`: the non-chain shapes carry the
  indicated standard Cartan types.
* `TauCeti.IsFiniteType.existsUnique_dynkinType_of_star`: a finite star whose three arms are
  nonempty carries a unique valid Dynkin type.

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

private theorem starCartanMatrix_zero_eq_submatrix_A (b c : ℕ) :
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
  rw [starCartanMatrix_zero_eq_submatrix_A]
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

private noncomputable def starIndexEquivD (c : ℕ) : StarIndex ![1, 1, c] ≃ Fin (c + 3) :=
  Equiv.ofBijective (starDEmbedding c) <|
    (Fintype.bijective_iff_injective_and_card _).2 ⟨starDEmbedding_injective c, by
      simp only [StarIndex, Fintype.card_option, Fintype.card_sigma, Fintype.card_fin,
        Fin.sum_univ_three]
      norm_num [Matrix.cons_val_two]
      omega⟩

private theorem starCartanMatrix_one_one_eq_submatrix_D (c : ℕ) :
    starCartanMatrix ![1, 1, c] =
      (CartanMatrix.D (c + 3)).submatrix (starIndexEquivD c) (starIndexEquivD c) := by
  ext v w
  rcases v with _ | ⟨i, s⟩ <;> rcases w with _ | ⟨j, t⟩
  · simp [Matrix.submatrix_apply, starIndexEquivD, starDEmbedding, CartanMatrix.D]
  · fin_cases j <;>
      simp [Matrix.submatrix_apply, starIndexEquivD, starDEmbedding, CartanMatrix.D] at t ⊢
    all_goals split_ifs
    all_goals omega
  · fin_cases i <;>
      simp [Matrix.submatrix_apply, starIndexEquivD, starDEmbedding, CartanMatrix.D] at s ⊢
    all_goals split_ifs
    all_goals omega
  · fin_cases i <;> fin_cases j <;>
      simp [Matrix.submatrix_apply, starIndexEquivD, starDEmbedding, CartanMatrix.D] at s t ⊢ <;>
      split_ifs <;> omega

private theorem isFiniteType_starCartanMatrix_one_one (c : ℕ) :
    IsFiniteType (starCartanMatrix ![1, 1, c]) := by
  rw [starCartanMatrix_one_one_eq_submatrix_D]
  exact (isFiniteType_cartanMatrix_D _).submatrix (starIndexEquivD c).injective

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

private noncomputable def starIndexEquivE (c : ℕ) : StarIndex ![1, 2, c] ≃ Fin (c + 4) :=
  Equiv.ofBijective (starEEmbedding c) <|
    (Fintype.bijective_iff_injective_and_card _).2 ⟨starEEmbedding_injective c, by
      simp only [StarIndex, Fintype.card_option, Fintype.card_sigma, Fintype.card_fin,
        Fin.sum_univ_three]
      norm_num [Matrix.cons_val_two]
      omega⟩

private theorem starCartanMatrix_one_two_two_eq_submatrix_E6 :
    starCartanMatrix ![1, 2, 2] =
      CartanMatrix.E₆.submatrix (starIndexEquivE 2) (starIndexEquivE 2) := by
  ext v w
  rcases v with _ | ⟨i, s⟩ <;> rcases w with _ | ⟨j, t⟩
  · norm_num [Matrix.submatrix_apply, starIndexEquivE, starEEmbedding, CartanMatrix.E₆]
  · fin_cases j <;> fin_cases t <;>
      norm_num [Matrix.submatrix_apply, starIndexEquivE, starEEmbedding, CartanMatrix.E₆]
  · fin_cases i <;> fin_cases s <;>
      norm_num [Matrix.submatrix_apply, starIndexEquivE, starEEmbedding, CartanMatrix.E₆]
  · fin_cases i <;> fin_cases j <;> fin_cases s <;> fin_cases t <;>
      norm_num [Matrix.submatrix_apply, starIndexEquivE, starEEmbedding, CartanMatrix.E₆]

private theorem starCartanMatrix_one_two_three_eq_submatrix_E7 :
    starCartanMatrix ![1, 2, 3] =
      CartanMatrix.E₇.submatrix (starIndexEquivE 3) (starIndexEquivE 3) := by
  ext v w
  rcases v with _ | ⟨i, s⟩ <;> rcases w with _ | ⟨j, t⟩
  · norm_num [Matrix.submatrix_apply, starIndexEquivE, starEEmbedding, CartanMatrix.E₇]
  · fin_cases j <;> fin_cases t <;>
      norm_num [Matrix.submatrix_apply, starIndexEquivE, starEEmbedding, CartanMatrix.E₇]
  · fin_cases i <;> fin_cases s <;>
      norm_num [Matrix.submatrix_apply, starIndexEquivE, starEEmbedding, CartanMatrix.E₇]
  · fin_cases i <;> fin_cases j <;> fin_cases s <;> fin_cases t <;>
      norm_num [Matrix.submatrix_apply, starIndexEquivE, starEEmbedding, CartanMatrix.E₇]

private theorem starCartanMatrix_one_two_four_eq_submatrix_E8 :
    starCartanMatrix ![1, 2, 4] =
      CartanMatrix.E₈.submatrix (starIndexEquivE 4) (starIndexEquivE 4) := by
  ext v w
  rcases v with _ | ⟨i, s⟩ <;> rcases w with _ | ⟨j, t⟩
  · norm_num [Matrix.submatrix_apply, starIndexEquivE, starEEmbedding, CartanMatrix.E₈]
  · fin_cases j <;> fin_cases t <;>
      norm_num [Matrix.submatrix_apply, starIndexEquivE, starEEmbedding, CartanMatrix.E₈]
  · fin_cases i <;> fin_cases s <;>
      norm_num [Matrix.submatrix_apply, starIndexEquivE, starEEmbedding, CartanMatrix.E₈]
  · fin_cases i <;> fin_cases j <;> fin_cases s <;> fin_cases t <;>
      norm_num [Matrix.submatrix_apply, starIndexEquivE, starEEmbedding, CartanMatrix.E₈]

private theorem isFiniteType_starCartanMatrix_one_two_two :
    IsFiniteType (starCartanMatrix ![1, 2, 2]) := by
  rw [starCartanMatrix_one_two_two_eq_submatrix_E6]
  exact (DynkinType.cartanMatrix_E6 ▸ DynkinType.isFiniteType_cartanMatrix_E6).submatrix
    (starIndexEquivE 2).injective

private theorem isFiniteType_starCartanMatrix_one_two_three :
    IsFiniteType (starCartanMatrix ![1, 2, 3]) := by
  rw [starCartanMatrix_one_two_three_eq_submatrix_E7]
  exact (DynkinType.cartanMatrix_E7 ▸ DynkinType.isFiniteType_cartanMatrix_E7).submatrix
    (starIndexEquivE 3).injective

private theorem isFiniteType_starCartanMatrix_one_two_four :
    IsFiniteType (starCartanMatrix ![1, 2, 4]) := by
  rw [starCartanMatrix_one_two_four_eq_submatrix_E8]
  exact (DynkinType.cartanMatrix_E8 ▸ DynkinType.isFiniteType_cartanMatrix_E8).submatrix
    (starIndexEquivE 4).injective

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

/-! ## Cartan types of forks -/

open DynkinType

variable {α β : Type*} [DecidableEq α] [DecidableEq β] {ℓ : α → ℕ} {t : DynkinType}

/-- The star with arms `ℓ` **has Cartan type `t`** when its vertices can be relabelled by the
Bourbaki indices `Fin t.rank` so that its Cartan matrix becomes the standard one of type `t`.
The same relabelling is applied simultaneously to rows and columns. -/
def StarHasCartanType (ℓ : α → ℕ) (t : DynkinType) : Prop :=
  ∃ e : StarIndex ℓ ≃ Fin t.rank,
    ∀ v w, starCartanMatrix ℓ v w = t.cartanMatrix (e v) (e w)

/-- Having Cartan type `t`, unfolded to the simultaneous relabelling it asserts to exist. This is
the interface through which consumers build and destructure `TauCeti.StarHasCartanType`. -/
lemma starHasCartanType_iff (ℓ : α → ℕ) (t : DynkinType) :
    StarHasCartanType ℓ t ↔ ∃ e : StarIndex ℓ ≃ Fin t.rank,
      ∀ v w, starCartanMatrix ℓ v w = t.cartanMatrix (e v) (e w) :=
  Iff.rfl

/-- Having Cartan type `t`, expressed as a reindexing of matrices rather than entrywise. -/
lemma starHasCartanType_iff_reindex (ℓ : α → ℕ) (t : DynkinType) :
    StarHasCartanType ℓ t ↔
      ∃ e : StarIndex ℓ ≃ Fin t.rank, (starCartanMatrix ℓ).reindex e e = t.cartanMatrix := by
  refine exists_congr fun e ↦ ⟨fun h ↦ ?_, fun h v w ↦ ?_⟩
  · ext v w
    simpa using h (e.symm v) (e.symm w)
  · simpa using congrFun₂ h (e v) (e w)

/-- A star has at most one valid Cartan type. -/
theorem StarHasCartanType.eq_of_valid (h : StarHasCartanType ℓ t)
    (h' : StarHasCartanType ℓ t') (ht : t.Valid) (ht' : t'.Valid) : t = t' := by
  obtain ⟨e, he⟩ := (starHasCartanType_iff ℓ t).mp h
  obtain ⟨e', he'⟩ := (starHasCartanType_iff ℓ t').mp h'
  exact DynkinType.eq_of_valid_of_forall_eq ht ht' e e' he he'

/-- Having a Cartan type is invariant under relabelling the arms. -/
theorem StarHasCartanType.comp {m : β → ℕ} (h : StarHasCartanType m t) (e : α ≃ β) :
    StarHasCartanType (m ∘ e) t := by
  obtain ⟨f, hf⟩ := (starHasCartanType_iff m t).mp h
  refine (starHasCartanType_iff (m ∘ e) t).mpr
    ⟨(starIndexCongrArms e m).trans f, fun v w ↦ ?_⟩
  rw [starCartanMatrix_comp_apply e m v w]
  exact hf _ _

/-- Having a Cartan type is invariant under relabelling the arms, in either direction. -/
@[simp] theorem starHasCartanType_comp_iff {m : β → ℕ} (e : α ≃ β) :
    StarHasCartanType (m ∘ e) t ↔ StarHasCartanType m t := by
  constructor
  · intro h
    have hm : m = (m ∘ e) ∘ e.symm := by
      funext b
      simp
    rw [hm]
    exact h.comp (e.symm : β ≃ α)
  · exact fun h ↦ h.comp e

private lemma starHasCartanType_of_eq_submatrix (e : StarIndex ℓ ≃ Fin t.rank)
    (h : starCartanMatrix ℓ = t.cartanMatrix.submatrix e e) : StarHasCartanType ℓ t :=
  (starHasCartanType_iff ℓ t).mpr ⟨e, fun v w ↦ by rw [h, Matrix.submatrix_apply]⟩

/-! ### The fork `(1, 1, c)` and type `D` -/

/-- **The fork of type `D`.** The star with arms of one, one and `c` vertices has Cartan type
`D (c + 3)`. When `1 ≤ c`, the branch node is Bourbaki index `c`, the two leaves of the fork are
`c + 1` and `c + 2`, and the long arm is the chain `c - 1, …, 0`. When `c = 0`, the third arm is
empty and the same formula identifies the resulting chain with the degenerate type `D 3`. -/
theorem starHasCartanType_D (c : ℕ) :
    StarHasCartanType (![1, 1, c] : Fin 3 → ℕ) (D (c + 3)) := by
  apply starHasCartanType_of_eq_submatrix (starIndexEquivD c)
  rw [cartanMatrix_D]
  exact starCartanMatrix_one_one_eq_submatrix_D c

/-! ### The exceptional shapes `(1, 2, c)` and the types `E₆`, `E₇`, `E₈` -/

/-- **Type `E₆`.** The star with arms of one, two and two vertices has Cartan type `E₆`. -/
theorem starHasCartanType_E6 : StarHasCartanType (![1, 2, 2] : Fin 3 → ℕ) E6 := by
  apply starHasCartanType_of_eq_submatrix (starIndexEquivE 2)
  rw [cartanMatrix_E6]
  exact starCartanMatrix_one_two_two_eq_submatrix_E6

/-- **Type `E₇`.** The star with arms of one, two and three vertices has Cartan type `E₇`. -/
theorem starHasCartanType_E7 : StarHasCartanType (![1, 2, 3] : Fin 3 → ℕ) E7 := by
  apply starHasCartanType_of_eq_submatrix (starIndexEquivE 3)
  rw [cartanMatrix_E7]
  exact starCartanMatrix_one_two_three_eq_submatrix_E7

/-- **Type `E₈`.** The star with arms of one, two and four vertices has Cartan type `E₈`. -/
theorem starHasCartanType_E8 : StarHasCartanType (![1, 2, 4] : Fin 3 → ℕ) E8 := by
  apply starHasCartanType_of_eq_submatrix (starIndexEquivE 4)
  rw [cartanMatrix_E8]
  exact starCartanMatrix_one_two_four_eq_submatrix_E8

/-- **The classification of the three-armed forks of finite type.** A finite star with three
nonempty arms has a unique valid Cartan type: exactly one valid standard Cartan matrix agrees with
the star after simultaneously relabelling its rows and columns.

The fork bound leaves the shapes `(1, 1, c)`, `(1, 2, 2)`, `(1, 2, 3)`, and `(1, 2, 4)` after the
arms are sorted. The theorems `TauCeti.starHasCartanType_D`, `TauCeti.starHasCartanType_E6`,
`TauCeti.starHasCartanType_E7`, and `TauCeti.starHasCartanType_E8` identify those shapes as `D` or
one of the exceptional `E` types. Uniqueness follows from
`TauCeti.DynkinType.eq_of_valid_of_forall_eq`. -/
theorem IsFiniteType.existsUnique_dynkinType_of_star {ℓ : Fin 3 → ℕ} (hℓ : ∀ i, ℓ i ≠ 0)
    (h : IsFiniteType (starCartanMatrix ℓ)) :
    ∃! t : DynkinType, t.Valid ∧ StarHasCartanType ℓ t := by
  have hex : ∃ t : DynkinType, t.Valid ∧ StarHasCartanType ℓ t := by
    obtain ⟨σ, hmono⟩ : ∃ σ : Equiv.Perm (Fin 3), Monotone (ℓ ∘ σ) :=
      ⟨Tuple.sort ℓ, Tuple.monotone_sort ℓ⟩
    have hcomp : ℓ ∘ σ = ![ℓ (σ 0), ℓ (σ 1), ℓ (σ 2)] := by
      funext i
      fin_cases i <;> rfl
    have hab : ℓ (σ 0) ≤ ℓ (σ 1) := hmono (by decide)
    have hbc : ℓ (σ 1) ≤ ℓ (σ 2) := hmono (by decide)
    have hsorted : IsFiniteType (starCartanMatrix ![ℓ (σ 0), ℓ (σ 1), ℓ (σ 2)]) := by
      rw [← hcomp]
      exact (isFiniteType_starCartanMatrix_comp_iff (σ : Fin 3 ≃ Fin 3)).2 h
    have hback : ∀ t : DynkinType,
        StarHasCartanType (![ℓ (σ 0), ℓ (σ 1), ℓ (σ 2)] : Fin 3 → ℕ) t →
          StarHasCartanType ℓ t := by
      intro t ht
      rw [← hcomp] at ht
      exact (starHasCartanType_comp_iff (σ : Fin 3 ≃ Fin 3)).1 ht
    rcases
        eq_zero_or_eq_one_one_or_eq_one_two_le_four_of_isFiniteType_star_three hab hbc hsorted with
      h0 | ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
    · exact absurd h0 (hℓ (σ 0))
    · refine ⟨D (ℓ (σ 2) + 3), ?_, hback _ ?_⟩
      · simp only [valid_D]
        omega
      · rw [h1, h2]
        exact starHasCartanType_D _
    · have hc : ℓ (σ 2) = 2 ∨ ℓ (σ 2) = 3 ∨ ℓ (σ 2) = 4 := by omega
      rcases hc with hc | hc | hc
      · refine ⟨E6, valid_E6, hback _ ?_⟩
        rw [h1, h2, hc]
        exact starHasCartanType_E6
      · refine ⟨E7, valid_E7, hback _ ?_⟩
        rw [h1, h2, hc]
        exact starHasCartanType_E7
      · refine ⟨E8, valid_E8, hback _ ?_⟩
        rw [h1, h2, hc]
        exact starHasCartanType_E8
  obtain ⟨t, htv, ht⟩ := hex
  exact ⟨t, ⟨htv, ht⟩, fun _ hs ↦ hs.2.eq_of_valid ht hs.1 htv⟩

end TauCeti
