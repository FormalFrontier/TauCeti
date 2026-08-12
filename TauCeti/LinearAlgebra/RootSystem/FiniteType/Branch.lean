/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Fin.Tuple.Sort
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Star.Classification
import TauCeti.LinearAlgebra.RootSystem.Classification

public section

/-!
# The finite-type stars are the diagrams of types `Dₙ`, `E₆`, `E₇` and `E₈`

`TauCeti.LinearAlgebra.RootSystem.FiniteType.Star.Basic` bounds the shape of a star of finite type:
with three arms carrying `a ≤ b ≤ c` vertices besides the centre, either `a = 0` (so the star is a
chain), or `a = b = 1`, or `a = 1`, `b = 2` and `c ≤ 4`. That is an arithmetic statement about the
arm lengths, and it does not yet say which Dynkin diagram the surviving star *is*.

This file supplies the missing half: each surviving shape with no empty arm is identified with a
standard Cartan matrix of `TauCeti.DynkinType` under an explicit relabelling of its vertices by the
Bourbaki numbering. The fork `(1, 1, c)` is type `D (c + 3)`, its branch node sitting at Bourbaki
index `c`, and the three exceptional shapes `(1, 2, 2)`, `(1, 2, 3)`, `(1, 2, 4)` are `E₆`, `E₇`
and `E₈`, whose common branch node is Bourbaki index `3`. Combining the two halves gives
`TauCeti.IsFiniteType.existsUnique_dynkinType_of_star`: **a three-armed star of finite type with no
empty arm is, after one simultaneous relabelling of rows and columns, the standard Cartan matrix of
a unique valid Dynkin type**. Which type that is, is not part of that statement; it is the four
identifications above that name it, as `D` or one of `E₆`, `E₇` and `E₈` according to the arms.

This is the fork half of the reindexing step of the Cartan-Killing classification, the step that
turns the elimination theorems into a `DynkinType`. The complementary step for a diagram with no
branch node produces the chains `Aₙ`, and the step for a diagram with a multiple edge produces
`Bₙ`, `Cₙ`, `F₄` and `G₂`; neither is proved here. Nor is the extraction that presents a general
finite-type diagram with a branch vertex as a star - this file starts from the star.

The proofs construct explicit vertex relabellings and check the identification entrywise against
Mathlib's `CartanMatrix.D`, `.E₆`, `.E₇` and `.E₈`.

## Main definitions

* `TauCeti.IsStarOfType`: the star with arms `ℓ` carries the Dynkin diagram of type `t`, in the
  sense that some relabelling of its vertices by `Fin t.rank` matches `t.cartanMatrix` entrywise.

## Main results

* `TauCeti.isStarOfType_D`, `TauCeti.isStarOfType_E6`, `TauCeti.isStarOfType_E7`,
  `TauCeti.isStarOfType_E8`: the four admissible shapes and the types they carry.
* `TauCeti.IsStarOfType.isFiniteType`: the converse of the fork bound. A star carrying a finite-type
  diagram is of finite type, so each of the four admissible shapes does occur.
* `TauCeti.IsFiniteType.existsUnique_dynkinType_of_star`: **the classification of the three-armed
  stars**. A star of finite type whose three arms are all nonempty carries a unique valid Dynkin
  type. The statement asserts existence and uniqueness only; the type carried by a given star is
  named by the four identifications above.

## References

This file supplies the fork half of the reindexing step of the classification of finite-type Cartan
matrices, Layer 5 of `TauCetiRoadmap/RepresentationTheory/RootSystems/README.md`. See
N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4-6*, Ch. VI §4, plates IV-VII for the Bourbaki
numbering of `Dₙ` and of the exceptional types, and J. E. Humphreys, *Introduction to Lie Algebras
and Representation Theory*, §11.4, step (7).
-/

namespace TauCeti

open DynkinType

variable {α β : Type*} [DecidableEq α] [DecidableEq β] {ℓ : α → ℕ} {t : DynkinType}

/-- The star with arms `ℓ` **carries the Dynkin diagram of type `t`**: its vertices can be
relabelled by the Bourbaki indices `Fin t.rank` so that its Cartan matrix becomes the standard one
of type `t`. The relabelling is a single simultaneous permutation of rows and columns, which is the
form the Cartan-Killing classification asks for. -/
def IsStarOfType (ℓ : α → ℕ) (t : DynkinType) : Prop :=
  ∃ e : StarIndex ℓ ≃ Fin t.rank,
    ∀ v w, starCartanMatrix ℓ v w = t.cartanMatrix (e v) (e w)

/-- Carrying a Dynkin type, unfolded to the simultaneous relabelling it asserts to exist. This is
the interface through which consumers build and destructure `TauCeti.IsStarOfType`. -/
lemma isStarOfType_iff (ℓ : α → ℕ) (t : DynkinType) :
    IsStarOfType ℓ t ↔ ∃ e : StarIndex ℓ ≃ Fin t.rank,
      ∀ v w, starCartanMatrix ℓ v w = t.cartanMatrix (e v) (e w) :=
  Iff.rfl

/-- A star carrying a finite-type Dynkin diagram is of finite type. Together with the four
identifications below this is the converse of the fork bound: each admissible shape really is the
diagram of a root system. -/
theorem IsStarOfType.isFiniteType [Fintype α] (h : IsStarOfType ℓ t)
    (ht : IsFiniteType t.cartanMatrix) : IsFiniteType (starCartanMatrix ℓ) := by
  obtain ⟨e, he⟩ := (isStarOfType_iff ℓ t).mp h
  have hsub : starCartanMatrix ℓ = t.cartanMatrix.submatrix e e := by ext v w; exact he v w
  rw [hsub]
  exact ht.submatrix e.injective

/-- Carrying a Dynkin diagram is invariant under a relabelling of the arms. -/
theorem IsStarOfType.comp {m : β → ℕ} (h : IsStarOfType m t) (e : α ≃ β) :
    IsStarOfType (m ∘ e) t := by
  obtain ⟨f, hf⟩ := (isStarOfType_iff m t).mp h
  refine (isStarOfType_iff (m ∘ e) t).mpr
    ⟨(starIndexCongrArms e m).trans f, fun v w ↦ ?_⟩
  rw [starCartanMatrix_comp e m v w]
  exact hf _ _

/-- Carrying a Dynkin diagram is invariant under a relabelling of the arms, in either direction. -/
@[simp] theorem isStarOfType_comp_iff {m : β → ℕ} (e : α ≃ β) :
    IsStarOfType (m ∘ e) t ↔ IsStarOfType m t :=
  ⟨fun h ↦ (Equiv.comp_symm_eq e m (m ∘ e)).2 rfl ▸ h.comp (e.symm : β ≃ α), fun h ↦ h.comp e⟩

section Fork

/-! ### The fork `(1, 1, c)` and type `D` -/

/-- **The fork of type `D`.** The star with arms of one, one and `c` vertices is the Dynkin diagram
of type `D (c + 3)`. When `1 ≤ c`, the branch node is Bourbaki index `c`, the two leaves of the fork
are `c + 1` and `c + 2`, and the long arm is the chain `c - 1, …, 0`. When `c = 0`, the third arm is
empty and the same formula identifies the resulting chain with the degenerate type `D 3`. -/
theorem isStarOfType_D (c : ℕ) : IsStarOfType (![1, 1, c] : Fin 3 → ℕ) (D (c + 3)) := by
  refine (isStarOfType_iff _ _).mpr ⟨starIndexEquivD c, fun v w ↦ ?_⟩
  simp only [cartanMatrix_D]
  exact congrFun (congrFun (starCartanMatrix_one_one_eq_D c) v) w

end Fork

section Exceptional

/-! ### The exceptional shapes `(1, 2, c)` and the types `E₆`, `E₇`, `E₈` -/

/-- **Type `E₆`.** The star with arms of one, two and two vertices is the Dynkin diagram of `E₆`. -/
theorem isStarOfType_E6 : IsStarOfType (![1, 2, 2] : Fin 3 → ℕ) E6 := by
  refine (isStarOfType_iff _ _).mpr ⟨starIndexEquivE 2, fun v w ↦ ?_⟩
  simp only [cartanMatrix_E6]
  exact congrFun (congrFun starCartanMatrix_one_two_two_eq_E6 v) w

/-- **Type `E₇`.** The star with arms of one, two and three vertices is the Dynkin diagram of
`E₇`. -/
theorem isStarOfType_E7 : IsStarOfType (![1, 2, 3] : Fin 3 → ℕ) E7 := by
  refine (isStarOfType_iff _ _).mpr ⟨starIndexEquivE 3, fun v w ↦ ?_⟩
  simp only [cartanMatrix_E7]
  exact congrFun (congrFun starCartanMatrix_one_two_three_eq_E7 v) w

/-- **Type `E₈`.** The star with arms of one, two and four vertices is the Dynkin diagram of
`E₈`. -/
theorem isStarOfType_E8 : IsStarOfType (![1, 2, 4] : Fin 3 → ℕ) E8 := by
  refine (isStarOfType_iff _ _).mpr ⟨starIndexEquivE 4, fun v w ↦ ?_⟩
  simp only [cartanMatrix_E8]
  exact congrFun (congrFun starCartanMatrix_one_two_four_eq_E8 v) w

end Exceptional

/-- **The classification of the three-armed stars of finite type.** A star with three nonempty arms
whose Cartan matrix is of finite type carries a unique valid Dynkin type: exactly one valid type
has a standard Cartan matrix that the star becomes after one simultaneous relabelling of rows and
columns.

The statement does not name that type. It is cut out in the proof by the fork bound
`TauCeti.eq_zero_or_eq_one_one_or_eq_one_two_le_four_of_isFiniteType_star_three`, which leaves the
arms `(1, 1, c)` and `(1, 2, c)` with `c ≤ 4` once no arm is empty, and each of those is identified
with its Bourbaki-numbered diagram by `TauCeti.isStarOfType_D`, `TauCeti.isStarOfType_E6`,
`TauCeti.isStarOfType_E7` and `TauCeti.isStarOfType_E8`; those four theorems are what exhibit the
type for a given star, as `D n` with `4 ≤ n`, or as `E₆`, `E₇` or `E₈`.

The type is unique, by `TauCeti.DynkinType.eq_of_valid_of_forall_eq`. -/
theorem IsFiniteType.existsUnique_dynkinType_of_star {ℓ : Fin 3 → ℕ} (hℓ : ∀ i, ℓ i ≠ 0)
    (h : IsFiniteType (starCartanMatrix ℓ)) :
    ∃! t : DynkinType, t.Valid ∧ IsStarOfType ℓ t := by
  have hex : ∃ t : DynkinType, t.Valid ∧ t.IsSimplyLaced ∧ IsStarOfType ℓ t := by
    -- Sort the arms so that the fork bound applies, and record the sorted star as a `![a, b, c]`.
    obtain ⟨σ, hmono⟩ : ∃ σ : Equiv.Perm (Fin 3), Monotone (ℓ ∘ σ) :=
      ⟨Tuple.sort ℓ, Tuple.monotone_sort ℓ⟩
    have hcomp : ℓ ∘ σ = ![ℓ (σ 0), ℓ (σ 1), ℓ (σ 2)] := by
      funext i; fin_cases i <;> rfl
    have hab : ℓ (σ 0) ≤ ℓ (σ 1) := hmono (by decide)
    have hbc : ℓ (σ 1) ≤ ℓ (σ 2) := hmono (by decide)
    have hsorted : IsFiniteType (starCartanMatrix ![ℓ (σ 0), ℓ (σ 1), ℓ (σ 2)]) := by
      rw [← hcomp]
      exact (isFiniteType_starCartanMatrix_comp_iff (σ : Fin 3 ≃ Fin 3)).2 h
    -- Transporting a statement about the sorted star back to `ℓ` undoes the sorting permutation.
    have hback : ∀ t : DynkinType, IsStarOfType (![ℓ (σ 0), ℓ (σ 1), ℓ (σ 2)] : Fin 3 → ℕ) t →
        IsStarOfType ℓ t := by
      intro t ht
      rw [← hcomp] at ht
      exact (isStarOfType_comp_iff (σ : Fin 3 ≃ Fin 3)).1 ht
    -- The fork bound leaves the fork `(1, 1, c)` and the three exceptional shapes.
    rcases
        eq_zero_or_eq_one_one_or_eq_one_two_le_four_of_isFiniteType_star_three hab hbc hsorted with
      h0 | ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
    · exact absurd h0 (hℓ (σ 0))
    · refine ⟨D (ℓ (σ 2) + 3), ?_, isSimplyLaced_D _, hback _ ?_⟩
      · simp only [valid_D]; omega
      · rw [h1, h2]; exact isStarOfType_D _
    · have hc : ℓ (σ 2) = 2 ∨ ℓ (σ 2) = 3 ∨ ℓ (σ 2) = 4 := by omega
      rcases hc with hc | hc | hc
      · refine ⟨E6, valid_E6, isSimplyLaced_E6, hback _ ?_⟩
        rw [h1, h2, hc]; exact isStarOfType_E6
      · refine ⟨E7, valid_E7, isSimplyLaced_E7, hback _ ?_⟩
        rw [h1, h2, hc]; exact isStarOfType_E7
      · refine ⟨E8, valid_E8, isSimplyLaced_E8, hback _ ?_⟩
        rw [h1, h2, hc]; exact isStarOfType_E8
  obtain ⟨t, htv, _, et, het⟩ := hex
  exact ⟨t, ⟨htv, et, het⟩, fun s ⟨hsv, es, hes⟩ ↦
    DynkinType.eq_of_valid_of_forall_eq hsv htv es et hes het⟩

end TauCeti
