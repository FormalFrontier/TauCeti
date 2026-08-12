/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Fin.Tuple.Sort
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Classical
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Dynkin
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Star
import TauCeti.LinearAlgebra.RootSystem.Classification

public section

/-!
# The finite-type stars are the diagrams of types `Dₙ`, `E₆`, `E₇` and `E₈`

`TauCeti.LinearAlgebra.RootSystem.FiniteType.Star` bounds the shape of a star of finite type: with
three arms carrying `a ≤ b ≤ c` vertices besides the centre, either `a = 0` (so the star is a
chain), or `a = b = 1`, or `a = 1`, `b = 2` and `c ≤ 4`. That is an arithmetic statement about the
arm lengths, and it does not yet say which Dynkin diagram the surviving star *is*.

This file supplies the missing half: each surviving shape with no empty arm is identified with a
standard Cartan matrix of `TauCeti.DynkinType` under an explicit relabelling of its vertices by the
Bourbaki numbering. The fork `(1, 1, c)` is type `D (c + 3)`, its branch node sitting at Bourbaki
index `c`, and the three exceptional shapes `(1, 2, 2)`, `(1, 2, 3)`, `(1, 2, 4)` are `E₆`, `E₇`
and `E₈`, whose common branch node is Bourbaki index `3`. Combining the two halves gives
`TauCeti.IsFiniteType.existsUnique_dynkinType_of_star`: **a three-armed star of finite type with no
empty arm is, after one simultaneous relabelling of rows and columns, the standard Cartan matrix of
a unique valid simply-laced Dynkin type**, namely `D`, `E₆`, `E₇` or `E₈`.

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
  stars**. A star of finite type whose three arms are all nonempty carries a unique valid
  simply-laced Dynkin type.

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

/-- Relabelling the arms of a star: an equivalence `e : α ≃ β` of arm indices carries the star with
arms `ℓ ∘ e` isomorphically onto the star with arms `ℓ`, moving the vertex at position `t` of the
arm `i` to the same position of the arm `e i` and fixing the centre. -/
def starIndexCongrArms (e : α ≃ β) (ℓ : β → ℕ) : StarIndex (ℓ ∘ e) ≃ StarIndex ℓ :=
  (Equiv.sigmaCongrLeft (β := fun j ↦ Fin (ℓ j)) e).optionCongr

omit [DecidableEq α] [DecidableEq β] in
/-- Relabelling the arms fixes the centre. -/
@[simp] lemma starIndexCongrArms_none (e : α ≃ β) (ℓ : β → ℕ) :
    starIndexCongrArms e ℓ none = none := (rfl)

omit [DecidableEq α] [DecidableEq β] in
/-- Relabelling the arms keeps each arm vertex at its position along its (renamed) arm. -/
@[simp] lemma starIndexCongrArms_some (e : α ≃ β) (ℓ : β → ℕ) (v : (i : α) × Fin (ℓ (e i))) :
    starIndexCongrArms e ℓ (some v) = some ⟨e v.1, v.2⟩ := (rfl)

/-- Relabelling the arms does not change the Cartan matrix of a star. -/
theorem starCartanMatrix_comp (e : α ≃ β) (ℓ : β → ℕ) (v w : StarIndex (ℓ ∘ e)) :
    starCartanMatrix (ℓ ∘ e) v w
      = starCartanMatrix ℓ (starIndexCongrArms e ℓ v) (starIndexCongrArms e ℓ w) := by
  rcases v with _ | v <;> rcases w with _ | w <;>
    simp [e.injective.eq_iff]

/-- A matrix that agrees entrywise with a finite-type matrix along a relabelling of its index type
is itself of finite type. This is `TauCeti.IsFiniteType.submatrix` in the shape the identifications
below produce, where the relabelling is given by its action on entries rather than as a
submatrix. -/
private theorem isFiniteType_of_forall_eq {B C : Type*} [Fintype B] [Fintype C]
    {A : Matrix B B ℤ} {A' : Matrix C C ℤ} (e : C ≃ B) (hA : IsFiniteType A)
    (h : ∀ v w, A' v w = A (e v) (e w)) : IsFiniteType A' := by
  have hsub : A' = A.submatrix e e := by ext v w; exact h v w
  rw [hsub]
  exact hA.submatrix e.injective

/-- A star carrying a finite-type Dynkin diagram is of finite type. Together with the four
identifications below this is the converse of the fork bound: each admissible shape really is the
diagram of a root system. -/
theorem IsStarOfType.isFiniteType [Fintype α] (h : IsStarOfType ℓ t)
    (ht : IsFiniteType t.cartanMatrix) : IsFiniteType (starCartanMatrix ℓ) := by
  obtain ⟨e, he⟩ := h
  exact isFiniteType_of_forall_eq e ht he

/-- Carrying a Dynkin diagram is invariant under a relabelling of the arms. -/
theorem IsStarOfType.comp {m : β → ℕ} (h : IsStarOfType m t) (e : α ≃ β) :
    IsStarOfType (m ∘ e) t := by
  obtain ⟨f, hf⟩ := h
  refine ⟨(starIndexCongrArms e m).trans f, fun v w ↦ ?_⟩
  rw [starCartanMatrix_comp e m v w]
  exact hf _ _

/-- Finite type is invariant under a relabelling of the arms of a star. -/
theorem isFiniteType_starCartanMatrix_comp [Fintype α] [Fintype β] {m : β → ℕ} (e : α ≃ β)
    (h : IsFiniteType (starCartanMatrix m)) : IsFiniteType (starCartanMatrix (m ∘ e)) :=
  isFiniteType_of_forall_eq (starIndexCongrArms e m) h (starCartanMatrix_comp e m)

section Fork

/-! ### The fork `(1, 1, c)` and type `D` -/

/-- The position of a vertex of the star with arms `(1, 1, c)` in the Bourbaki numbering of type
`D (c + 3)`. When `1 ≤ c`, the centre is the branch node `c`, the two short arms are the two leaves
`c + 1` and `c + 2` of the fork, and the long arm runs back down the chain from `c - 1` to `0`.
When `c = 0`, the absent third arm leaves the three-node chain of the degenerate type `D 3`. -/
private def forkValD (c : ℕ) : StarIndex (![1, 1, c] : Fin 3 → ℕ) → ℕ
  | none => c
  | some v => if (v.1 : ℕ) = 0 then c + 1 else if (v.1 : ℕ) = 1 then c + 2 else c - 1 - (v.2 : ℕ)

private lemma forkValD_none (c : ℕ) : forkValD c none = c := rfl

private lemma forkValD_some (c : ℕ) (v : (i : Fin 3) × Fin ((![1, 1, c] : Fin 3 → ℕ) i)) :
    forkValD c (some v) =
      if (v.1 : ℕ) = 0 then c + 1 else if (v.1 : ℕ) = 1 then c + 2 else c - 1 - (v.2 : ℕ) := rfl

/-- Which arm a vertex of the star `(1, 1, c)` lies on, and where along it: the first two arms carry
their single vertex, and the third carries `c` of them. -/
private lemma forkArmD (c : ℕ) (v : (i : Fin 3) × Fin ((![1, 1, c] : Fin 3 → ℕ) i)) :
    ((v.1 : ℕ) = 0 ∧ (v.2 : ℕ) = 0) ∨ ((v.1 : ℕ) = 1 ∧ (v.2 : ℕ) = 0) ∨
      ((v.1 : ℕ) = 2 ∧ (v.2 : ℕ) < c) := by
  have key : (![1, 1, c] : Fin 3 → ℕ) v.1 =
      if (v.1 : ℕ) = 0 then 1 else if (v.1 : ℕ) = 1 then 1 else c := by
    obtain ⟨i, s⟩ := v; fin_cases i <;> simp
  have hs : (v.2 : ℕ) < (![1, 1, c] : Fin 3 → ℕ) v.1 := v.2.isLt
  have hi := v.1.isLt
  split_ifs at key <;> omega

private lemma forkValD_lt (c : ℕ) (v : StarIndex (![1, 1, c] : Fin 3 → ℕ)) :
    forkValD c v < c + 3 := by
  rcases v with _ | v
  · rw [forkValD_none]; omega
  · rw [forkValD_some]
    split_ifs <;> omega

/-- The relabelling of the star `(1, 1, c)` by the Bourbaki indices of type `D (c + 3)`. -/
private def forkIndexD (c : ℕ) (v : StarIndex (![1, 1, c] : Fin 3 → ℕ)) : Fin (c + 3) :=
  ⟨forkValD c v, forkValD_lt c v⟩

private lemma forkIndexD_val (c : ℕ) (v : StarIndex (![1, 1, c] : Fin 3 → ℕ)) :
    (forkIndexD c v : ℕ) = forkValD c v := rfl

private lemma forkIndexD_injective (c : ℕ) : Function.Injective (forkIndexD c) := by
  rintro v w h
  have hval : forkValD c v = forkValD c w := congrArg Fin.val h
  rcases v with _ | v <;> rcases w with _ | w
  · rfl
  · exfalso
    have hw := forkArmD c w
    rw [forkValD_none, forkValD_some] at hval
    split_ifs at hval <;> omega
  · exfalso
    have hv := forkArmD c v
    rw [forkValD_none, forkValD_some] at hval
    split_ifs at hval <;> omega
  · have hv := forkArmD c v
    have hw := forkArmD c w
    rw [forkValD_some, forkValD_some] at hval
    have hij : (v.1 : ℕ) = (w.1 : ℕ) := by split_ifs at hval <;> omega
    have hsu : (v.2 : ℕ) = (w.2 : ℕ) := by split_ifs at hval <;> omega
    obtain ⟨i, s⟩ := v
    obtain ⟨j, u⟩ := w
    obtain rfl : i = j := Fin.ext hij
    simp only [Option.some.injEq, Sigma.mk.injEq, heq_eq_eq, true_and]
    exact Fin.ext hsu

private lemma card_starIndex_fork (c : ℕ) :
    Fintype.card (StarIndex (![1, 1, c] : Fin 3 → ℕ)) = Fintype.card (Fin (c + 3)) := by
  simp only [StarIndex, Fintype.card_option, Fintype.card_sigma, Fintype.card_fin,
    Fin.sum_univ_three]
  norm_num [Matrix.cons_val_two]
  omega

private lemma starCartanMatrix_fork_eq (c : ℕ) (v w : StarIndex (![1, 1, c] : Fin 3 → ℕ)) :
    starCartanMatrix ![1, 1, c] v w
      = CartanMatrix.D (c + 3) (forkIndexD c v) (forkIndexD c w) := by
  rcases v with _ | v <;> rcases w with _ | w
  · rw [starCartanMatrix_none_none, CartanMatrix.D_apply]
    simp only [forkIndexD_val, forkValD_none]
    split_ifs <;> omega
  · have hw := forkArmD c w
    rw [starCartanMatrix_none_some, CartanMatrix.D_apply]
    simp only [forkIndexD_val, forkValD_none, forkValD_some]
    -- `split_ifs` normalizes some edge conditions to `True ∧ …`, which `omega` cannot read.
    split_ifs <;> first | omega | simp_all
  · have hv := forkArmD c v
    rw [starCartanMatrix_some_none, CartanMatrix.D_apply]
    simp only [forkIndexD_val, forkValD_none, forkValD_some]
    split_ifs <;> first | omega | simp_all
  · have hv := forkArmD c v
    have hw := forkArmD c w
    rw [starCartanMatrix_some_some, CartanMatrix.D_apply]
    simp only [forkIndexD_val, forkValD_some, Fin.ext_iff]
    split_ifs <;> omega

/-- **The fork of type `D`.** The star with arms of one, one and `c` vertices is the Dynkin diagram
of type `D (c + 3)`. When `1 ≤ c`, the branch node is Bourbaki index `c`, the two leaves of the fork
are `c + 1` and `c + 2`, and the long arm is the chain `c - 1, …, 0`. When `c = 0`, the third arm is
empty and the same formula identifies the resulting chain with the degenerate type `D 3`. -/
theorem isStarOfType_D (c : ℕ) : IsStarOfType (![1, 1, c] : Fin 3 → ℕ) (D (c + 3)) := by
  have hbij : Function.Bijective (forkIndexD c) :=
    (Fintype.bijective_iff_injective_and_card _).2 ⟨forkIndexD_injective c, card_starIndex_fork c⟩
  refine ⟨Equiv.ofBijective _ hbij, fun v w ↦ ?_⟩
  simp only [cartanMatrix_D]
  exact starCartanMatrix_fork_eq c v w

end Fork

section Exceptional

/-! ### The exceptional shapes `(1, 2, c)` and the types `E₆`, `E₇`, `E₈` -/

/-- The position of a vertex of the star with arms `(1, 2, c)` in the Bourbaki numbering pattern
used below for `E₆`, `E₇` and `E₈`, where `c` is respectively `2`, `3` and `4`: the centre is the
branch node `3`, the short arm is the node `1` hanging off it, the arm of two vertices is `2` then
`0`, and the long arm is `4, …, c + 3`. -/
private def forkValE (c : ℕ) : StarIndex (![1, 2, c] : Fin 3 → ℕ) → ℕ
  | none => 3
  | some v =>
      if (v.1 : ℕ) = 0 then 1
      else if (v.1 : ℕ) = 1 then (if (v.2 : ℕ) = 0 then 2 else 0)
      else 4 + (v.2 : ℕ)

/-- Which arm a vertex of the star `(1, 2, c)` lies on, and where along it. -/
private lemma forkArmE (c : ℕ) (v : (i : Fin 3) × Fin ((![1, 2, c] : Fin 3 → ℕ) i)) :
    ((v.1 : ℕ) = 0 ∧ (v.2 : ℕ) = 0) ∨ ((v.1 : ℕ) = 1 ∧ (v.2 : ℕ) < 2) ∨
      ((v.1 : ℕ) = 2 ∧ (v.2 : ℕ) < c) := by
  have key : (![1, 2, c] : Fin 3 → ℕ) v.1 =
      if (v.1 : ℕ) = 0 then 1 else if (v.1 : ℕ) = 1 then 2 else c := by
    obtain ⟨i, s⟩ := v; fin_cases i <;> simp
  have hs : (v.2 : ℕ) < (![1, 2, c] : Fin 3 → ℕ) v.1 := v.2.isLt
  have hi := v.1.isLt
  split_ifs at key <;> omega

private lemma forkValE_none (c : ℕ) : forkValE c none = 3 := rfl

private lemma forkValE_some (c : ℕ) (v : (i : Fin 3) × Fin ((![1, 2, c] : Fin 3 → ℕ) i)) :
    forkValE c (some v) =
      if (v.1 : ℕ) = 0 then 1
      else if (v.1 : ℕ) = 1 then (if (v.2 : ℕ) = 0 then 2 else 0)
      else 4 + (v.2 : ℕ) := rfl

private lemma forkValE_lt (c : ℕ) (v : StarIndex (![1, 2, c] : Fin 3 → ℕ)) :
    forkValE c v < c + 4 := by
  rcases v with _ | v
  · rw [forkValE_none]; omega
  · have h := forkArmE c v
    rw [forkValE_some]
    split_ifs <;> omega

/-- The relabelling of the star `(1, 2, c)` by the Bourbaki indices of the exceptional type of
rank `c + 4`. -/
private def forkIndexE (c : ℕ) (v : StarIndex (![1, 2, c] : Fin 3 → ℕ)) : Fin (c + 4) :=
  ⟨forkValE c v, forkValE_lt c v⟩

private lemma starCartanMatrix_exceptional_E6 (v w : StarIndex (![1, 2, 2] : Fin 3 → ℕ)) :
    starCartanMatrix ![1, 2, 2] v w = CartanMatrix.E₆ (forkIndexE 2 v) (forkIndexE 2 w) := by
  rcases v with _ | v <;> rcases w with _ | w
  · simp only [starCartanMatrix_none_none]; decide
  · revert w; simp only [starCartanMatrix_none_some]; decide
  · revert v; simp only [starCartanMatrix_some_none]; decide
  · revert v w; simp only [starCartanMatrix_some_some]; decide

private lemma starCartanMatrix_exceptional_E7 (v w : StarIndex (![1, 2, 3] : Fin 3 → ℕ)) :
    starCartanMatrix ![1, 2, 3] v w = CartanMatrix.E₇ (forkIndexE 3 v) (forkIndexE 3 w) := by
  rcases v with _ | v <;> rcases w with _ | w
  · simp only [starCartanMatrix_none_none]; decide
  · revert w; simp only [starCartanMatrix_none_some]; decide
  · revert v; simp only [starCartanMatrix_some_none]; decide
  · revert v w; simp only [starCartanMatrix_some_some]; decide

private lemma starCartanMatrix_exceptional_E8 (v w : StarIndex (![1, 2, 4] : Fin 3 → ℕ)) :
    starCartanMatrix ![1, 2, 4] v w = CartanMatrix.E₈ (forkIndexE 4 v) (forkIndexE 4 w) := by
  rcases v with _ | v <;> rcases w with _ | w
  · simp only [starCartanMatrix_none_none]; decide
  · revert w; simp only [starCartanMatrix_none_some]; decide
  · revert v; simp only [starCartanMatrix_some_none]; decide
  · revert v w; simp only [starCartanMatrix_some_some]; decide

/-- **Type `E₆`.** The star with arms of one, two and two vertices is the Dynkin diagram of `E₆`. -/
theorem isStarOfType_E6 : IsStarOfType (![1, 2, 2] : Fin 3 → ℕ) E6 := by
  have hbij : Function.Bijective (forkIndexE 2) :=
    (Fintype.bijective_iff_surjective_and_card _).2 ⟨by decide, by decide⟩
  refine ⟨Equiv.ofBijective _ hbij, fun v w ↦ ?_⟩
  simp only [cartanMatrix_E6]
  exact starCartanMatrix_exceptional_E6 v w

/-- **Type `E₇`.** The star with arms of one, two and three vertices is the Dynkin diagram of
`E₇`. -/
theorem isStarOfType_E7 : IsStarOfType (![1, 2, 3] : Fin 3 → ℕ) E7 := by
  have hbij : Function.Bijective (forkIndexE 3) :=
    (Fintype.bijective_iff_surjective_and_card _).2 ⟨by decide, by decide⟩
  refine ⟨Equiv.ofBijective _ hbij, fun v w ↦ ?_⟩
  simp only [cartanMatrix_E7]
  exact starCartanMatrix_exceptional_E7 v w

/-- **Type `E₈`.** The star with arms of one, two and four vertices is the Dynkin diagram of
`E₈`. -/
theorem isStarOfType_E8 : IsStarOfType (![1, 2, 4] : Fin 3 → ℕ) E8 := by
  have hbij : Function.Bijective (forkIndexE 4) :=
    (Fintype.bijective_iff_surjective_and_card _).2 ⟨by decide, by decide⟩
  refine ⟨Equiv.ofBijective _ hbij, fun v w ↦ ?_⟩
  simp only [cartanMatrix_E8]
  exact starCartanMatrix_exceptional_E8 v w

end Exceptional

/-- **The classification of the three-armed stars of finite type.** A star with three nonempty arms
whose Cartan matrix is of finite type carries a unique valid simply-laced Dynkin type: after one
simultaneous relabelling of rows and columns it is the standard Cartan matrix of `D n` with
`n ≥ 4`, or of `E₆`, `E₇` or `E₈`.

The shape is cut out by the fork bound
`TauCeti.eq_zero_or_eq_one_one_or_eq_one_two_le_four_of_isFiniteType_star_three`, which leaves the
arms `(1, 1, c)` and `(1, 2, c)` with `c ≤ 4` once no arm is empty, and each of those is identified
with its Bourbaki-numbered diagram by `TauCeti.isStarOfType_D`, `TauCeti.isStarOfType_E6`,
`TauCeti.isStarOfType_E7` and `TauCeti.isStarOfType_E8`.

The type is unique, by `TauCeti.DynkinType.eq_of_valid_of_forall_eq`. -/
theorem IsFiniteType.existsUnique_dynkinType_of_star {ℓ : Fin 3 → ℕ} (hℓ : ∀ i, ℓ i ≠ 0)
    (h : IsFiniteType (starCartanMatrix ℓ)) :
    ∃! t : DynkinType, t.Valid ∧ t.IsSimplyLaced ∧ IsStarOfType ℓ t := by
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
      exact isFiniteType_starCartanMatrix_comp σ h
    -- Transporting a statement about the sorted star back to `ℓ` undoes the sorting permutation.
    have hback : ∀ t : DynkinType, IsStarOfType (![ℓ (σ 0), ℓ (σ 1), ℓ (σ 2)] : Fin 3 → ℕ) t →
        IsStarOfType ℓ t := by
      intro t ht
      have hfun : ((![ℓ (σ 0), ℓ (σ 1), ℓ (σ 2)] : Fin 3 → ℕ) ∘
          (σ.symm : Fin 3 ≃ Fin 3)) = ℓ := by
        rw [← hcomp]; funext i; simp
      exact hfun ▸ ht.comp (σ.symm : Fin 3 ≃ Fin 3)
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
  obtain ⟨t, htv, hts, et, het⟩ := hex
  exact ⟨t, ⟨htv, hts, et, het⟩, fun s ⟨hsv, _, es, hes⟩ ↦
    DynkinType.eq_of_valid_of_forall_eq hsv htv es et hes het⟩

end TauCeti
