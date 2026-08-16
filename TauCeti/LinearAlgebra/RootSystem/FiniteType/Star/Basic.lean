/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.NumberTheory.ADEInequality
public import TauCeti.LinearAlgebra.RootSystem.Chain
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Basic

public section

/-!
# The fork bound for finite-type Cartan matrices

A connected finite-type diagram is a tree whose vertices have degree at most three. Such a tree may
branch at several vertices, and a branch vertex together with a choice of path into each of its
three branches carries a **star**: that vertex as the centre, with three arms hanging off it. Which
stars survive is the fork half of the "chain/fork length constraints" of the Cartan-Killing
classification, and it is an arithmetic constraint. Writing `p, q, r` for the numbers of vertices on
the three arms *counting the centre*, a star of finite type satisfies

`1 / p + 1 / q + 1 / r > 1`,

whose solutions with `p ≤ q ≤ r` are `(1, q, r)`, `(2, 2, r)`, `(2, 3, 3)`, `(2, 3, 4)` and
`(2, 3, 5)` - the chains `Aₙ`, the forks `Dₙ`, and `E₆`, `E₇`, `E₈`.

Only that arithmetic constraint is proved here. The step that produces a star from a diagram with a
branch vertex is outside this file, and so is the constraint governing a multiple edge (the one
behind `B`, `C`, `F₄`), which is
`TauCeti.LinearAlgebra.RootSystem.FiniteType.DoubleEdge.Basic`.

This file builds the star as a matrix, `TauCeti.starCartanMatrix`, out of the chain entries of
`TauCeti.LinearAlgebra.RootSystem.Chain`, over an arbitrary finite index type of arms, and proves
the bound. The elimination tool is a new one, living with the others in
`TauCeti.LinearAlgebra.RootSystem.FiniteType.Basic`: a finite-type matrix admits no nonzero
**subdominant** vector, one whose every coordinate `xᵢ` has `xᵢ · (A x)ᵢ ≤ 0`
(`TauCeti.IsFiniteType.eq_zero_of_forall_mul_sum_apply_mul_nonpos`), because the symmetrized
quadratic form evaluates at such a vector to `∑ᵢ dᵢ xᵢ (A x)ᵢ ≤ 0`. The certificate for a star is
its vector of **marks** `TauCeti.starMark`, which decreases linearly along each arm, from `p q r` at
the centre down to `q r` at the far end of the first arm. The marks are annihilated by the matrix
at every arm vertex, and at the centre they take the value `qr + pr + pq - pqr`, which is `≤ 0`
exactly when the fork bound fails.

The three critical stars, where the marks are a genuine null vector, are the extended Dynkin
diagrams `Ẽ₆ = T(3, 3, 3)`, `Ẽ₇ = T(2, 4, 4)` and `Ẽ₈ = T(2, 3, 6)`; they are recorded as
corollaries. Since the argument is uniform in the number of arms, the `n`-armed form of the bound,
`∑ᵢ 1 / pᵢ > n - 2`, comes out at the same time, and at `n = 4` with every `pᵢ = 2` it reproves the
exclusion of `D̃₄` that `TauCeti.not_isFiniteType_affineD₄` gets from the degree bound.

## Main definitions

* `TauCeti.StarIndex`: the vertices of a star - a centre `none`, and `ℓ i` further vertices on the
  arm `i`, the vertex `some ⟨i, t⟩` sitting at distance `t + 1` from the centre.
* `TauCeti.starCartanMatrix`: the Cartan matrix of a star, simply laced by construction.
* `TauCeti.starIndexCongrArms`: the relabelling of the vertices of a star induced by a relabelling
  of its arms, under which both the Cartan matrix (`TauCeti.starCartanMatrix_comp`) and finite type
  (`TauCeti.isFiniteType_starCartanMatrix_comp_iff`) are invariant.
* `TauCeti.starMark`: the marks of a star, the test vector the bound is proved with.

## Main results

* `TauCeti.card_sub_two_lt_sum_inv_of_isFiniteType_star` and
  `TauCeti.not_isFiniteType_starCartanMatrix_of_sum_inv_le`: **the fork bound**,
  `∑ᵢ 1 / (ℓ i + 1) > n - 2` for a star of finite type with `n` arms, and its contrapositive.
* `TauCeti.one_lt_sum_inv_of_isFiniteType_star_three` and
  `TauCeti.not_isFiniteType_starCartanMatrix_three_of_sum_inv_le_one`: the same pair for three arms,
  where the bound reads `1 / p + 1 / q + 1 / r > 1`.
* `TauCeti.eq_zero_or_eq_one_one_or_eq_one_two_le_four_of_isFiniteType_star_three`:
  **the admissible three-armed shapes**. A finite-type
  star with arms of `a ≤ b ≤ c` further vertices has `a = 0` (a chain), or `a = b = 1` (a fork of
  type `D`), or `a = 1`, `b = 2` and `c ≤ 4` (types `E₆`, `E₇`, `E₈`). The solutions are read off
  Mathlib's `ADEInequality.lt_three`, `.lt_four` and `.lt_six`.
* `TauCeti.not_isFiniteType_affineE₆`, `TauCeti.not_isFiniteType_affineE₇`,
  `TauCeti.not_isFiniteType_affineE₈`: the three critical stars are not of finite type.

## References

This file supplies the fork half of the "chain/fork length constraints" step of the classification
of finite-type Cartan matrices, Layer 5 of
`TauCetiRoadmap/RepresentationTheory/RootSystems/README.md`. See
J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §11.4, step (7), where
the inequality `1/p + 1/q + 1/r > 1` is obtained from the same linear weighting of the arms, and
Bourbaki, *Lie Groups and Lie Algebras, Chapters 4-6*, Ch. VI §4.
-/

open scoped Matrix

namespace TauCeti

variable {α : Type*} [DecidableEq α] {ℓ : α → ℕ}

/-- The vertices of the **star** with arms of lengths `ℓ`: a centre, written `none`, together with
`ℓ i` further vertices on the arm `i`, the vertex `some ⟨i, t⟩` sitting at distance `t + 1` from
the centre. An arm with `ℓ i = 0` is absent, so the degree of the centre is the number of `i` with
`ℓ i ≠ 0`. -/
abbrev StarIndex (ℓ : α → ℕ) : Type _ := Option ((i : α) × Fin (ℓ i))

/-- The **Cartan matrix of a star**: the simply-laced matrix whose diagram is the star with arms of
lengths `ℓ`. Two vertices are joined exactly when they are consecutive along a common arm, the
centre counting as position `0` of every arm. -/
def starCartanMatrix (ℓ : α → ℕ) : Matrix (StarIndex ℓ) (StarIndex ℓ) ℤ :=
  Matrix.of fun v w ↦
    match v, w with
    | none, none => chainEntry 0 0
    | none, some w => chainEntry 0 (w.2 + 1)
    | some v, none => chainEntry (v.2 + 1) 0
    | some v, some w => if v.1 = w.1 then chainEntry (v.2 + 1) (w.2 + 1) else 0

@[simp] lemma starCartanMatrix_none_none : starCartanMatrix ℓ none none = 2 := chainEntry_self 0

-- `(rfl)`, not `rfl`: the body of `TauCeti.starCartanMatrix` is deliberately left unexposed, and
-- the parenthesised form keeps these equations out of the exported definitional-equality check.
private lemma starCartanMatrix_none_some_chain (w : (i : α) × Fin (ℓ i)) :
    starCartanMatrix ℓ none (some w) = chainEntry 0 ((w.2 : ℕ) + 1) := (rfl)

private lemma starCartanMatrix_some_none_chain (v : (i : α) × Fin (ℓ i)) :
    starCartanMatrix ℓ (some v) none = chainEntry ((v.2 : ℕ) + 1) 0 := (rfl)

private lemma starCartanMatrix_some_some_chain (v w : (i : α) × Fin (ℓ i)) :
    starCartanMatrix ℓ (some v) (some w)
      = if v.1 = w.1 then chainEntry ((v.2 : ℕ) + 1) ((w.2 : ℕ) + 1) else 0 := (rfl)

/-- The centre is joined precisely to the first vertex of each nonempty arm. -/
@[simp] lemma starCartanMatrix_none_some (w : (i : α) × Fin (ℓ i)) :
    starCartanMatrix ℓ none (some w) = if (w.2 : ℕ) = 0 then -1 else 0 := by
  rw [starCartanMatrix_none_some_chain]
  simp [chainEntry_def]

/-- The centre is joined precisely to the first vertex of each nonempty arm. -/
@[simp] lemma starCartanMatrix_some_none (v : (i : α) × Fin (ℓ i)) :
    starCartanMatrix ℓ (some v) none = if (v.2 : ℕ) = 0 then -1 else 0 := by
  rw [starCartanMatrix_some_none_chain]
  simp [chainEntry_def]

/-- Two arm vertices have entry `2` when equal, `-1` when consecutive on the same arm, and `0`
otherwise. -/
@[simp] lemma starCartanMatrix_some_some (v w : (i : α) × Fin (ℓ i)) :
    starCartanMatrix ℓ (some v) (some w) = if v.1 = w.1 then
        if (v.2 : ℕ) = w.2 then 2
        else if (v.2 : ℕ) = w.2 + 1 then -1
        else if (w.2 : ℕ) = v.2 + 1 then -1 else 0
      else 0 := by
  rw [starCartanMatrix_some_some_chain]
  simp only [chainEntry_def]
  split_ifs <;> omega

/-- A star is simply laced, in particular symmetric: each arm is a chain, and being on a common arm
is a symmetric relation. -/
@[simp] lemma starCartanMatrix_transpose : (starCartanMatrix ℓ)ᵀ = starCartanMatrix ℓ := by
  ext v w
  rcases v with _ | v <;> rcases w with _ | w
  · rfl
  · rw [Matrix.transpose_apply, starCartanMatrix_some_none_chain, starCartanMatrix_none_some_chain,
      chainEntry_comm]
  · rw [Matrix.transpose_apply, starCartanMatrix_none_some_chain, starCartanMatrix_some_none_chain,
      chainEntry_comm]
  · rw [Matrix.transpose_apply, starCartanMatrix_some_some_chain,
      starCartanMatrix_some_some_chain]
    rcases eq_or_ne v.1 w.1 with h | h
    · rw [ite_eq_left h, ite_eq_left h.symm, chainEntry_comm]
    · rw [ite_eq_right h, ite_eq_right (Ne.symm h)]

section Relabel

/-! ### Relabelling the arms -/

variable {β : Type*} [DecidableEq β]

omit [DecidableEq α] [DecidableEq β] in
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

/-- Relabelling the arms does not change an entry of the Cartan matrix of a star. -/
@[simp] theorem starCartanMatrix_comp_apply (e : α ≃ β) (ℓ : β → ℕ)
    (v w : StarIndex (ℓ ∘ e)) :
    starCartanMatrix (ℓ ∘ e) v w
      = starCartanMatrix ℓ (starIndexCongrArms e ℓ v) (starIndexCongrArms e ℓ w) := by
  rcases v with _ | v <;> rcases w with _ | w <;>
    simp [e.injective.eq_iff]

/-- Relabelling the arms reindexes the Cartan matrix of a star.

Deliberately not `@[simp]`: it replaces the compact `starCartanMatrix (ℓ ∘ e)` by a submatrix, so
it would preempt the normalizations that strip the relabelling outright, such as
`TauCeti.isFiniteType_starCartanMatrix_comp_iff`. The entrywise
`TauCeti.starCartanMatrix_comp_apply` is the simp-normal form of a relabelled entry. -/
theorem starCartanMatrix_comp (e : α ≃ β) (ℓ : β → ℕ) :
    starCartanMatrix (ℓ ∘ e) =
      (starCartanMatrix ℓ).submatrix (starIndexCongrArms e ℓ) (starIndexCongrArms e ℓ) := by
  ext v w
  exact starCartanMatrix_comp_apply e ℓ v w

/-- Finite type is invariant under a relabelling of the arms of a star. -/
theorem isFiniteType_starCartanMatrix_comp [Fintype α] [Fintype β] {m : β → ℕ} (e : α ≃ β)
    (h : IsFiniteType (starCartanMatrix m)) : IsFiniteType (starCartanMatrix (m ∘ e)) := by
  rw [starCartanMatrix_comp]
  exact h.submatrix (starIndexCongrArms e m).injective

/-- Finite type is invariant under a relabelling of the arms of a star, in either direction. -/
@[simp] theorem isFiniteType_starCartanMatrix_comp_iff [Fintype α] [Fintype β] {m : β → ℕ}
    (e : α ≃ β) : IsFiniteType (starCartanMatrix (m ∘ e)) ↔
      IsFiniteType (starCartanMatrix m) := by
  constructor
  · intro h
    have hm : m = (m ∘ e) ∘ e.symm := by
      funext b
      simp
    rw [hm]
    exact isFiniteType_starCartanMatrix_comp (e.symm : β ≃ α) h
  · exact isFiniteType_starCartanMatrix_comp e

end Relabel

variable [Fintype α]

/-- The **marks** of a star: the value `∏ᵢ (ℓ i + 1)` at the centre, decreasing linearly along the
arm `i` in steps of `∏_{j ≠ i} (ℓ j + 1)`, down to that step itself at the far end of the arm.

In the critical cases these are a positive multiple of the marks of the corresponding extended
Dynkin diagram - for `ℓ = ![2, 2, 2]` they are `9` times the marks of `Ẽ₆` - and the same formula
serves in general: the Cartan matrix annihilates them at every arm vertex whatever the arm lengths
are, and only the value at the centre feels the fork bound. -/
def starMark (ℓ : α → ℕ) : StarIndex ℓ → ℚ
  | none => ∏ i, ((ℓ i : ℚ) + 1)
  | some v => ((ℓ v.1 : ℚ) - (v.2 : ℕ)) * ∏ j ∈ ({v.1}ᶜ : Finset α), ((ℓ j : ℚ) + 1)

@[simp] lemma starMark_none : starMark ℓ none = ∏ i, ((ℓ i : ℚ) + 1) := (rfl)

@[simp] lemma starMark_some (v : (i : α) × Fin (ℓ i)) :
    starMark ℓ (some v) = ((ℓ v.1 : ℚ) - (v.2 : ℕ)) * ∏ j ∈ ({v.1}ᶜ : Finset α), ((ℓ j : ℚ) + 1) :=
  (rfl)

/-- The marks are positive: the centre carries the largest of them. -/
lemma starMark_pos (v : StarIndex ℓ) : 0 < starMark ℓ v := by
  cases v with
  | none => exact Finset.prod_pos fun i _ ↦ by positivity
  | some v =>
    have hlt : ((v.2 : ℕ) : ℚ) < (ℓ v.1 : ℚ) := by exact_mod_cast v.2.isLt
    exact mul_pos (by linarith) (Finset.prod_pos fun i _ ↦ by positivity)

/-- The mark at the centre, factored along the arm `i`: it is the product of `ℓ i + 1` with the
weight `∏_{j ≠ i} (ℓ j + 1)` that the arm `i` decreases by. This is what makes the marks the value
at position `0` of the linear function that describes the arm `i`. -/
private lemma starMark_none_eq_mul_prod_compl (i : α) :
    starMark ℓ none = ((ℓ i : ℚ) + 1) * ∏ j ∈ ({i}ᶜ : Finset α), ((ℓ j : ℚ) + 1) := by
  rw [starMark_none, Finset.compl_singleton]
  exact (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm

/-- The mark at the vertex of the arm `i` at distance `s + 1` from the centre, in the shape the row
computations consume: the same weight `∏_{j ≠ i} (ℓ j + 1)`, times the value at `s + 1` of the
linear function that takes the value `ℓ i + 1` at the centre and drops by one per step. -/
private lemma starMark_some_eq_mul_prod_compl (i : α) (s : Fin (ℓ i)) :
    starMark ℓ (some ⟨i, s⟩)
      = ((ℓ i : ℚ) + 1 - ((s : ℕ) + 1)) * ∏ j ∈ ({i}ᶜ : Finset α), ((ℓ j : ℚ) + 1) := by
  rw [starMark_some]
  push_cast
  ring

section RowSums

/-! ### The rows of a star at its marks

The two computations behind the bound: the row of `starCartanMatrix` at an arm vertex annihilates
the marks, and the row at the centre evaluates to `∑ᵢ ∏_{j ≠ i} (ℓ j + 1) - (n - 2) ∏ᵢ (ℓ i + 1)`.
Both are assembled from the chain row of `TauCeti.LinearAlgebra.RootSystem.Chain`,
`TauCeti.sum_range_chainEntry_mul`, taken at an abstract weight function `g`.
-/

/-- The full row of a star at an arm vertex, in chain coordinates: the centre contributes `-g 0` at
the near end of the arm and nothing elsewhere, which is exactly the term the chain sum omits. -/
private theorem chainEntry_arm_row {n m : ℕ} (hm : m < n) (g : ℕ → ℚ) :
    (chainEntry (m + 1) 0 : ℚ) * g 0
        + ∑ s ∈ Finset.range n, (chainEntry (m + 1) (s + 1) : ℚ) * g (s + 1)
      = 2 * g (m + 1) - g m - (if m + 1 = n then 0 else g (m + 2)) := by
  simp only [chainEntry_succ_succ]
  rw [sum_range_chainEntry_mul hm]
  rcases eq_or_ne m 0 with rfl | hm0
  · rw [chainEntry_succ_left, ite_eq_left rfl]
    push_cast
    ring
  · rw [chainEntry_eq_zero (Nat.succ_ne_zero m) (fun h ↦ hm0 (by omega)) (by omega),
      ite_eq_right hm0]
    push_cast
    ring

/-- The row of a star at the centre, in chain coordinates: only the near end of each arm meets the
centre. -/
private theorem chainEntry_center_row (n : ℕ) (g : ℕ → ℚ) :
    ∑ s ∈ Finset.range n, (chainEntry 0 (s + 1) : ℚ) * g (s + 1) = if n = 0 then 0 else -g 1 := by
  match n with
  | 0 => simp
  | k + 1 =>
    rw [Finset.sum_range_succ' _ k]
    have htail : ∀ s ∈ Finset.range k, (chainEntry 0 (s + 1 + 1) : ℚ) * g (s + 1 + 1) = 0 := by
      intro s _
      rw [chainEntry_eq_zero (by omega) (by omega) (by omega)]
      norm_num
    rw [Finset.sum_congr rfl htail]
    simp

end RowSums

omit [DecidableEq α] in
/-- Splitting a sum over the vertices of a star into the centre and the arms. -/
private theorem sum_starIndex (f : StarIndex ℓ → ℚ) :
    ∑ v, f v = f none + ∑ i, ∑ s : Fin (ℓ i), f (some ⟨i, s⟩) := by
  rw [Fintype.sum_option, ← Finset.univ_sigma_univ, Finset.sum_sigma]

/-- **The rows of a star at an arm vertex annihilate the marks.** The marks are linear along each
arm, and the centre supplies exactly the value the linear function takes at position `0`, so the
three-term recurrence of a chain closes at both ends.

This is not a `simp` lemma, and neither is the companion
`TauCeti.sum_starCartanMatrix_mul_starMark_none`: the left-hand side is not in simp-normal form.
`Fintype.sum_option` splits the sum over `TauCeti.StarIndex` into the centre and the arms, and the
entry lemmas above then rewrite the summands, so `simp` has dismantled the left-hand side before
this equation could fire; the attribute reports only as a `simpNF` violation. Both rows are stated
in the shape `TauCeti.IsFiniteType.eq_zero_of_forall_mul_sum_apply_mul_nonpos` consumes, and their
call sites reach them by `rw`. -/
theorem sum_starCartanMatrix_mul_starMark_some_eq_zero (v : (i : α) × Fin (ℓ i)) :
    ∑ w, (starCartanMatrix ℓ (some v) w : ℚ) * starMark ℓ w = 0 := by
  set Q : ℚ := ∏ j ∈ ({v.1}ᶜ : Finset α), ((ℓ j : ℚ) + 1) with hQ
  set g : ℕ → ℚ := fun u ↦ ((ℓ v.1 : ℚ) + 1 - u) * Q with hg
  -- The marks along the arm of `v`, and at the centre, are the values of `g`.
  have hg0 : g 0 = starMark ℓ none := by
    rw [hg, starMark_none_eq_mul_prod_compl v.1]; norm_num [hQ]
  have hgarm : ∀ s : Fin (ℓ v.1), g ((s : ℕ) + 1) = starMark ℓ (some ⟨v.1, s⟩) := by
    intro s
    rw [hg, starMark_some_eq_mul_prod_compl]
    push_cast
    ring
  rw [sum_starIndex]
  -- Only the arm of `v` and the centre contribute.
  have harms : ∀ i ∈ Finset.univ, ∑ s : Fin (ℓ i),
      (starCartanMatrix ℓ (some v) (some ⟨i, s⟩) : ℚ) * starMark ℓ (some ⟨i, s⟩)
        = if i = v.1 then
            ∑ s ∈ Finset.range (ℓ v.1), (chainEntry ((v.2 : ℕ) + 1) (s + 1) : ℚ) * g (s + 1)
          else 0 := by
    intro i _
    rcases eq_or_ne i v.1 with rfl | hi
    · rw [ite_eq_left rfl, ← Fin.sum_univ_eq_sum_range
        (fun s ↦ (chainEntry ((v.2 : ℕ) + 1) (s + 1) : ℚ) * g (s + 1)) (ℓ v.1)]
      exact Finset.sum_congr rfl fun s _ ↦ by
        rw [starCartanMatrix_some_some_chain, ite_eq_left rfl, hgarm s]
    · refine (Finset.sum_eq_zero fun s _ ↦ ?_).trans (ite_eq_right hi).symm
      rw [starCartanMatrix_some_some_chain, ite_eq_right (Ne.symm hi)]
      norm_num
  rw [Finset.sum_congr rfl harms, Finset.sum_ite_eq' Finset.univ v.1,
    ite_eq_left (Finset.mem_univ _), starCartanMatrix_some_none_chain, ← hg0]
  rw [chainEntry_arm_row v.2.isLt g]
  -- The three-term recurrence of a linear function vanishes, and so does its truncation at the end
  -- of the arm, because the arm ends one step before the value `0`.
  rcases eq_or_ne ((v.2 : ℕ) + 1) (ℓ v.1) with hend | hend
  · have hL : ((ℓ v.1 : ℕ) : ℚ) = ((v.2 : ℕ) : ℚ) + 1 := by exact_mod_cast hend.symm
    rw [ite_eq_left hend]
    simp only [hg]
    push_cast
    linear_combination Q * hL
  · rw [ite_eq_right hend]
    simp only [hg]
    push_cast
    ring

/-- **The row of a star at the centre, evaluated at the marks.** With `n` arms and `pᵢ = ℓ i + 1`
vertices on the arm `i` counting the centre, the value is `∑ᵢ ∏_{j ≠ i} pⱼ - (n - 2) ∏ᵢ pᵢ`, that
is, `(∑ᵢ 1 / pᵢ - (n - 2)) ∏ᵢ pᵢ`. This is the only place the shape of the star is felt.

Not a `simp` lemma, for the reason given at
`TauCeti.sum_starCartanMatrix_mul_starMark_some_eq_zero`. -/
theorem sum_starCartanMatrix_mul_starMark_none :
    ∑ w, (starCartanMatrix ℓ none w : ℚ) * starMark ℓ w
      = ∑ i, (∏ j ∈ ({i}ᶜ : Finset α), ((ℓ j : ℚ) + 1))
        - ((Fintype.card α : ℚ) - 2) * ∏ i, ((ℓ i : ℚ) + 1) := by
  rw [sum_starIndex]
  have harms : ∀ i ∈ Finset.univ, ∑ s : Fin (ℓ i),
      (starCartanMatrix ℓ none (some ⟨i, s⟩) : ℚ) * starMark ℓ (some ⟨i, s⟩)
        = -((ℓ i : ℚ) * ∏ j ∈ ({i}ᶜ : Finset α), ((ℓ j : ℚ) + 1)) := by
    intro i _
    set Q : ℚ := ∏ j ∈ ({i}ᶜ : Finset α), ((ℓ j : ℚ) + 1) with hQ
    set g : ℕ → ℚ := fun u ↦ ((ℓ i : ℚ) + 1 - u) * Q with hg
    have hgarm : ∀ s : Fin (ℓ i), g ((s : ℕ) + 1) = starMark ℓ (some ⟨i, s⟩) := by
      intro s
      rw [hg, starMark_some_eq_mul_prod_compl]
      push_cast
      ring
    have hstep : ∑ s : Fin (ℓ i), (starCartanMatrix ℓ none (some ⟨i, s⟩) : ℚ)
          * starMark ℓ (some ⟨i, s⟩)
        = ∑ s : Fin (ℓ i), (chainEntry 0 ((s : ℕ) + 1) : ℚ) * g ((s : ℕ) + 1) :=
      Finset.sum_congr rfl fun s _ ↦ by rw [starCartanMatrix_none_some_chain, hgarm s]
    rw [hstep, Fin.sum_univ_eq_sum_range (fun s ↦ (chainEntry 0 (s + 1) : ℚ) * g (s + 1)) (ℓ i),
      chainEntry_center_row]
    rcases eq_or_ne (ℓ i) 0 with h0 | h0
    · rw [ite_eq_left h0, h0]
      norm_num
    · rw [ite_eq_right h0]
      simp only [hg]
      push_cast
      ring
  rw [Finset.sum_congr rfl harms, starCartanMatrix_none_none]
  -- `ℓ i · ∏_{j ≠ i} pⱼ = ∏ⱼ pⱼ - ∏_{j ≠ i} pⱼ`, so the arms subtract
  -- `n · ∏ⱼ pⱼ - ∑ᵢ ∏_{j ≠ i} pⱼ`.
  have hsplit : ∀ i ∈ Finset.univ, -((ℓ i : ℚ) * ∏ j ∈ ({i}ᶜ : Finset α), ((ℓ j : ℚ) + 1))
      = (∏ j ∈ ({i}ᶜ : Finset α), ((ℓ j : ℚ) + 1)) - ∏ j, ((ℓ j : ℚ) + 1) := by
    intro i _
    have hprod := starMark_none_eq_mul_prod_compl (ℓ := ℓ) i
    rw [starMark_none] at hprod
    rw [hprod]
    ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, starMark_none]
  push_cast
  ring

/-- **The fork bound.** A star of finite type with `n` arms carrying `ℓ i` vertices each, so `pᵢ =
ℓ i + 1` vertices counting the centre, satisfies `∑ᵢ 1 / pᵢ > n - 2`.

For three arms this is `1 / p + 1 / q + 1 / r > 1`, the inequality that leaves only the forks of
types `D` and `E`; see
`TauCeti.eq_zero_or_eq_one_one_or_eq_one_two_le_four_of_isFiniteType_star_three`. -/
theorem card_sub_two_lt_sum_inv_of_isFiniteType_star (h : IsFiniteType (starCartanMatrix ℓ)) :
    (Fintype.card α : ℚ) - 2 < ∑ i, ((ℓ i : ℚ) + 1)⁻¹ := by
  rw [← not_le]
  intro hle
  -- Under the negated bound the marks are subdominant, so they vanish; but they are positive.
  refine absurd
    (congrFun (h.eq_zero_of_forall_mul_sum_apply_mul_nonpos (x := starMark ℓ) ?_) none) ?_
  · rintro (_ | v)
    · rw [sum_starCartanMatrix_mul_starMark_none]
      have hprod : (0 : ℚ) < ∏ i, ((ℓ i : ℚ) + 1) := Finset.prod_pos fun i _ ↦ by positivity
      -- The `i`-th term of the sum, cleared of its denominator, is the weight of the arm `i`.
      have hterm : ∀ i ∈ Finset.univ, ((ℓ i : ℚ) + 1)⁻¹ * ∏ j, ((ℓ j : ℚ) + 1)
          = ∏ j ∈ ({i}ᶜ : Finset α), ((ℓ j : ℚ) + 1) := by
        intro i _
        rw [← starMark_none, starMark_none_eq_mul_prod_compl i,
          inv_mul_cancel_left₀ (by positivity)]
      have hsum : (∑ i, ((ℓ i : ℚ) + 1)⁻¹) * ∏ j, ((ℓ j : ℚ) + 1)
          = ∑ i, ∏ j ∈ ({i}ᶜ : Finset α), ((ℓ j : ℚ) + 1) := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl hterm
      have hkey : ∑ i, (∏ j ∈ ({i}ᶜ : Finset α), ((ℓ j : ℚ) + 1))
          ≤ ((Fintype.card α : ℚ) - 2) * ∏ i, ((ℓ i : ℚ) + 1) := by
        rw [← hsum]
        exact mul_le_mul_of_nonneg_right hle hprod.le
      nlinarith [starMark_pos (ℓ := ℓ) none]
    · rw [sum_starCartanMatrix_mul_starMark_some_eq_zero v, mul_zero]
  · exact (starMark_pos (ℓ := ℓ) none).ne'

/-- The contrapositive of `TauCeti.card_sub_two_lt_sum_inv_of_isFiniteType_star`: a star violating
the fork bound is not of finite type.

This is the shape the classification consumes. A candidate diagram is excluded by exhibiting an
embedded star with `∑ᵢ 1 / pᵢ ≤ n - 2`, that is, by `TauCeti.IsFiniteType.submatrix` along an
injection `e` with `A.submatrix e e = starCartanMatrix ℓ`. -/
theorem not_isFiniteType_starCartanMatrix_of_sum_inv_le
    (h : ∑ i, ((ℓ i : ℚ) + 1)⁻¹ ≤ (Fintype.card α : ℚ) - 2) :
    ¬ IsFiniteType (starCartanMatrix ℓ) := fun hft ↦
  absurd (card_sub_two_lt_sum_inv_of_isFiniteType_star hft) (not_lt.2 h)

section Three

/-! ### The three-armed case

The classification meets the bound at a branch vertex, where there are exactly three arms and the
inequality reads `1 / p + 1 / q + 1 / r > 1`. Its solutions are the chains, the forks of type `D`,
and the three exceptional shapes.
-/

/-- The fork bound written out for three arms: `n - 2` is `1`, and the sum has three terms. -/
private lemma card_sub_two_lt_sum_inv_three_iff (a b c : ℕ) :
    (Fintype.card (Fin 3) : ℚ) - 2 < ∑ i, (((![a, b, c] : Fin 3 → ℕ) i : ℚ) + 1)⁻¹
      ↔ 1 < ((a : ℚ) + 1)⁻¹ + ((b : ℚ) + 1)⁻¹ + ((c : ℚ) + 1)⁻¹ := by
  have hcard : (Fintype.card (Fin 3) : ℚ) - 2 = 1 := by norm_num
  rw [hcard, Fin.sum_univ_three]
  simp

/-- **The fork bound for three arms**, `1 / p + 1 / q + 1 / r > 1`. -/
theorem one_lt_sum_inv_of_isFiniteType_star_three {a b c : ℕ}
    (h : IsFiniteType (starCartanMatrix ![a, b, c])) :
    1 < ((a : ℚ) + 1)⁻¹ + ((b : ℚ) + 1)⁻¹ + ((c : ℚ) + 1)⁻¹ :=
  (card_sub_two_lt_sum_inv_three_iff a b c).1 (card_sub_two_lt_sum_inv_of_isFiniteType_star h)

/-- The contrapositive of `TauCeti.one_lt_sum_inv_of_isFiniteType_star_three`: a three-armed star
with `1 / p + 1 / q + 1 / r ≤ 1` is not of finite type. -/
theorem not_isFiniteType_starCartanMatrix_three_of_sum_inv_le_one {a b c : ℕ}
    (h : ((a : ℚ) + 1)⁻¹ + ((b : ℚ) + 1)⁻¹ + ((c : ℚ) + 1)⁻¹ ≤ 1) :
    ¬ IsFiniteType (starCartanMatrix ![a, b, c]) := by
  refine not_isFiniteType_starCartanMatrix_of_sum_inv_le ?_
  rw [← not_lt, card_sub_two_lt_sum_inv_three_iff]
  exact not_lt.2 h

/-- **The admissible three-armed shapes.** A star of finite type whose three arms carry
`a ≤ b ≤ c` vertices besides the centre is a chain (`a = 0`), a fork of type `D` (`a = b = 1`), or
one of `E₆`, `E₇`, `E₈` (`a = 1`, `b = 2` and `c ≤ 4`).

This is the exclusion half of the classification of forks. The converse, that each of these shapes
is the diagram of an actual root system, is the separate realization target of the same layer and
is not proved here. -/
theorem eq_zero_or_eq_one_one_or_eq_one_two_le_four_of_isFiniteType_star_three
    {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c)
    (h : IsFiniteType (starCartanMatrix ![a, b, c])) :
    a = 0 ∨ (a = 1 ∧ b = 1) ∨ (a = 1 ∧ b = 2 ∧ c ≤ 4) := by
  -- With `p = a + 1 ≤ q = b + 1 ≤ r = c + 1` the bound is Mathlib's ADE inequality, whose
  -- solutions `ADEInequality.lt_three`, `.lt_four` and `.lt_six` cut out one at a time.
  have hsum : 1 < ADEInequality.sumInv {a.succPNat, b.succPNat, c.succPNat} := by
    rw [ADEInequality.sumInv_pqr]
    push_cast [Nat.succPNat_coe]
    exact one_lt_sum_inv_of_isFiniteType_star_three h
  have hpq : a.succPNat ≤ b.succPNat := Nat.succPNat_le_succPNat.2 hab
  have hqr : b.succPNat ≤ c.succPNat := Nat.succPNat_le_succPNat.2 hbc
  have ha : a + 1 < 3 := ADEInequality.lt_three hpq hqr hsum
  rcases Nat.lt_or_ge a 1 with ha0 | ha1
  · exact Or.inl (by omega)
  obtain rfl : a = 1 := by omega
  have htwo : Nat.succPNat 1 = 2 := rfl
  rw [htwo] at hsum
  have hb : b + 1 < 4 := ADEInequality.lt_four hqr hsum
  rcases Nat.lt_or_ge b 2 with hb1 | hb2
  · exact Or.inr (Or.inl ⟨rfl, by omega⟩)
  obtain rfl : b = 2 := by omega
  have hthree : Nat.succPNat 2 = 3 := rfl
  rw [hthree] at hsum
  have hc : c + 1 < 6 := ADEInequality.lt_six hsum
  exact Or.inr (Or.inr ⟨rfl, rfl, by omega⟩)

/-- The extended Dynkin diagram `Ẽ₆`, the star with three arms of two vertices each, is not of
finite type: its marks are a null vector. -/
theorem not_isFiniteType_affineE₆ : ¬ IsFiniteType (starCartanMatrix ![2, 2, 2]) :=
  not_isFiniteType_starCartanMatrix_three_of_sum_inv_le_one (by norm_num)

/-- The extended Dynkin diagram `Ẽ₇`, the star with arms of one, three and three vertices, is not
of finite type. -/
theorem not_isFiniteType_affineE₇ : ¬ IsFiniteType (starCartanMatrix ![1, 3, 3]) :=
  not_isFiniteType_starCartanMatrix_three_of_sum_inv_le_one (by norm_num)

/-- The extended Dynkin diagram `Ẽ₈`, the star with arms of one, two and five vertices, is not of
finite type. -/
theorem not_isFiniteType_affineE₈ : ¬ IsFiniteType (starCartanMatrix ![1, 2, 5]) :=
  not_isFiniteType_starCartanMatrix_three_of_sum_inv_le_one (by norm_num)

end Three

end TauCeti
