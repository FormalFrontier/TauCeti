/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Basic

public section

/-!
# The fork bound for finite-type Cartan matrices

A connected finite-type diagram is a tree whose vertices have degree at most three. Such a tree may
branch at several vertices, but choosing one branch vertex exhibits a **star** as a subdiagram: that
vertex as the centre, with three arms hanging off it. Which stars survive is the last local
constraint of the Cartan-Killing classification, and it is an arithmetic one. Writing
`p, q, r` for the numbers of vertices on the three arms *counting the centre*, a star of finite
type satisfies

`1 / p + 1 / q + 1 / r > 1`,

whose solutions with `p ≤ q ≤ r` are `(1, q, r)`, `(2, 2, r)`, `(2, 3, 3)`, `(2, 3, 4)` and
`(2, 3, 5)` - the chains `Aₙ`, the forks `Dₙ`, and `E₆`, `E₇`, `E₈`.

This file builds the star as a matrix, `TauCeti.starCartanMatrix`, over an arbitrary finite index
type of arms, and proves the bound. The elimination tool is a new one, living with the others in
`TauCeti.LinearAlgebra.RootSystem.FiniteType.Basic`: a finite-type matrix admits no nonzero
**subdominant** vector, one whose every coordinate `xᵢ` has `xᵢ · (A x)ᵢ ≤ 0`
(`TauCeti.IsFiniteType.eq_zero_of_forall_mul_sum_nonpos`), because the symmetrized quadratic form
evaluates at such a vector to `∑ᵢ dᵢ xᵢ (A x)ᵢ ≤ 0`. The certificate exhibited for a star is its
vector of **marks** `TauCeti.starMark`, which decreases linearly along each arm, from `p q r` at
the centre down to `q r` at the far end of the first arm. The marks are annihilated by the matrix
at every arm vertex, and at the centre they take the value `qr + pr + pq - pqr`, which is `≤ 0`
exactly when the fork bound fails.

The three critical stars, where the marks are a genuine null vector, are the extended Dynkin
diagrams `Ẽ₆ = T(3, 3, 3)`, `Ẽ₇ = T(2, 4, 4)` and `Ẽ₈ = T(2, 3, 6)`; they are recorded as
corollaries. Since the argument is uniform in the number of arms, the `n`-armed form of the bound,
`∑ᵢ 1 / pᵢ > n - 2`, comes out at the same time, and at `n = 4` with every `pᵢ = 2` it reproves the
exclusion of `D̃₄` that `TauCeti.not_isFiniteType_affineD₄` gets from the degree bound.

## Main definitions

* `TauCeti.chainEntry`: the Cartan-matrix entry of a chain, read off the two positions along it.
* `TauCeti.StarIndex`: the vertices of a star - a centre `none`, and `ℓ i` further vertices on the
  arm `i`, the vertex `some ⟨i, t⟩` sitting at distance `t + 1` from the centre.
* `TauCeti.starCartanMatrix`: the Cartan matrix of a star, simply laced by construction.
* `TauCeti.starMark`: the marks of a star, the test vector the bound is proved with.

## Main results

* `TauCeti.card_sub_two_lt_sum_inv_of_isFiniteType_star` and
  `TauCeti.not_isFiniteType_starCartanMatrix`: **the fork bound**, `∑ᵢ 1 / (ℓ i + 1) > n - 2` for a
  star of finite type with `n` arms, and its contrapositive.
* `TauCeti.card_sub_two_lt_sum_inv_of_star_submatrix`: the bound in the form a diagram containing a
  star meets it, through `TauCeti.IsFiniteType.submatrix`.
* `TauCeti.arms_of_isFiniteType_star_three`: **the admissible three-armed shapes**. A finite-type
  star with arms of `a ≤ b ≤ c` further vertices has `a = 0` (a chain), or `a = b = 1` (a fork of
  type `D`), or `a = 1`, `b = 2` and `c ≤ 4` (types `E₆`, `E₇`, `E₈`).
* `TauCeti.not_isFiniteType_starCartanMatrix_affineE₆`, `...E₇`, `...E₈`: the three critical stars
  are not of finite type.

## References

This file supplies the "chain/fork length constraints" step of the classification of finite-type
Cartan matrices, Layer 5 of `TauCetiRoadmap/RepresentationTheory/RootSystems/README.md`. See
J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §11.4, step (7), where
the inequality `1/p + 1/q + 1/r > 1` is obtained from the same linear weighting of the arms, and
Bourbaki, *Lie Groups and Lie Algebras, Chapters 4-6*, Ch. VI §4.
-/

open scoped Matrix

namespace TauCeti

/-- The Cartan-matrix entry of a **chain** between the positions `s` and `t` along it: `2` on the
diagonal, `-1` between consecutive positions, and `0` otherwise. Every diagram in this file is
simply laced, so this single function describes all of its edges. -/
def chainEntry (s t : ℕ) : ℤ :=
  if s = t then 2 else if s = t + 1 then -1 else if t = s + 1 then -1 else 0

-- `(rfl)`, not `rfl`: the bodies of the definitions in this file are deliberately left unexposed,
-- and the parenthesised form keeps these equations out of the exported definitional-equality check.
lemma chainEntry_def (s t : ℕ) :
    chainEntry s t = if s = t then 2 else if s = t + 1 then -1 else if t = s + 1 then -1 else 0 :=
  (rfl)

@[simp] lemma chainEntry_self (s : ℕ) : chainEntry s s = 2 := by simp [chainEntry]

@[simp] lemma chainEntry_succ_left (s : ℕ) : chainEntry (s + 1) s = -1 := by
  unfold chainEntry; split_ifs <;> omega

@[simp] lemma chainEntry_succ_right (s : ℕ) : chainEntry s (s + 1) = -1 := by
  unfold chainEntry; split_ifs <;> omega

/-- Away from the diagonal and its two neighbours a chain has no entry. -/
lemma chainEntry_eq_zero {s t : ℕ} (h1 : s ≠ t) (h2 : s ≠ t + 1) (h3 : t ≠ s + 1) :
    chainEntry s t = 0 := by
  unfold chainEntry; split_ifs <;> omega

/-- Shifting both positions of a chain by one leaves the entry unchanged: only the difference of
the positions matters. -/
@[simp] lemma chainEntry_succ_succ (s t : ℕ) : chainEntry (s + 1) (t + 1) = chainEntry s t := by
  unfold chainEntry; split_ifs <;> omega

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

@[simp] lemma starCartanMatrix_none_none : starCartanMatrix ℓ none none = 2 := (rfl)

@[simp] lemma starCartanMatrix_none_some (w : (i : α) × Fin (ℓ i)) :
    starCartanMatrix ℓ none (some w) = chainEntry 0 ((w.2 : ℕ) + 1) := (rfl)

@[simp] lemma starCartanMatrix_some_none (v : (i : α) × Fin (ℓ i)) :
    starCartanMatrix ℓ (some v) none = chainEntry ((v.2 : ℕ) + 1) 0 := (rfl)

@[simp] lemma starCartanMatrix_some_some (v w : (i : α) × Fin (ℓ i)) :
    starCartanMatrix ℓ (some v) (some w)
      = if v.1 = w.1 then chainEntry ((v.2 : ℕ) + 1) ((w.2 : ℕ) + 1) else 0 := (rfl)

variable [Fintype α]

/-- The **marks** of a star: the value `∏ᵢ (ℓ i + 1)` at the centre, decreasing linearly along the
arm `i` in steps of `∏_{j ≠ i} (ℓ j + 1)`, down to that step itself at the far end of the arm.

These are the marks of an extended Dynkin diagram in the critical cases, and the same formula
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
lemma starMark_none_eq (i : α) :
    starMark ℓ none = ((ℓ i : ℚ) + 1) * ∏ j ∈ ({i}ᶜ : Finset α), ((ℓ j : ℚ) + 1) := by
  rw [starMark_none, Finset.compl_singleton]
  exact (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm

section RowSums

/-! ### The rows of a star at its marks

The two computations behind the bound: the row of `starCartanMatrix` at an arm vertex annihilates
the marks, and the row at the centre evaluates to `∑ᵢ ∏_{j ≠ i} (ℓ j + 1) - (n - 2) ∏ᵢ (ℓ i + 1)`.
Both are assembled from the same two facts about a chain, proved first for an abstract linear
weight function `g`.
-/

/-- The chain sum, in the shape both rows consume: along `n` positions `1, …, n`, the entries at
the position `m` collect `2 g (m + 1) - g m - g (m + 2)`, the term `g m` being absent at `m = 0`
(where it is the centre, summed separately) and `g (m + 2)` at the far end. -/
private theorem sum_range_chainEntry_mul {n m : ℕ} (hm : m < n) (g : ℕ → ℚ) :
    ∑ s ∈ Finset.range n, (chainEntry m s : ℚ) * g (s + 1)
      = 2 * g (m + 1) - (if m = 0 then 0 else g m)
        - (if m + 1 = n then 0 else g (m + 2)) := by
  have key : ∀ s ∈ Finset.range n, ((chainEntry m s : ℤ) : ℚ) * g (s + 1)
      = (if s = m then 2 * g (m + 1) else 0) + (if s + 1 = m then -g m else 0)
        + (if s = m + 1 then -g (m + 2) else 0) := by
    intro s _
    by_cases h1 : s = m
    · subst h1
      rw [if_pos rfl, if_neg (by omega : ¬ (s + 1 = s)), if_neg (by omega : ¬ (s = s + 1)),
        chainEntry_self]
      norm_num
    by_cases h2 : s + 1 = m
    · subst h2
      rw [if_neg h1, if_pos rfl, if_neg (by omega : ¬ (s = s + 1 + 1)), chainEntry_succ_left]
      norm_num
    by_cases h3 : s = m + 1
    · subst h3
      rw [if_neg h1, if_neg h2, if_pos rfl, chainEntry_succ_right]
      norm_num
    · rw [if_neg h1, if_neg h2, if_neg h3,
        chainEntry_eq_zero (fun h ↦ h1 h.symm) (fun h ↦ h2 h.symm) h3]
      norm_num
  rw [Finset.sum_congr rfl key, Finset.sum_add_distrib, Finset.sum_add_distrib]
  have h1 : ∑ s ∈ Finset.range n, (if s = m then 2 * g (m + 1) else 0) = 2 * g (m + 1) := by
    rw [Finset.sum_ite_eq' (Finset.range n) m fun _ ↦ 2 * g (m + 1)]
    simp [Finset.mem_range, hm]
  have h3 : ∑ s ∈ Finset.range n, (if s = m + 1 then -g (m + 2) else 0)
      = -(if m + 1 = n then 0 else g (m + 2)) := by
    rw [Finset.sum_ite_eq' (Finset.range n) (m + 1) fun _ ↦ -g (m + 2)]
    by_cases hn : m + 1 = n
    · simp [Finset.mem_range, hn]
    · rw [if_pos (Finset.mem_range.2 (by omega)), if_neg hn]
  have h2 : ∑ s ∈ Finset.range n, (if s + 1 = m then -g m else 0)
      = -(if m = 0 then 0 else g m) := by
    match m with
    | 0 => simp
    | k + 1 =>
      have hcongr : ∀ s ∈ Finset.range n, (if s + 1 = k + 1 then -g (k + 1) else 0)
          = (if s = k then -g (k + 1) else 0) := by
        intro s _
        by_cases h : s = k <;> simp [h]
      rw [Finset.sum_congr rfl hcongr,
        Finset.sum_ite_eq' (Finset.range n) k fun _ ↦ -g (k + 1)]
      rw [if_pos (Finset.mem_range.2 (show k < n by omega)), if_neg (Nat.succ_ne_zero k)]
  rw [h1, h2, h3]
  ring

/-- The full row of a star at an arm vertex, in chain coordinates: the centre contributes `-g 0` at
the near end of the arm and nothing elsewhere, which is exactly the term the chain sum omits. -/
private theorem chainEntry_arm_row {n m : ℕ} (hm : m < n) (g : ℕ → ℚ) :
    (chainEntry (m + 1) 0 : ℚ) * g 0
        + ∑ s ∈ Finset.range n, (chainEntry (m + 1) (s + 1) : ℚ) * g (s + 1)
      = 2 * g (m + 1) - g m - (if m + 1 = n then 0 else g (m + 2)) := by
  simp only [chainEntry_succ_succ]
  rw [sum_range_chainEntry_mul hm]
  rcases eq_or_ne m 0 with rfl | hm0
  · rw [chainEntry_succ_left, if_pos rfl]
    push_cast
    ring
  · rw [chainEntry_eq_zero (Nat.succ_ne_zero m) (fun h ↦ hm0 (by omega)) (by omega), if_neg hm0]
    push_cast
    ring

/-- The row of a star at the centre, in chain coordinates: only the near end of each arm meets the
centre. -/
private theorem chainEntry_centre_row (n : ℕ) (g : ℕ → ℚ) :
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
    simp [chainEntry]

end RowSums

omit [DecidableEq α] in
/-- Splitting a sum over the vertices of a star into the centre and the arms. -/
private theorem sum_starIndex (f : StarIndex ℓ → ℚ) :
    ∑ v, f v = f none + ∑ i, ∑ s : Fin (ℓ i), f (some ⟨i, s⟩) := by
  rw [Fintype.sum_option, ← Finset.univ_sigma_univ, Finset.sum_sigma]

/-- **The rows of a star at an arm vertex annihilate the marks.** The marks are linear along each
arm, and the centre supplies exactly the value the linear function takes at position `0`, so the
three-term recurrence of a chain closes at both ends. -/
theorem sum_starCartanMatrix_mul_starMark_some (v : (i : α) × Fin (ℓ i)) :
    ∑ w, (starCartanMatrix ℓ (some v) w : ℚ) * starMark ℓ w = 0 := by
  set Q : ℚ := ∏ j ∈ ({v.1}ᶜ : Finset α), ((ℓ j : ℚ) + 1) with hQ
  set g : ℕ → ℚ := fun u ↦ ((ℓ v.1 : ℚ) + 1 - u) * Q with hg
  -- The marks along the arm of `v`, and at the centre, are the values of `g`.
  have hg0 : g 0 = starMark ℓ none := by rw [hg, starMark_none_eq v.1]; norm_num [hQ]
  have hgarm : ∀ s : Fin (ℓ v.1), g ((s : ℕ) + 1) = starMark ℓ (some ⟨v.1, s⟩) := by
    intro s
    rw [hg, starMark_some]
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
    · rw [if_pos rfl, ← Fin.sum_univ_eq_sum_range
        (fun s ↦ (chainEntry ((v.2 : ℕ) + 1) (s + 1) : ℚ) * g (s + 1)) (ℓ v.1)]
      exact Finset.sum_congr rfl fun s _ ↦ by
        rw [starCartanMatrix_some_some, if_pos rfl, hgarm s]
    · refine (Finset.sum_eq_zero fun s _ ↦ ?_).trans (if_neg hi).symm
      simp [starCartanMatrix_some_some, Ne.symm hi]
  rw [Finset.sum_congr rfl harms, Finset.sum_ite_eq' Finset.univ v.1, if_pos (Finset.mem_univ _),
    starCartanMatrix_some_none, ← hg0]
  rw [chainEntry_arm_row v.2.isLt g]
  -- The three-term recurrence of a linear function vanishes, and so does its truncation at the end
  -- of the arm, because the arm ends one step before the value `0`.
  rcases eq_or_ne ((v.2 : ℕ) + 1) (ℓ v.1) with hend | hend
  · have hL : ((ℓ v.1 : ℕ) : ℚ) = ((v.2 : ℕ) : ℚ) + 1 := by exact_mod_cast hend.symm
    rw [if_pos hend]
    simp only [hg]
    push_cast
    linear_combination Q * hL
  · rw [if_neg hend]
    simp only [hg]
    push_cast
    ring

/-- **The row of a star at the centre, evaluated at the marks.** With `n` arms and `pᵢ = ℓ i + 1`
vertices on the arm `i` counting the centre, the value is `∑ᵢ ∏_{j ≠ i} pⱼ - (n - 2) ∏ᵢ pᵢ`, that
is, `(∑ᵢ 1 / pᵢ - (n - 2)) ∏ᵢ pᵢ`. This is the only place the shape of the star is felt. -/
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
      rw [hg, starMark_some]
      push_cast
      ring
    have hstep : ∑ s : Fin (ℓ i), (starCartanMatrix ℓ none (some ⟨i, s⟩) : ℚ)
          * starMark ℓ (some ⟨i, s⟩)
        = ∑ s : Fin (ℓ i), (chainEntry 0 ((s : ℕ) + 1) : ℚ) * g ((s : ℕ) + 1) :=
      Finset.sum_congr rfl fun s _ ↦ by rw [starCartanMatrix_none_some, hgarm s]
    rw [hstep, Fin.sum_univ_eq_sum_range (fun s ↦ (chainEntry 0 (s + 1) : ℚ) * g (s + 1)) (ℓ i),
      chainEntry_centre_row]
    rcases eq_or_ne (ℓ i) 0 with h0 | h0
    · rw [if_pos h0, h0]
      norm_num
    · rw [if_neg h0]
      simp only [hg]
      push_cast
      ring
  rw [Finset.sum_congr rfl harms, starCartanMatrix_none_none]
  -- `ℓ i · ∏_{j ≠ i} pⱼ = ∏ⱼ pⱼ - ∏_{j ≠ i} pⱼ`, so the arms subtract
  -- `n · ∏ⱼ pⱼ - ∑ᵢ ∏_{j ≠ i} pⱼ`.
  have hsplit : ∀ i ∈ Finset.univ, -((ℓ i : ℚ) * ∏ j ∈ ({i}ᶜ : Finset α), ((ℓ j : ℚ) + 1))
      = (∏ j ∈ ({i}ᶜ : Finset α), ((ℓ j : ℚ) + 1)) - ∏ j, ((ℓ j : ℚ) + 1) := by
    intro i _
    have hprod := starMark_none_eq (ℓ := ℓ) i
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
types `D` and `E`; see `TauCeti.arms_of_isFiniteType_star_three`. -/
theorem card_sub_two_lt_sum_inv_of_isFiniteType_star (h : IsFiniteType (starCartanMatrix ℓ)) :
    (Fintype.card α : ℚ) - 2 < ∑ i, ((ℓ i : ℚ) + 1)⁻¹ := by
  rw [← not_le]
  intro hle
  -- Under the negated bound the marks are subdominant, so they vanish; but they are positive.
  refine absurd (congrFun (h.eq_zero_of_forall_mul_sum_nonpos (x := starMark ℓ) ?_) none) ?_
  · rintro (_ | v)
    · rw [sum_starCartanMatrix_mul_starMark_none]
      have hprod : (0 : ℚ) < ∏ i, ((ℓ i : ℚ) + 1) := Finset.prod_pos fun i _ ↦ by positivity
      have hterm : ∀ i ∈ Finset.univ, ((ℓ i : ℚ) + 1)⁻¹ * ∏ j, ((ℓ j : ℚ) + 1)
          = ∏ j ∈ ({i}ᶜ : Finset α), ((ℓ j : ℚ) + 1) := by
        intro i _
        rw [Finset.compl_singleton, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
          ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]
      have hsum : (∑ i, ((ℓ i : ℚ) + 1)⁻¹) * ∏ j, ((ℓ j : ℚ) + 1)
          = ∑ i, ∏ j ∈ ({i}ᶜ : Finset α), ((ℓ j : ℚ) + 1) := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl hterm
      have hkey : ∑ i, (∏ j ∈ ({i}ᶜ : Finset α), ((ℓ j : ℚ) + 1))
          ≤ ((Fintype.card α : ℚ) - 2) * ∏ i, ((ℓ i : ℚ) + 1) := by
        rw [← hsum]
        exact mul_le_mul_of_nonneg_right hle hprod.le
      nlinarith [starMark_pos (ℓ := ℓ) none]
    · rw [sum_starCartanMatrix_mul_starMark_some v, mul_zero]
  · exact (starMark_pos (ℓ := ℓ) none).ne'

/-- The contrapositive of `TauCeti.card_sub_two_lt_sum_inv_of_isFiniteType_star`: a star violating
the fork bound is not of finite type. -/
theorem not_isFiniteType_starCartanMatrix
    (h : ∑ i, ((ℓ i : ℚ) + 1)⁻¹ ≤ (Fintype.card α : ℚ) - 2) :
    ¬ IsFiniteType (starCartanMatrix ℓ) := fun hft ↦
  absurd (card_sub_two_lt_sum_inv_of_isFiniteType_star hft) (not_lt.2 h)

/-- **The fork bound for a diagram containing a star.** A principal submatrix of a finite-type
matrix is of finite type, so a diagram in which a star sits as a full subdiagram inherits the
bound. This is the shape the classification consumes: a candidate diagram is excluded by exhibiting
one embedded star with `∑ᵢ 1 / pᵢ ≤ n - 2`. -/
theorem card_sub_two_lt_sum_inv_of_star_submatrix {B : Type*} [Fintype B] {A : Matrix B B ℤ}
    (h : IsFiniteType A) {e : StarIndex ℓ → B} (he : Function.Injective e)
    (heq : A.submatrix e e = starCartanMatrix ℓ) :
    (Fintype.card α : ℚ) - 2 < ∑ i, ((ℓ i : ℚ) + 1)⁻¹ :=
  card_sub_two_lt_sum_inv_of_isFiniteType_star (heq ▸ h.submatrix he)

section Three

/-! ### The three-armed case

The classification meets the bound at a branch vertex, where there are exactly three arms and the
inequality reads `1 / p + 1 / q + 1 / r > 1`. Its solutions are the chains, the forks of type `D`,
and the three exceptional shapes.
-/

/-- The arithmetic behind the three-armed case: the positive solutions of `qr + pr + pq > pqr`
with `1 ≤ p ≤ q ≤ r` are `p = 1`, `(p, q) = (2, 2)`, and `(p, q) = (2, 3)` with `r ≤ 5`. -/
private theorem three_arm_arith {p q r : ℕ} (hp : 1 ≤ p) (hpq : p ≤ q) (hqr : q ≤ r)
    (h : p * (q * r) < q * r + p * r + p * q) :
    p = 1 ∨ (p = 2 ∧ q = 2) ∨ (p = 2 ∧ q = 3 ∧ r ≤ 5) := by
  -- Three arms of three or more vertices each already exhaust the form: `pqr ≥ 3qr ≥ qr + pr + pq`.
  have hp2 : p ≤ 2 := by
    by_contra hc
    have h1 : p * r ≤ q * r := Nat.mul_le_mul_right r hpq
    have h2 : p * q ≤ q * r := Nat.mul_le_mul hpq hqr
    have h3 : 3 * (q * r) ≤ p * (q * r) := Nat.mul_le_mul_right (q * r) (by omega)
    linarith
  rcases Nat.lt_or_ge p 2 with hp1 | hp1
  · exact Or.inl (by omega)
  obtain rfl : p = 2 := by omega
  -- With `p = 2` the form reads `qr < 2r + 2q ≤ 4r`, so `q ≤ 3`.
  have hq3 : q ≤ 3 := by
    by_contra hc
    have h4 : 4 * r ≤ q * r := Nat.mul_le_mul_right r (by omega)
    linarith
  rcases Nat.lt_or_ge q 3 with hq2 | hq2
  · exact Or.inr (Or.inl ⟨rfl, by omega⟩)
  obtain rfl : q = 3 := by omega
  exact Or.inr (Or.inr ⟨rfl, rfl, by omega⟩)

/-- **The admissible three-armed shapes.** A star of finite type whose three arms carry
`a ≤ b ≤ c` vertices besides the centre is a chain (`a = 0`), a fork of type `D` (`a = b = 1`), or
one of `E₆`, `E₇`, `E₈` (`a = 1`, `b = 2` and `c ≤ 4`).

This is the exclusion half of the classification of forks. The converse, that each of these shapes
is the diagram of an actual root system, is the separate realization target of the same layer and
is not proved here. -/
theorem arms_of_isFiniteType_star_three {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c)
    (h : IsFiniteType (starCartanMatrix ![a, b, c])) :
    a = 0 ∨ (a = 1 ∧ b = 1) ∨ (a = 1 ∧ b = 2 ∧ c ≤ 4) := by
  have hbound := card_sub_two_lt_sum_inv_of_isFiniteType_star h
  rw [show (Fintype.card (Fin 3) : ℚ) = 3 from by norm_num, Fin.sum_univ_three] at hbound
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons] at hbound
  -- Clear the denominators: the bound is `qr + pr + pq > pqr` for `p = a + 1` and so on.
  have hpa : (0 : ℚ) < (a : ℚ) + 1 := by positivity
  have hpb : (0 : ℚ) < (b : ℚ) + 1 := by positivity
  have hpc : (0 : ℚ) < (c : ℚ) + 1 := by positivity
  have hclear : ((b : ℚ) + 1) * ((c : ℚ) + 1) + ((a : ℚ) + 1) * ((c : ℚ) + 1)
      + ((a : ℚ) + 1) * ((b : ℚ) + 1) > ((a : ℚ) + 1) * (((b : ℚ) + 1) * ((c : ℚ) + 1)) := by
    have := mul_lt_mul_of_pos_right hbound (mul_pos hpa (mul_pos hpb hpc))
    field_simp at this
    linarith
  have hnat : (b + 1) * (c + 1) + (a + 1) * (c + 1) + (a + 1) * (b + 1)
      > (a + 1) * ((b + 1) * (c + 1)) := by exact_mod_cast hclear
  rcases three_arm_arith (Nat.le_add_left 1 a) (by omega) (by omega) hnat with
    h1 | ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
  · exact Or.inl (by omega)
  · exact Or.inr (Or.inl ⟨by omega, by omega⟩)
  · exact Or.inr (Or.inr ⟨by omega, by omega, by omega⟩)

/-- The extended Dynkin diagram `Ẽ₆`, the star with three arms of two vertices each, is not of
finite type: its marks are a null vector. -/
theorem not_isFiniteType_starCartanMatrix_affineE₆ :
    ¬ IsFiniteType (starCartanMatrix ![2, 2, 2]) := by
  refine not_isFiniteType_starCartanMatrix ?_
  rw [show (Fintype.card (Fin 3) : ℚ) = 3 from by norm_num, Fin.sum_univ_three]
  norm_num [Matrix.cons_val_two, Matrix.tail_cons]

/-- The extended Dynkin diagram `Ẽ₇`, the star with arms of one, three and three vertices, is not
of finite type. -/
theorem not_isFiniteType_starCartanMatrix_affineE₇ :
    ¬ IsFiniteType (starCartanMatrix ![1, 3, 3]) := by
  refine not_isFiniteType_starCartanMatrix ?_
  rw [show (Fintype.card (Fin 3) : ℚ) = 3 from by norm_num, Fin.sum_univ_three]
  norm_num [Matrix.cons_val_two, Matrix.tail_cons]

/-- The extended Dynkin diagram `Ẽ₈`, the star with arms of one, two and five vertices, is not of
finite type. -/
theorem not_isFiniteType_starCartanMatrix_affineE₈ :
    ¬ IsFiniteType (starCartanMatrix ![1, 2, 5]) := by
  refine not_isFiniteType_starCartanMatrix ?_
  rw [show (Fintype.card (Fin 3) : ℚ) = 3 from by norm_num, Fin.sum_univ_three]
  norm_num [Matrix.cons_val_two, Matrix.tail_cons]

end Three

end TauCeti
