/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TensorCoalgebra.Basic

/-!
# Collapsing a block of a tensor word to a single letter

For an `R`-module `M`, `TauCeti.ReducedTensorWords.splice x a b p d e` is the tensor word obtained
from the block `x a ⋯ x (a + b - 1)` by deleting its `d` letters at relative offset `p` and putting
the single letter `e` in their place.  It is the shape of every summand of a coderivation of the
reduced tensor coalgebra, whose Taylor expansion replaces one block of letters by the value of a
single operation on that block.

The main computation here is `TauCeti.ReducedTensorWords.deconcatenation_splice`: a cut of a spliced
word falls either weakly to the left of the new letter, leaving a plain block on the left and a
spliced word on the right, or strictly to its right, leaving a spliced word on the left and a plain
block on the right.  No cut splits the new letter, a letter having no internal position.  Written
this way both halves are again of the two shapes `subword` and `splice`, which is what makes the
coderivation identity an equality of two sums over the same pairs of a cut position and a collapsed
block.

## Main definitions

* `TauCeti.ReducedTensorWords.splice`: a block of a tensor word with one of its subblocks collapsed
  to a single letter.

## Main results

* `TauCeti.ReducedTensorWords.splice_congr`: a spliced word depends only on the letters spliced.
* `TauCeti.ReducedTensorWords.deconcatenation_splice`: reduced deconcatenation of a spliced word.

## References

* E. Getzler and J. D. S. Jones, *A-infinity algebras and the cyclic bar complex*, Sections 1--2.
* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.1 and 3.6.
-/

public section

open scoped BigOperators DirectSum TensorProduct

universe uR uM

namespace TauCeti

namespace ReducedTensorWords

variable (R : Type uR) {M : Type uM} [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- The block `x a ⊗ ⋯ ⊗ x (a + b - 1)` with its `d` letters at relative offset `p` replaced by the
single letter `e`, a tensor word of length `b + 1 - d`.

It is zero unless the collapsed block is nonempty and fits inside the block being spliced, which
fits inside `x`; the intended range of the definition is `0 < d`, `p + d ≤ b` and `a + b ≤ n`. -/
noncomputable def splice {n : ℕ} (x : Fin n → M) (a b p d : ℕ) (e : M) :
    ReducedTensorWords R M :=
  if h : 0 < d ∧ p + d ≤ b ∧ a + b ≤ n then
    of R M ⟨b + 1 - d, by omega⟩
      (PiTensorProduct.tprod R fun j : Fin (b + 1 - d) ↦
        if _ : j.1 < p then x ⟨a + j.1, by omega⟩
        else if _ : j.1 = p then e
        else x ⟨a + (j.1 + d - 1), by omega⟩)
  else 0

/-- On its intended range, a spliced word is the pure tensor of its letters: the letters of the
block before the collapsed subblock, then the new letter, then the letters after it. -/
theorem splice_eq_of_tprod {n : ℕ} (x : Fin n → M) {a b p d : ℕ} (e : M) (hd : 0 < d)
    (hpd : p + d ≤ b) (hab : a + b ≤ n) :
    splice R x a b p d e =
      of R M ⟨b + 1 - d, by omega⟩
        (PiTensorProduct.tprod R fun j : Fin (b + 1 - d) ↦
          if _ : j.1 < p then x ⟨a + j.1, by omega⟩
          else if _ : j.1 = p then e
          else x ⟨a + (j.1 + d - 1), by omega⟩) := by
  rw [splice, dite_eq_left ⟨hd, hpd, hab⟩]

/-- Collapsing an empty subblock is zero: a letter is never produced out of nothing. -/
@[simp]
theorem splice_zero_length {n : ℕ} (x : Fin n → M) (a b p : ℕ) (e : M) :
    splice R x a b p 0 e = 0 := by
  rw [splice, dite_eq_right (by omega)]

/-- A collapsed subblock running past the end of the spliced block is zero: the length `b` of that
block is smaller than the end `p + d` of the subblock. -/
@[simp]
theorem splice_eq_zero_of_block_lt_add {n : ℕ} (x : Fin n → M) {a b p d : ℕ} (e : M)
    (hpd : b < p + d) :
    splice R x a b p d e = 0 := by
  rw [splice, dite_eq_right (by omega)]

/-- A spliced block running past the end of the tuple is zero: the length `n` of the tuple is
smaller than the end `a + b` of the block. -/
@[simp]
theorem splice_eq_zero_of_length_lt_add {n : ℕ} (x : Fin n → M) {a b p d : ℕ} (e : M)
    (hab : n < a + b) :
    splice R x a b p d e = 0 := by
  rw [splice, dite_eq_right (by omega)]

/-- A spliced word is zero outside the intended range of the definition. -/
theorem splice_eq_zero {n : ℕ} (x : Fin n → M) {a b p d : ℕ} (e : M)
    (h : ¬(0 < d ∧ p + d ≤ b ∧ a + b ≤ n)) : splice R x a b p d e = 0 := by
  rw [splice, dite_eq_right h]

/-- A spliced word vanishes when the collapsed block does not fit into the block being spliced
into: either the collapsed block is empty, or it overruns that block. -/
theorem splice_eq_zero_of_not_fits {n : ℕ} (x : Fin n → M) {a b p d : ℕ} (e : M)
    (h : ¬(0 < d ∧ p + d ≤ b)) : splice R x a b p d e = 0 := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · exact splice_zero_length R x a b p e
  · exact splice_eq_zero_of_block_lt_add R x e (by omega)

/-- A spliced word depends only on the letters of the block it splices, not on the tuple carrying
them nor on the position of the block in it. -/
theorem splice_congr {n m : ℕ} (x : Fin n → M) (y : Fin m → M) {a a' b p d : ℕ} (e : M)
    (hab : a + b ≤ n) (hab' : a' + b ≤ m)
    (h : ∀ (j : ℕ) (hj : j < b), x ⟨a + j, by omega⟩ = y ⟨a' + j, by omega⟩) :
    splice R x a b p d e = splice R y a' b p d e := by
  by_cases hd : 0 < d ∧ p + d ≤ b
  · rw [splice_eq_of_tprod R x e hd.1 hd.2 hab, splice_eq_of_tprod R y e hd.1 hd.2 hab']
    refine of_tprod_congr R M _ rfl fun j ↦ ?_
    have hj := j.isLt
    simp only [Fin.val_cast]
    split_ifs with h₁ h₂
    · exact h j.1 (by omega)
    · rfl
    · exact h (j.1 + d - 1) (by omega)
  · rw [splice, splice, dite_eq_right (by tauto), dite_eq_right (by tauto)]


/-- Reduced deconcatenation of a pure tensor word, cut at every nontrivial position. -/
private theorem deconcatenation_of_tprod {L : ℕ} (hL : 0 < L) (y : Fin L → M) :
    deconcatenation R M (of R M ⟨L, hL⟩ (PiTensorProduct.tprod R y)) =
      ∑ c ∈ Finset.Ioo 0 L, subword R y 0 c ⊗ₜ[R] subword R y c (L - c) := by
  rw [of_tprod_eq_subword R hL y, deconcatenation_subword R y (a := 0) (b := L)]
  exact Finset.sum_congr rfl fun c _ ↦ by rw [Nat.zero_add]

/-- Cutting a spliced word weakly to the left of the new letter leaves a shorter block on the left
and a spliced word on the right. -/
private theorem deconcatenation_splice_left {n : ℕ} (x : Fin n → M) {a b p d c : ℕ} (e : M)
    (hd : 0 < d) (hpd : p + d ≤ b) (hab : a + b ≤ n) (hc : 0 < c) (hcp : c ≤ p) :
    subword R
        (fun j : Fin (b + 1 - d) ↦
          if _ : j.1 < p then x ⟨a + j.1, by omega⟩
          else if _ : j.1 = p then e
          else x ⟨a + (j.1 + d - 1), by omega⟩) 0 c ⊗ₜ[R]
      subword R
        (fun j : Fin (b + 1 - d) ↦
          if _ : j.1 < p then x ⟨a + j.1, by omega⟩
          else if _ : j.1 = p then e
          else x ⟨a + (j.1 + d - 1), by omega⟩) c (b + 1 - d - c) =
      subword R x a c ⊗ₜ[R] splice R x (a + c) (b - c) (p - c) d e := by
  have hfst : subword R
      (fun j : Fin (b + 1 - d) ↦
        if _ : j.1 < p then x ⟨a + j.1, by omega⟩
        else if _ : j.1 = p then e
        else x ⟨a + (j.1 + d - 1), by omega⟩) 0 c = subword R x a c := by
    rw [subword_eq_of_tprod R _ hc (by omega), subword_eq_of_tprod R x hc (by omega)]
    refine of_tprod_congr R M _ rfl fun j ↦ ?_
    have hj := j.isLt
    simp only [Fin.val_cast]
    have hjp : 0 + j.1 < p := by omega
    rw [dite_eq_left hjp]
    exact congrArg x (by simp only [Fin.mk.injEq]; omega)
  have hsnd : subword R
      (fun j : Fin (b + 1 - d) ↦
        if _ : j.1 < p then x ⟨a + j.1, by omega⟩
        else if _ : j.1 = p then e
        else x ⟨a + (j.1 + d - 1), by omega⟩) c (b + 1 - d - c) =
      splice R x (a + c) (b - c) (p - c) d e := by
    rw [subword_eq_of_tprod R _ (by omega) (by omega),
      splice_eq_of_tprod R x e hd (by omega) (by omega)]
    refine of_tprod_congr R M _ (by omega) fun j ↦ ?_
    have hj := j.isLt
    simp only [Fin.val_cast]
    split_ifs <;> first | rfl | exact congrArg x (by simp only [Fin.mk.injEq]; omega) | omega
  rw [hfst, hsnd]

/-- Cutting a spliced word strictly to the right of the new letter leaves a spliced word on the
left and a shorter block on the right. -/
private theorem deconcatenation_splice_right {n : ℕ} (x : Fin n → M) {a b p d c : ℕ} (e : M)
    (hd : 0 < d) (hpd : p + d ≤ b) (hab : a + b ≤ n) (hpc : p < c) (hc : c < b + 1 - d) :
    subword R
        (fun j : Fin (b + 1 - d) ↦
          if _ : j.1 < p then x ⟨a + j.1, by omega⟩
          else if _ : j.1 = p then e
          else x ⟨a + (j.1 + d - 1), by omega⟩) 0 c ⊗ₜ[R]
      subword R
        (fun j : Fin (b + 1 - d) ↦
          if _ : j.1 < p then x ⟨a + j.1, by omega⟩
          else if _ : j.1 = p then e
          else x ⟨a + (j.1 + d - 1), by omega⟩) c (b + 1 - d - c) =
      splice R x a (c + (d - 1)) p d e ⊗ₜ[R]
        subword R x (a + (c + (d - 1))) (b - (c + (d - 1))) := by
  have hfst : subword R
      (fun j : Fin (b + 1 - d) ↦
        if _ : j.1 < p then x ⟨a + j.1, by omega⟩
        else if _ : j.1 = p then e
        else x ⟨a + (j.1 + d - 1), by omega⟩) 0 c = splice R x a (c + (d - 1)) p d e := by
    rw [subword_eq_of_tprod R _ (by omega) (by omega),
      splice_eq_of_tprod R x e hd (by omega) (by omega)]
    refine of_tprod_congr R M _ (by omega) fun j ↦ ?_
    have hj := j.isLt
    simp only [Fin.val_cast]
    split_ifs <;> first | rfl | exact congrArg x (by simp only [Fin.mk.injEq]; omega) | omega
  have hsnd : subword R
      (fun j : Fin (b + 1 - d) ↦
        if _ : j.1 < p then x ⟨a + j.1, by omega⟩
        else if _ : j.1 = p then e
        else x ⟨a + (j.1 + d - 1), by omega⟩) c (b + 1 - d - c) =
      subword R x (a + (c + (d - 1))) (b - (c + (d - 1))) := by
    rw [subword_eq_of_tprod R _ (by omega) (by omega),
      subword_eq_of_tprod R x (by omega) (by omega)]
    refine of_tprod_congr R M _ (by omega) fun j ↦ ?_
    have hj := j.isLt
    simp only [Fin.val_cast]
    have hjp : ¬(c + j.1) < p := by omega
    have hjp_ne : ¬(c + j.1) = p := by omega
    rw [dite_eq_right hjp, dite_eq_right hjp_ne]
    exact congrArg x (by simp only [Fin.mk.injEq]; omega)
  rw [hfst, hsnd]

/-- Reduced deconcatenation of a spliced word, when the collapsed block really is a nonempty
block of the spliced block. -/
private theorem deconcatenation_splice_of_le {n : ℕ} (x : Fin n → M) {a b p d : ℕ} (e : M)
    (hd : 0 < d) (hpd : p + d ≤ b) (hab : a + b ≤ n) :
    deconcatenation R M (splice R x a b p d e) =
      (∑ c ∈ Finset.range (p + 1), subword R x a c ⊗ₜ[R] splice R x (a + c) (b - c) (p - c) d e) +
        ∑ c ∈ Finset.range b, splice R x a c p d e ⊗ₜ[R] subword R x (a + c) (b - c) := by
  rw [splice_eq_of_tprod R x e hd hpd hab, deconcatenation_of_tprod R (by omega)]
  have hIoo : Finset.Ioo 0 (b + 1 - d) =
      Finset.Ico 1 (p + 1) ∪ Finset.Ico (p + 1) (b + 1 - d) := by
    rw [Finset.Ico_union_Ico_eq_Ico (by omega) (by omega)]
    ext c
    simp only [Finset.mem_Ioo, Finset.mem_Ico]
    omega
  rw [hIoo, Finset.sum_union (Finset.Ico_disjoint_Ico_consecutive 1 (p + 1) (b + 1 - d))]
  congr 1
  · have hzero : ∀ c ∈ Finset.Ico 0 (p + 1), c ∉ Finset.Ico 1 (p + 1) →
        subword R x a c ⊗ₜ[R] splice R x (a + c) (b - c) (p - c) d e = 0 := by
      intro c hc hc'
      have hc0 : c = 0 := by
        by_contra hne
        exact hc' (Finset.mem_Ico.2 ⟨by omega, (Finset.mem_Ico.1 hc).2⟩)
      rw [hc0, subword_length_zero, TensorProduct.zero_tmul]
    rw [Finset.range_eq_Ico,
      ← Finset.sum_subset (Finset.Ico_subset_Ico_left (Nat.zero_le 1)) hzero]
    refine Finset.sum_congr rfl fun c hc ↦ ?_
    simp only [Finset.mem_Ico] at hc
    exact deconcatenation_splice_left R x e hd hpd hab (by omega) (by omega)
  · have hzero : ∀ c ∈ Finset.Ico 0 b, c ∉ Finset.Ico (p + d) b →
        splice R x a c p d e ⊗ₜ[R] subword R x (a + c) (b - c) = 0 := by
      intro c hc hc'
      have hlt : c < p + d := by
        by_contra hge
        exact hc' (Finset.mem_Ico.2 ⟨by omega, (Finset.mem_Ico.1 hc).2⟩)
      rw [splice_eq_zero_of_block_lt_add R x e hlt, TensorProduct.zero_tmul]
    have hIco :
        Finset.Ico (p + d) b = Finset.Ico (p + 1 + (d - 1)) (b + 1 - d + (d - 1)) := by
      congr 1 <;> omega
    rw [Finset.range_eq_Ico,
      ← Finset.sum_subset (Finset.Ico_subset_Ico (Nat.zero_le (p + d)) (le_refl b)) hzero,
      hIco,
      ← Finset.sum_Ico_add'
        (fun c ↦ splice R x a c p d e ⊗ₜ[R] subword R x (a + c) (b - c)) (p + 1) (b + 1 - d)
        (d - 1)]
    refine Finset.sum_congr rfl fun c hc ↦ ?_
    simp only [Finset.mem_Ico] at hc
    exact deconcatenation_splice_right R x e hd hpd hab (by omega) (by omega)

/-- Reduced deconcatenation of a spliced word.  A cut never splits the new letter, so it falls
either weakly to its left, leaving a plain block and a spliced word, or strictly to its right,
leaving a spliced word and a plain block.  Both sums range over the cut position measured in the
original block, and their summands vanish outside the positions that really occur; that is what
makes the identity hold for a degenerate collapsed block too, both sides then being zero. -/
theorem deconcatenation_splice {n : ℕ} (x : Fin n → M) {a b p d : ℕ} (e : M) :
    deconcatenation R M (splice R x a b p d e) =
      (∑ c ∈ Finset.range (p + 1), subword R x a c ⊗ₜ[R] splice R x (a + c) (b - c) (p - c) d e) +
        ∑ c ∈ Finset.range b, splice R x a c p d e ⊗ₜ[R] subword R x (a + c) (b - c) := by
  by_cases hab : a + b ≤ n
  · by_cases h : 0 < d ∧ p + d ≤ b
    · exact deconcatenation_splice_of_le R x e h.1 h.2 hab
    · rw [splice, dite_eq_right (by tauto), map_zero]
      rw [Finset.sum_eq_zero fun c hc ↦ ?_, Finset.sum_eq_zero fun c hc ↦ ?_, add_zero]
      · simp only [Finset.mem_range] at hc
        rcases Nat.eq_zero_or_pos d with rfl | hd
        · rw [splice_zero_length, TensorProduct.zero_tmul]
        · rw [splice_eq_zero_of_block_lt_add R x e (by omega), TensorProduct.zero_tmul]
      · simp only [Finset.mem_range] at hc
        rcases Nat.eq_zero_or_pos d with rfl | hd
        · rw [splice_zero_length, TensorProduct.tmul_zero]
        · rw [splice_eq_zero_of_block_lt_add R x e (by omega), TensorProduct.tmul_zero]
  · rw [splice_eq_zero_of_length_lt_add R x e (by omega), map_zero]
    have hleft :
        ∑ c ∈ Finset.range (p + 1),
          subword R x a c ⊗ₜ[R] splice R x (a + c) (b - c) (p - c) d e = 0 :=
      Finset.sum_eq_zero fun c hc ↦ by
        simp only [Finset.mem_range] at hc
        by_cases hcb : c ≤ b
        · rw [splice_eq_zero_of_length_lt_add R x e (by omega), TensorProduct.tmul_zero]
        · rw [subword_eq_zero_of_lt_add R x (by omega), TensorProduct.zero_tmul]
    have hright : ∑ c ∈ Finset.range b,
        splice R x a c p d e ⊗ₜ[R] subword R x (a + c) (b - c) = 0 :=
      Finset.sum_eq_zero fun c hc ↦ by
        simp only [Finset.mem_range] at hc
        rw [subword_eq_zero_of_lt_add R x (by omega), TensorProduct.tmul_zero]
    rw [hleft, hright, add_zero]

end ReducedTensorWords

end TauCeti
