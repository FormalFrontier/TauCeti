/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.GradedModule.Internal
public import TauCeti.LinearAlgebra.TensorCoalgebra.Coderivation
public import TauCeti.LinearAlgebra.Graded.LinearMap

/-!
# Graded coderivations of the reduced tensor coalgebra

Let `M` carry an internal integer grading `G`, and let `T = ⨁_{n ≥ 1} M^{⊗ n}` be the reduced
tensor coalgebra of `TauCeti.ReducedTensorWords`.  The ungraded correspondence of
`TauCeti.ReducedTensorWords.coderivEquivTaylor` matches coderivations with their Taylor components,
but an operation of degree `q` assembles into a coderivation *of degree `q`*, and a degree-`q`
coderivation satisfies the co-Leibniz rule with a Koszul sign: cutting its value gives the cut
halves with `b` applied to one half, scaled by the sign `(-1)^(q * |w₁|)` when `b` is applied to
the right half `w₂`.  This file packages that signed correspondence.

The sign is not carried by hand.  The parity operator `TauCeti.InternalGrading.parityTwist G q`
scales each homogeneous element of degree `e` by `(-1)^(q * e)`, and the letterwise extension
`ReducedTensorWords.map` lifts it to words.  Precomposing each Taylor summand with the twist of the
letters preceding its collapsed block produces exactly the signs
`(-1)^(q * (|x₁| + ⋯ + |x_{p - 1}|))` of the classical suspended formula, and the twisted co-Leibniz
identity takes the sign-free shape

`Δ ∘ b = (b ⊗ 1) ∘ Δ + (1 ⊗ b) ∘ (τ ⊗ 1) ∘ Δ`

in which `τ = TauCeti.InternalGrading.parityTwist G q` acts on the left half of every cut.  For
`q = 0` this reduces term by term to the ungraded theory: the twist of degree zero is the
identity, so a degree-`0` graded coderivation is exactly an ungraded coderivation.

## Main definitions

* `TauCeti.InternalGrading.parityTwist`: the parity operator scaling degree-`e` elements by
  `(-1)^(q * e)`.
* `TauCeti.ReducedTensorWords.gradedCoderiv`: the graded Taylor expansion of a linear map `F` from
  words to letters, at degree `q`.
* `TauCeti.ReducedTensorWords.IsGradedCoderivation`: the twisted co-Leibniz identity of a degree-`q`
  endomorphism of words.
* `TauCeti.ReducedTensorWords.gradedPiece`: the words whose letters have total degree `D`.

## Main results

* `TauCeti.ReducedTensorWords.isGradedCoderivation_gradedCoderiv`,
  `TauCeti.ReducedTensorWords.letter_comp_gradedCoderiv`: `gradedCoderiv G q F` is a degree-`q`
  graded coderivation with letter component `F`.
* `TauCeti.ReducedTensorWords.IsGradedCoderivation.eq_of_letter_comp_eq`: a graded coderivation is
  determined by its letter component.
* `TauCeti.ReducedTensorWords.isHomogeneous_gradedCoderiv`: if `F` raises degrees by `q` then so
  does `gradedCoderiv G F q`.
* `TauCeti.ReducedTensorWords.gradedCoderivEquivTaylor`: the degree-`q` graded coderivations form a
  submodule identified, through the letter components, with the maps from tensor words to letters.

## References

* E. Getzler and J. D. S. Jones, *A-infinity algebras and the cyclic bar complex*, Sections 1--2.
* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.1 and 3.6.
-/
public section

open scoped BigOperators DirectSum TensorProduct

universe uR uM

namespace TauCeti



section GradedCoderiv

open ReducedTensorWords InternalGrading

variable {R : Type uR} {M : Type uM} [CommRing R] [AddCommMonoid M] [Module R M]

/-- The tuple `x` with exactly the letters at positions in the half-open interval `[a, a + p)`
twisted.  The Taylor summand collapsing the block of length `d` starting at `a + p`, namely the
block `[a + p, a + p + d)` of `x`, is supported on this tuple: the collapse carries the Koszul
sign of moving the operation past those preceding letters, and twisting them is how that sign is
encoded. -/
noncomputable def ReducedTensorWords.twistedTuple (G : InternalGrading R M) (q : ℤ) {n : ℕ}
    (x : Fin n → M) (a p : ℕ) : Fin n → M :=
  fun i => if a ≤ i.val ∧ i.val < a + p then parityTwist G q (x i) else x i


/-- The endomorphism of length-`n` tensor words twisting the first `p` letters: precomposing the
ungraded Taylor summand at position `p` with it produces the graded, Koszul-signed summand. -/
private noncomputable def ReducedTensorWords.gradedTwistFirst (G : InternalGrading R M) (q : ℤ)
    (n p : ℕ) :
    TensorPower R n M →ₗ[R] TensorPower R n M :=
  PiTensorProduct.lift
    (MultilinearMap.compLinearMap (PiTensorProduct.tprod R (s := fun _ : Fin n => M))
      fun i => if i.val < p then parityTwist G q else LinearMap.id)

private theorem ReducedTensorWords.gradedTwistFirst_tprod (G : InternalGrading R M) (q : ℤ)
    (n p : ℕ)
    (x : Fin n → M) :
    gradedTwistFirst G q n p (PiTensorProduct.tprod R x)
      = PiTensorProduct.tprod R
          fun i => (if i.val < p then parityTwist G q else LinearMap.id) (x i) := by
  rw [gradedTwistFirst, PiTensorProduct.lift.tprod, _root_.MultilinearMap.compLinearMap_apply]

/-- The `(p, d)` summand of the graded Taylor expansion of `F` at degree `q`: the ungraded summand,
precomposed with the twist of the letters preceding the collapsed block. -/
noncomputable def ReducedTensorWords.gradedCoderivSummand (G : InternalGrading R M)
    (F : ReducedTensorWords R M →ₗ[R] M) (q : ℤ) (n p d : ℕ) :
    TensorPower R n M →ₗ[R] ReducedTensorWords R M :=
  coderivSummand R F n p d ∘ₗ gradedTwistFirst G q n p

/-- On a pure tensor word, the graded Taylor summand splices the value of `F` on the collapsed
block into the tuple whose first `p` letters carry the parity twist. -/
theorem ReducedTensorWords.gradedCoderivSummand_tprod (G : InternalGrading R M)
    (F : ReducedTensorWords R M →ₗ[R] M) (q : ℤ) {n p d : ℕ} (hd : 0 < d) (hpd : p + d ≤ n)
    (x : Fin n → M) :
    gradedCoderivSummand G F q n p d (PiTensorProduct.tprod R x)
      = splice R (twistedTuple G q x 0 p) 0 n p d (F (subword R x p d)) := by
  have hsub : subword R
      (fun i => (if i.val < p then parityTwist G q else LinearMap.id) (x i)) p d =
      subword R x p d :=
    subword_congr R _ _ (by omega) (by omega) fun j hj ↦ by
      simp [show ¬(p + j < p) from by omega]
  rw [gradedCoderivSummand, LinearMap.coe_comp, Function.comp_apply, gradedTwistFirst_tprod,
    coderivSummand_tprod R F hd hpd, hsub]
  refine splice_congr R _ _ _ (by omega) (by omega) fun j hj ↦ ?_
  simp only [twistedTuple, Nat.zero_le, true_and]
  by_cases hj' : j < p <;> simp [hj']

/-- The graded Taylor expansion of a map `F` from words to single letters, at degree `q`: on a
tensor word it collapses each block to the letter that `F` produces from it, composed with the
twist of the letters preceding the block.

If the inputs are homogeneous of degrees `𝒟 i`, the collapse at position `p` thus carries the
Koszul sign `(-1)^(q * (𝒟 0 + ⋯ + 𝒟 (p - 1)))`, because the parity twist scales each of those
letters by its own sign factor; see `InternalGrading.parityTwist_apply_of_mem`. -/
noncomputable def ReducedTensorWords.gradedCoderiv (G : InternalGrading R M)
    (F : ReducedTensorWords R M →ₗ[R] M) (q : ℤ) :
    ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M :=
  DirectSum.toModule R {n : ℕ // 0 < n} _ fun n =>
    ∑ p ∈ Finset.range n.1, ∑ d ∈ Finset.range (n.1 + 1), gradedCoderivSummand G F q n.1 p d

private theorem gradedCoderiv_of (G : InternalGrading R M) (F : ReducedTensorWords R M →ₗ[R] M)
    (q : ℤ) (n : {n : ℕ // 0 < n}) (z : TensorPower R n.1 M) :
    gradedCoderiv G F q (of R M n z)
      = ∑ p ∈ Finset.range n.1, ∑ d ∈ Finset.range (n.1 + 1),
          gradedCoderivSummand G F q n.1 p d z := by
  rw [gradedCoderiv, toModule_of]
  simp only [LinearMap.sum_apply]

/-- Evaluation of the graded Taylor expansion on a pure tensor word: every summand collapses one
block and twists the letters preceding it. -/
theorem ReducedTensorWords.gradedCoderiv_of_tprod (G : InternalGrading R M)
    (F : ReducedTensorWords R M →ₗ[R] M) (q : ℤ) {n : ℕ} (hn : 0 < n) (x : Fin n → M) :
    gradedCoderiv G F q (of R M ⟨n, hn⟩ (PiTensorProduct.tprod R x))
      = ∑ p ∈ Finset.range n, ∑ d ∈ Finset.range (n + 1),
          splice R (twistedTuple G q x 0 p) 0 n p d (F (subword R x p d)) := by
  rw [gradedCoderiv_of]
  refine Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun d _ ↦ ?_
  by_cases h : 0 < d ∧ p + d ≤ n
  · rw [gradedCoderivSummand_tprod G F q h.1 h.2 x]
  · rw [gradedCoderivSummand, coderivSummand_eq_zero R F (by tauto), LinearMap.zero_comp,
      LinearMap.zero_apply]
    exact (splice_eq_zero R (twistedTuple G q x 0 p) _ (by tauto)).symm

/-- Evaluation of a Taylor summand on a block read out of a longer tuple: the same transport as
for the ungraded summands, with the twisted tuple carried along. -/
theorem ReducedTensorWords.gradedCoderivSummand_tprod_of_eq (G : InternalGrading R M)
    (F : ReducedTensorWords R M →ₗ[R] M) (q : ℤ) {n b : ℕ} (x : Fin n → M) (y : Fin b → M)
    {a : ℕ} (hab : a + b ≤ n)
    (hy : ∀ j : Fin b, y j = x ⟨a + j.val, by omega⟩)
    (p d : ℕ) :
    gradedCoderivSummand G F q b p d (PiTensorProduct.tprod R y)
      = splice R (twistedTuple G q x a p) a b p d (F (subword R x (a + p) d)) := by
  by_cases h : 0 < d ∧ p + d ≤ b
  · have hsub : subword R y p d = subword R x (a + p) d :=
      subword_congr R _ _ h.2 (by omega) fun j hj ↦ by
        have hh := hy ⟨p + j, by omega⟩
        rw [hh]
        exact congrArg _ (Fin.ext (show a + (p + j) = a + p + j from (Nat.add_assoc a p j).symm))
    rw [gradedCoderivSummand_tprod G F q h.1 h.2 y, hsub]
    refine splice_congr R _ _ _ (by omega) (by omega) fun j hj ↦ ?_
    simp only [twistedTuple, Nat.zero_add]
    by_cases hj' : j < p
    · have hh := hy ⟨j, hj⟩
      rw [hh]
      simp [hj', show a ≤ a + j from by omega, show a + j < a + p from by omega]
    · have hh := hy ⟨j, hj⟩
      rw [hh]
      simp [hj', show ¬(a + j < a + p) from by omega]
  · rw [gradedCoderivSummand, coderivSummand_eq_zero R F (by tauto), LinearMap.zero_comp,
      LinearMap.zero_apply]
    exact (splice_eq_zero R (twistedTuple G q x a p) _ (by tauto)).symm

/-- Evaluation of the graded Taylor expansion on a block of a pure tensor word: the same sums as
for the ungraded `coderiv_subword`, with each spliced tuple twisted before the block that
collapses.  The two ranges may be taken as large as convenient, since a summand whose collapsed
block does not fit vanishes. -/
theorem ReducedTensorWords.gradedCoderiv_subword (G : InternalGrading R M)
    (F : ReducedTensorWords R M →ₗ[R] M) (q : ℤ) {n : ℕ} (x : Fin n → M) {a b K : ℕ}
    (hK : b ≤ K) :
    gradedCoderiv G F q (subword R x a b)
      = ∑ p ∈ Finset.range K, ∑ d ∈ Finset.range (K + 1),
          splice R (twistedTuple G q x a p) a b p d (F (subword R x (a + p) d)) := by
  by_cases hab : a + b ≤ n
  · have hvanish : ∀ p d : ℕ, b ≤ p ∨ b < d →
        splice R (twistedTuple G q x a p) a b p d (F (subword R x (a + p) d)) = 0 :=
      fun p d h ↦ by
        rcases h with h | h
        · refine splice_eq_zero R (twistedTuple G q x a p) _ ?_
          rintro ⟨hd, hb', -⟩
          rcases Nat.eq_zero_or_pos d with rfl | hdd
          · omega
          · omega
        · exact splice_eq_zero_of_block_lt_add R (twistedTuple G q x a p)
            (F (subword R x (a + p) d)) (by omega)
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · rw [subword_length_zero, map_zero]
      exact (Finset.sum_eq_zero fun p _ ↦ Finset.sum_eq_zero fun d _ ↦
        hvanish p d (Or.inl (Nat.zero_le p))).symm
    have inner : ∀ p : ℕ, ∑ d ∈ Finset.range (b + 1),
        splice R (twistedTuple G q x a p) a b p d (F (subword R x (a + p) d)) =
        ∑ d ∈ Finset.range (K + 1),
          splice R (twistedTuple G q x a p) a b p d (F (subword R x (a + p) d)) :=
      fun p ↦ Finset.sum_subset (Finset.range_subset_range.mpr (by omega)) fun d _ hd ↦ by
        simp only [Finset.mem_range, not_lt] at hd
        exact hvanish p d (Or.inr (by omega))
    have outer : ∑ p ∈ Finset.range b, ∑ d ∈ Finset.range (K + 1),
        splice R (twistedTuple G q x a p) a b p d (F (subword R x (a + p) d)) =
        ∑ p ∈ Finset.range K, ∑ d ∈ Finset.range (K + 1),
          splice R (twistedTuple G q x a p) a b p d (F (subword R x (a + p) d)) :=
      Finset.sum_subset (Finset.range_subset_range.mpr hK) fun p _ hp ↦ by
        simp only [Finset.mem_range, not_lt] at hp
        exact Finset.sum_eq_zero fun d _ ↦ hvanish p d (Or.inl hp)
    rw [subword_eq_of_tprod R x hb hab, gradedCoderiv_of, ← outer,
      ← Finset.sum_congr rfl (fun p (_ : p ∈ Finset.range b) ↦ inner p)]
    exact Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun d _ ↦
      gradedCoderivSummand_tprod_of_eq G F q x (fun j : Fin b => x ⟨a + j, by omega⟩) hab
        (fun j ↦ rfl) p d
  · rw [subword_eq_zero_of_lt_add R x (by omega), map_zero]
    symm
    exact Finset.sum_eq_zero fun p _ ↦ Finset.sum_eq_zero fun d _ ↦
      splice_eq_zero_of_length_lt_add R (twistedTuple G q x a p)
        (F (subword R x (a + p) d)) (by omega)


/-! ### The grading by total letter degree -/

/-- The words of total degree `D`: the span of the pure tensor words whose letters lie in
homogeneous pieces the degrees of which add up to `D`. -/
noncomputable def ReducedTensorWords.gradedPiece (G : InternalGrading R M) (D : ℤ) :
    Submodule R (ReducedTensorWords R M) :=
  Submodule.span R {z | ∃ (n : ℕ) (_hn : 0 < n) (𝒟 : Fin n → ℤ) (x : Fin n → M),
    (∀ i, x i ∈ G.piece (𝒟 i)) ∧ (∑ i, 𝒟 i) = D ∧
      z = of R M ⟨n, _hn⟩ (PiTensorProduct.tprod R x)}

/-- A pure tensor word of homogeneous letters of degrees `𝒟 i` lies in the graded piece of total
degree `∑ i, 𝒟 i`. -/
theorem ReducedTensorWords.mem_gradedPiece_of_tprod (G : InternalGrading R M) {n : ℕ} (hn : 0 < n)
    (x : Fin n → M) (𝒟 : Fin n → ℤ) (h𝒟 : ∀ i, x i ∈ G.piece (𝒟 i)) :
    of R M ⟨n, hn⟩ (PiTensorProduct.tprod R x) ∈ gradedPiece G (∑ i, 𝒟 i) :=
  Submodule.subset_span ⟨n, hn, 𝒟, x, h𝒟, rfl, rfl⟩

/-- Splicing one homogeneous letter into a word of homogeneous letters stays inside the graded
piece: the total degree is that of the untouched prefix and suffix plus the degree of the new
letter.  The degree family is indexed by absolute positions, since splicing shifts them. -/
theorem ReducedTensorWords.splice_mem_gradedPiece (G : InternalGrading R M) {n : ℕ}
    (x : Fin n → M) (𝒟 : ℕ → ℤ) (h𝒟 : ∀ i : Fin n, x i ∈ G.piece (𝒟 i))
    (p d : ℕ) {E : ℤ} {e : M} (he : e ∈ G.piece E) (hpd : p + d ≤ n) :
    splice R x 0 n p d e ∈ gradedPiece G
      ((∑ j ∈ Finset.range p, 𝒟 j) + E +
        ∑ j ∈ Finset.range (n - p - d), 𝒟 (p + d + j)) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · rw [splice_zero_length]
    exact Submodule.zero_mem _
  · have hidx : ∑ i : Fin (n + 1 - d),
        (fun j : Fin (n + 1 - d) =>
          if j.val < p then 𝒟 j.val else if j.val = p then E else 𝒟 (j.val + d - 1)) i =
        (∑ j ∈ Finset.range p, 𝒟 j) + E +
          ∑ j ∈ Finset.range (n - p - d), 𝒟 (p + d + j) := by
      rw [Fin.sum_univ_eq_sum_range
        (f := fun k : ℕ => if k < p then 𝒟 k else if k = p then E else 𝒟 (k + d - 1)),
        show n + 1 - d = p + (1 + (n - p - d)) from by omega, Finset.sum_range_add,
        Finset.sum_range_add, Finset.sum_range_one]
      have s1 : ∑ x ∈ Finset.range p,
          (if x < p then 𝒟 x else if x = p then E else 𝒟 (x + d - 1))
          = ∑ x ∈ Finset.range p, 𝒟 x :=
        Finset.sum_congr rfl fun j hj ↦ by simp [Finset.mem_range.mp hj]
      have s2 : ∑ x ∈ Finset.range (n - p - d),
          (if p + (1 + x) < p then 𝒟 (p + (1 + x))
            else if p + (1 + x) = p then E else 𝒟 (p + (1 + x) + d - 1))
          = ∑ x ∈ Finset.range (n - p - d), 𝒟 (p + d + x) :=
        Finset.sum_congr rfl fun j _ ↦ by
          simp [show p + (1 + j) + d - 1 = p + d + j from by omega]
      rw [s1, s2,
        show (if p + 0 < p then 𝒟 (p + 0)
            else if p + 0 = p then E else 𝒟 (p + 0 + d - 1)) = E from by simp]
      abel
    rw [splice_eq_of_tprod R x e hd hpd (by omega)]
    have step := mem_gradedPiece_of_tprod G (by omega)
      (fun j : Fin (n + 1 - d) =>
        dite (j.val < p) (fun _ => x ⟨(0 : ℕ) + j.val, by have := j.isLt; omega⟩)
          (fun _ =>
            dite (j.val = p) (fun _ => e)
              (fun _ => x ⟨(0 : ℕ) + (j.val + d - 1), by have := j.isLt; have := hpd; omega⟩)))
      (fun j : Fin (n + 1 - d) =>
        if j.val < p then 𝒟 j.val else if j.val = p then E else 𝒟 (j.val + d - 1))
      (by
        intro j
        split_ifs with h₁ h₂
        · have h := h𝒟 ⟨j.val, by have := j.isLt; omega⟩
          simpa using h
        · exact he
        · have h := h𝒟 ⟨j.val + d - 1, by have := j.isLt; have := hpd; omega⟩
          simpa using h)
    rw [hidx] at step
    exact step

/-- If `F` raises total degrees by `q`, so does its graded Taylor expansion: for every `D`,
the map `gradedCoderiv G F q` sends `gradedPiece G D` into `gradedPiece G (D + q)`. -/
theorem ReducedTensorWords.isHomogeneous_gradedCoderiv (G : InternalGrading R M)
    (F : ReducedTensorWords R M →ₗ[R] M) (q : ℤ)
    (hF : LinearMap.IsHomogeneous F (gradedPiece G) (fun e => G.piece e) q) :
    LinearMap.IsHomogeneous (gradedCoderiv G F q) (gradedPiece G) (gradedPiece G) q := by
  rw [LinearMap.isHomogeneous_def]
  intro D z hz
  induction hz using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨n, hn, 𝒟, x, hx, hD, rfl⟩ := hw
    rw [← hD, gradedCoderiv_of_tprod G F q hn x]
    refine Submodule.sum_mem _ fun p _ => Submodule.sum_mem _ fun d _ => ?_
    by_cases hfit : 0 < d ∧ p + d ≤ n
    · -- extend the degree family to all absolute positions, so that splicing can shift it
      set g : ℕ → ℤ := fun k => if h : k < n then 𝒟 ⟨k, h⟩ else 0 with hgdef
      have hg : ∀ i : Fin n, g i.val = 𝒟 i := fun i => by simp [hgdef]
      -- the twist keeps every letter inside its original piece
      have ht : ∀ i : Fin n, twistedTuple G q x 0 p i ∈ G.piece (g i.val) := fun i => by
        rw [hg i]
        simp only [twistedTuple, Nat.zero_le, true_and, Nat.zero_add]
        by_cases hi : i.val < p
        · simp only [hi, ite_true]
          exact parityTwist_mem_piece G (hx i) q
        · simp only [hi, ite_false]
          exact hx i
      -- the collapsed block is a word of total degree ∑_{j < d} g (p + j)
      have hsub : subword R x p d ∈ gradedPiece G (∑ j ∈ Finset.range d, g (p + j)) := by
        have h := mem_gradedPiece_of_tprod G hfit.1
          (fun j : Fin d => x ⟨p + j.val, by omega⟩)
          (fun j : Fin d => g (p + j.val))
          (fun j => by rw [hg ⟨p + j.val, by omega⟩]; exact hx _)
        rw [subword_eq_of_tprod R x hfit.1 hfit.2]
        rw [Fin.sum_univ_eq_sum_range (f := fun k : ℕ => g (p + k))] at h
        exact h
      have hFe : F (subword R x p d) ∈ G.piece ((∑ j ∈ Finset.range d, g (p + j)) + q) :=
        hF.map_mem hsub
      have idx : (∑ j ∈ Finset.range p, g j) +
          ((∑ j ∈ Finset.range d, g (p + j)) + q) +
          ∑ j ∈ Finset.range (n - p - d), g (p + d + j) = (∑ i, 𝒟 i) + q := by
        have hgsum : (∑ i, 𝒟 i) = ∑ j ∈ Finset.range n, g j := by
          rw [← Fin.sum_univ_eq_sum_range (f := g)]
          exact Finset.sum_congr rfl fun i _ => (hg i).symm
        rw [hgsum]
        have s1 : ∑ j ∈ Finset.range n, g j
            = (∑ j ∈ Finset.range p, g j) + ∑ j ∈ Finset.range (n - p), g (p + j) := by
          have key : ∑ x ∈ Finset.range (p + (n - p)), g x
              = (∑ x ∈ Finset.range p, g x) + ∑ x ∈ Finset.range (n - p), g (p + x) :=
            Finset.sum_range_add g p (n - p)
          rwa [show p + (n - p) = n from Nat.add_sub_cancel' (show p ≤ n from by omega)] at key
        have s2 : ∑ j ∈ Finset.range (n - p), g (p + j)
            = (∑ j ∈ Finset.range d, g (p + j)) +
              ∑ j ∈ Finset.range (n - p - d), g (p + d + j) := by
          have key : ∑ x ∈ Finset.range (d + (n - p - d)), g (p + x)
              = (∑ x ∈ Finset.range d, g (p + x)) +
                ∑ x ∈ Finset.range (n - p - d), g (p + (d + x)) :=
            Finset.sum_range_add (f := fun k : ℕ => g (p + k)) d (n - p - d)
          have hbound : d + (n - p - d) = n - p := by omega
          rw [hbound] at key
          refine Eq.trans key ?_
          simp only [Nat.add_assoc]
        rw [s1, s2]
        abel
      have step := splice_mem_gradedPiece G (twistedTuple G q x 0 p) g ht p d hFe hfit.2
      rwa [idx] at step
    · rw [splice_eq_zero R (twistedTuple G q x 0 p) _ (by tauto)]
      exact Submodule.zero_mem _
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add u v _ _ ihu ihv => rw [map_add]; exact Submodule.add_mem _ ihu ihv
  | smul a u _ ih => rw [map_smul]; exact Submodule.smul_mem _ _ ih

/-! ### Graded coderivations -/

section Predicate

open ReducedTensorWords

variable {R : Type uR} {M : Type uM} [CommRing R] [AddCommMonoid M] [Module R M]

/-- A degree-`q` *graded coderivation* of the reduced tensor coalgebra: an endomorphism `b`
satisfying the co-Leibniz rule with the Koszul sign of the left cut half,

`Δ ∘ b = (b ⊗ 1) ∘ Δ + (1 ⊗ b) ∘ (τ ⊗ 1) ∘ Δ`,

in which `τ = ReducedTensorWords.map (InternalGrading.parityTwist G q)` is the letterwise
extension of the parity operator and acts on the left half of every cut.  On a pure tensor
`z = w₁ ⊗ w₂` of homogeneous letters this reads

`Δ (b z) = b w₁ ⊗ w₂ + (-1)^(q * |w₁|) • (w₁ ⊗ b w₂)`,

the classical signed co-Leibniz rule of a degree-`q` coderivation.  For `q = 0` the twist is the
identity and this is plain `IsCoderivation`. -/
def ReducedTensorWords.IsGradedCoderivation (G : InternalGrading R M) (q : ℤ)
    (b : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M) : Prop :=
  deconcatenation R M ∘ₗ b =
    LinearMap.rTensor (ReducedTensorWords R M) b ∘ₗ deconcatenation R M +
      (LinearMap.lTensor (ReducedTensorWords R M) b ∘ₗ
          LinearMap.rTensor (ReducedTensorWords R M)
            (ReducedTensorWords.map (R := R) (InternalGrading.parityTwist G q))) ∘ₗ
        deconcatenation R M

variable {G}

/-- The co-Leibniz identity of a graded coderivation, applied to an element. -/
theorem ReducedTensorWords.IsGradedCoderivation.deconcatenation_apply {q : ℤ}
    {b : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M}
    (hb : IsGradedCoderivation G q b) (z : ReducedTensorWords R M) :
    deconcatenation R M (b z) =
      LinearMap.rTensor (ReducedTensorWords R M) b (deconcatenation R M z) +
        LinearMap.lTensor (ReducedTensorWords R M) b
          (LinearMap.rTensor (ReducedTensorWords R M)
            (ReducedTensorWords.map (R := R) (InternalGrading.parityTwist G q))
            (deconcatenation R M z)) := by
  have h := congrArg (fun f : _ →ₗ[_] _ => f z) hb
  simpa only [LinearMap.coe_comp, Function.comp_apply, LinearMap.add_apply] using h

/-- The co-Leibniz identity of a graded coderivation, as a reusable `Iff`: this exposes the body
of the predicate to consumers in other modules, for which the definition's body is not exposed. -/
theorem ReducedTensorWords.isGradedCoderivation_iff {q : ℤ}
    {b : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M} :
    IsGradedCoderivation G q b ↔
      (deconcatenation R M ∘ₗ b =
        LinearMap.rTensor (ReducedTensorWords R M) b ∘ₗ deconcatenation R M +
          (LinearMap.lTensor (ReducedTensorWords R M) b ∘ₗ
              LinearMap.rTensor (ReducedTensorWords R M)
                (ReducedTensorWords.map (R := R) (InternalGrading.parityTwist G q))) ∘ₗ
            deconcatenation R M) :=
  Iff.rfl

/-- Twisting letterwise preserves each step of the conilpotence filtration. -/
private theorem map_twist_mem_filtration (G : InternalGrading R M) (q : ℤ) {m : ℕ}
    (z : ReducedTensorWords R M) (hz : z ∈ filtration R M m) :
    ReducedTensorWords.map (R := R) (InternalGrading.parityTwist G q) z ∈ filtration R M m := by
  have key : filtration R M m ≤
      (filtration R M m).comap
        (ReducedTensorWords.map (R := R) (InternalGrading.parityTwist G q)) := by
    rw [filtration_le_iff]
    intro k _ z' hz'
    obtain ⟨x, rfl⟩ := hz'
    rw [Submodule.mem_comap, ReducedTensorWords.map_of]
    exact of_mem_filtration R M (k := k) (n := m) (by omega) _
  exact key hz

/-- On a block of a pure tensor word, twisting letterwise is the twisted tuple read in place. -/
private theorem map_twist_subword (G : InternalGrading R M) (q : ℤ) {n : ℕ}
    (x : Fin n → M) {a b : ℕ} (hab : a + b ≤ n) :
    ReducedTensorWords.map (R := R) (InternalGrading.parityTwist G q) (subword R x a b) =
      subword R (twistedTuple G q x a b) a b := by
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · rw [subword_length_zero, map_zero, subword_length_zero]
  · rw [subword_eq_of_tprod R x hb hab, map_of_tprod,
      subword_eq_of_tprod R (twistedTuple G q x a b) hb hab]
    refine of_tprod_congr R M _ rfl fun j => ?_
    have hj := j.isLt
    simp only [twistedTuple, Fin.val_cast]
    rw [ite_eq_left (show a ≤ a + j.val ∧ a + j.val < a + b from by omega)]

/-- A degree-`q` graded coderivation of the reduced tensor coalgebra is determined by its letter
component, that is by its composite with the projection onto single letters: two such coderivations
whose letter components agree are equal.  This is the signed analogue of
`TauCeti.ReducedTensorWords.IsCoderivation.eq_of_letter_comp_eq`. -/
theorem ReducedTensorWords.IsGradedCoderivation.eq_of_letter_comp_eq {q : ℤ}
    {b₁ b₂ : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M}
    (h₁ : IsGradedCoderivation G q b₁) (h₂ : IsGradedCoderivation G q b₂)
    (hl : letter R M ∘ₗ b₁ = letter R M ∘ₗ b₂) : b₁ = b₂ := by
  have hletter : ∀ z, letter R M (b₁ z) = letter R M (b₂ z) := fun z ↦ by
    have h := congrArg (fun f ↦ f z) hl
    simpa only [LinearMap.coe_comp, Function.comp_apply] using h
  have key : ∀ m : ℕ, ∀ z ∈ filtration R M m, b₁ z = b₂ z := by
    intro m
    induction m with
    | zero =>
        intro z hz
        rw [filtration_zero] at hz
        rw [(Submodule.mem_bot R).1 hz, map_zero, map_zero]
    | succ m ih =>
        intro z hz
        refine eq_of_deconcatenation_eq_of_letter_eq R M ?_ (hletter z)
        obtain ⟨w, hw⟩ := map_deconcatenation_filtration_succ_le R M m ⟨z, hz, rfl⟩
        rw [h₁.deconcatenation_apply, h₂.deconcatenation_apply, ← hw]
        exact rTwist_lTwist_congr _ ih w
  refine LinearMap.ext fun z ↦ ?_
  have hz : z ∈ ⨆ n : ℕ, filtration R M n := by rw [iSup_filtration_eq_top]; trivial
  obtain ⟨m, hm⟩ :=
    (Submodule.mem_iSup_of_directed _ (filtration_monotone R M).directed_le).1 hz
  exact key m z hm

end Predicate


/-- Off the triangle `c + p < n`, every right-half term of the graded co-Leibniz rule vanishes:
an empty collapse is zero outright, and an overrunning collapse vanishes because the cut half is
shorter than the end of the collapsed block. -/
private theorem sum_tmul_splice_eq_zero (G : InternalGrading R M)
    (F : ReducedTensorWords R M →ₗ[R] M) (q : ℤ) {n : ℕ} (x : Fin n → M) {c p : ℕ}
    (hp : n ≤ c + p) :
    ∑ d ∈ Finset.range (n + 1),
      subword R (twistedTuple G q x 0 c) 0 c ⊗ₜ[R]
        splice R (twistedTuple G q x c p) c (n - c) p d (F (subword R x (c + p) d)) = 0 := by
  refine Finset.sum_eq_zero fun d hd ↦ ?_
  simp only [Finset.mem_range] at hd
  rcases Nat.eq_zero_or_pos d with rfl | hd'
  · rw [splice_zero_length R (twistedTuple G q x c p) c (n - c) p
      (F (subword R x (c + p) 0)), TensorProduct.tmul_zero]
  · rw [splice_eq_zero_of_block_lt_add R (twistedTuple G q x c p)
      (F (subword R x (c + p) d)) (by omega), TensorProduct.tmul_zero]

/-- The words `twistedTuple G q x 0 m` and `twistedTuple G q x 0 c` agree on their first `c`
letters whenever `c ≤ m ≤ n`, since twisting only affects positions below the twist length. -/
private theorem subword_twistedTuple_congr (G : InternalGrading R M) (q : ℤ) {n : ℕ}
    (x : Fin n → M) {m c : ℕ} (hcm : c ≤ m) (hm : m ≤ n) :
    subword R (twistedTuple G q x 0 m) 0 c = subword R (twistedTuple G q x 0 c) 0 c := by
  refine subword_congr R (twistedTuple G q x 0 m) (twistedTuple G q x 0 c)
    (by omega) (by omega) fun j hj ↦ ?_
  simp only [twistedTuple, Nat.zero_le, true_and, Nat.zero_add]
  rw [ite_eq_left (show j < m from by omega), ite_eq_left hj]

/-- The tuples `twistedTuple G q x 0 (c + p)` and `twistedTuple G q x c p` agree on every letter
from position `c` onward, so splices acting on the letters at and after position `c` coincide. -/
private theorem splice_twistedTuple_congr (G : InternalGrading R M) (q : ℤ) {n : ℕ}
    (x : Fin n → M) {b c p d : ℕ} (hab : c + b ≤ n) (e : M) :
    splice R (twistedTuple G q x 0 (c + p)) c b p d e =
      splice R (twistedTuple G q x c p) c b p d e := by
  refine splice_congr R _ _ _ hab hab fun j hj ↦ ?_
  simp only [twistedTuple, Nat.zero_le, true_and, Nat.zero_add]
  by_cases hj' : j < p
  · have e2 : c ≤ c + j ∧ c + j < c + p := by omega
    rw [ite_eq_left (show c + j < c + p from by omega), ite_eq_left e2]
  · have e2 : ¬(c ≤ c + j ∧ c + j < c + p) := by omega
    rw [ite_eq_right (show ¬(c + j < c + p) from by omega), ite_eq_right e2]

/-- The graded Taylor expansion of any linear map `F` from tensor words to letters is a
degree-`q` graded coderivation: the signed analogue of `isCoderivation_coderiv`.  The twist of the
letters preceding each collapsed block produces exactly the Koszul sign `(-1)^(q * |left half|)`
of the co-Leibniz rule, so the identity holds for an arbitrary `F`, homogeneous or not. -/
@[simp]
theorem ReducedTensorWords.isGradedCoderivation_gradedCoderiv (G : InternalGrading R M)
    (F : ReducedTensorWords R M →ₗ[R] M) (q : ℤ) :
    IsGradedCoderivation G q (gradedCoderiv G F q) := by
  refine linearMap_ext R M fun n x ↦ ?_
  have hn : 0 < n.1 := n.2
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.add_apply]
  rw [of_tprod_eq_subword R hn x]
  have hLHS : deconcatenation R M (gradedCoderiv G F q (subword R x 0 n.1)) =
      (∑ p ∈ Finset.range n.1, ∑ d ∈ Finset.range (n.1 + 1), ∑ c ∈ Finset.range (p + 1),
          subword R (twistedTuple G q x 0 p) 0 c ⊗ₜ[R]
            splice R (twistedTuple G q x 0 p) c (n.1 - c) (p - c) d (F (subword R x p d))) +
        ∑ p ∈ Finset.range n.1, ∑ d ∈ Finset.range (n.1 + 1), ∑ c ∈ Finset.range n.1,
          splice R (twistedTuple G q x 0 p) 0 c p d (F (subword R x p d)) ⊗ₜ[R]
            subword R (twistedTuple G q x 0 p) c (n.1 - c) := by
    rw [gradedCoderiv_subword G F q x (K := n.1) (le_refl n.1), map_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    rw [map_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun d _ ↦ ?_
    rw [deconcatenation_splice R (twistedTuple G q x 0 p)]
    simp only [Nat.zero_add]
  have hdelta : deconcatenation R M (subword R x 0 n.1) =
      ∑ c ∈ Finset.range n.1, subword R x 0 c ⊗ₜ[R] subword R x c (n.1 - c) := by
    rw [deconcatenation_subword R x (a := 0) (b := n.1)]
    simp only [Nat.zero_add]
    exact sum_Ioo_eq_sum_range n.1 _ (by rw [subword_length_zero, TensorProduct.zero_tmul])
  have hRHS : LinearMap.rTensor (ReducedTensorWords R M) (gradedCoderiv G F q)
        (deconcatenation R M (subword R x 0 n.1)) +
      LinearMap.lTensor (ReducedTensorWords R M) (gradedCoderiv G F q)
        (LinearMap.rTensor (ReducedTensorWords R M)
          (ReducedTensorWords.map (R := R) (InternalGrading.parityTwist G q))
          (deconcatenation R M (subword R x 0 n.1))) =
      (∑ c ∈ Finset.range n.1, ∑ p ∈ Finset.range n.1, ∑ d ∈ Finset.range (n.1 + 1),
          splice R (twistedTuple G q x 0 p) 0 c p d (F (subword R x p d)) ⊗ₜ[R]
            subword R x c (n.1 - c)) +
        ∑ c ∈ Finset.range n.1, ∑ p ∈ Finset.range n.1, ∑ d ∈ Finset.range (n.1 + 1),
          subword R (twistedTuple G q x 0 c) 0 c ⊗ₜ[R]
            splice R (twistedTuple G q x c p) c (n.1 - c) p d
              (F (subword R x (c + p) d)) := by
    rw [hdelta, map_sum, map_sum, map_sum]
    congr 1 <;> refine Finset.sum_congr rfl fun c hc ↦ ?_ <;>
      simp only [Finset.mem_range] at hc
    · rw [LinearMap.rTensor_tmul,
        gradedCoderiv_subword G F q x (a := 0) (b := c) (K := n.1) (by omega),
        TensorProduct.sum_tmul]
      exact Finset.sum_congr rfl fun p _ ↦ by
        rw [TensorProduct.sum_tmul]
        simp only [Nat.zero_add]
    · rw [LinearMap.rTensor_tmul, map_twist_subword G q x (hab := by omega),
        LinearMap.lTensor_tmul,
        gradedCoderiv_subword G F q x (a := c) (b := n.1 - c) (K := n.1) (by omega)]
      rw [TensorProduct.tmul_sum]
      refine Finset.sum_congr rfl fun p _ ↦ ?_
      rw [TensorProduct.tmul_sum]
  rw [hLHS]
  rw [hRHS]
  -- Blocks collapsed in the left half match the plain co-Leibniz term.
  have hA2 : ∑ p ∈ Finset.range n.1, ∑ d ∈ Finset.range (n.1 + 1), ∑ c ∈ Finset.range n.1,
      splice R (twistedTuple G q x 0 p) 0 c p d (F (subword R x p d)) ⊗ₜ[R]
        subword R (twistedTuple G q x 0 p) c (n.1 - c) =
    ∑ c ∈ Finset.range n.1, ∑ p ∈ Finset.range n.1, ∑ d ∈ Finset.range (n.1 + 1),
      splice R (twistedTuple G q x 0 p) 0 c p d (F (subword R x p d)) ⊗ₜ[R]
        subword R x c (n.1 - c) := by
    refine Eq.trans (Finset.sum_congr rfl fun p _ ↦ Finset.sum_comm) ?_
    refine Finset.sum_comm.trans ?_
    refine Finset.sum_congr rfl fun c hc ↦ Finset.sum_congr rfl fun p _ ↦
      Finset.sum_congr rfl fun d _ ↦ ?_
    simp only [Finset.mem_range] at hc
    by_cases hpc : p + d ≤ c
    · have hrw : subword R (twistedTuple G q x 0 p) c (n.1 - c) = subword R x c (n.1 - c) :=
        subword_congr R _ _ (by omega) (by omega) fun j hj ↦ by
          have h2 : ¬((0:ℕ) ≤ c + j ∧ c + j < 0 + p) := by omega
          simp only [twistedTuple, h2, ite_false]
      simp only [hrw]
    · rw [splice_eq_zero_of_block_lt_add R (twistedTuple G q x 0 p)
        (F (subword R x p d)) (by omega), TensorProduct.zero_tmul,
        TensorProduct.zero_tmul]
  -- Blocks collapsed in the right half match the twisted co-Leibniz term, after reindexing the
  -- absolute block position through the triangle identity.
  have hA1 : ∑ p ∈ Finset.range n.1, ∑ d ∈ Finset.range (n.1 + 1),
      ∑ c ∈ Finset.range (p + 1),
        subword R (twistedTuple G q x 0 p) 0 c ⊗ₜ[R]
          splice R (twistedTuple G q x 0 p) c (n.1 - c) (p - c) d (F (subword R x p d)) =
    ∑ c ∈ Finset.range n.1, ∑ p ∈ Finset.range n.1, ∑ d ∈ Finset.range (n.1 + 1),
      subword R (twistedTuple G q x 0 c) 0 c ⊗ₜ[R]
        splice R (twistedTuple G q x c p) c (n.1 - c) p d
          (F (subword R x (c + p) d)) := by
    have hg : ∀ c p : ℕ, n.1 ≤ c + p →
        (∑ d ∈ Finset.range (n.1 + 1),
            subword R (twistedTuple G q x 0 c) 0 c ⊗ₜ[R]
              splice R (twistedTuple G q x c p) c (n.1 - c) p d
                (F (subword R x (c + p) d))) = 0 :=
      fun c p hp ↦ sum_tmul_splice_eq_zero G F q x hp
    rw [(sum_range_triangle n.1 _ hg).symm]
    rw [Finset.sum_congr rfl fun p (_ : p ∈ Finset.range n.1) ↦ Finset.sum_comm]
    refine Finset.sum_congr rfl fun P hP ↦ Finset.sum_congr rfl fun c hc ↦
      Finset.sum_congr rfl fun d _ ↦ ?_
    simp only [Finset.mem_range] at hP hc
    have hcp : c + (P - c) = P := by omega
    have hl := subword_twistedTuple_congr (G := G) (q := q) (x := x) (m := P) (c := c)
      (by omega) (by omega)
    have hbF : subword R x (c + (P - c)) d = subword R x P d := by
      rw [hcp]
    have hr := splice_twistedTuple_congr (G := G) (q := q) (x := x) (b := n.1 - c) (c := c)
      (p := P - c) (d := d) (hab := by omega)
    rw [hcp] at hr
    rw [← hbF, hl, hr]
  rw [add_comm, hA2, hA1]


/-! ### Determinedness and the correspondence -/

section Letter

open ReducedTensorWords

variable {R : Type uR} {M : Type uM} [CommRing R] [AddCommMonoid M] [Module R M]

/-- A spliced word contributes nothing to the letter component unless it collapses the entire
word (in which case the result is the new letter itself): any other collapse leaves at least two
letters, and an empty or overrunning collapse is zero outright. -/
private theorem letter_splice_twisted_eq_zero (G : InternalGrading R M) (q : ℤ)
    (x : Fin n → M) {p d : ℕ} {e : M} (h : ¬(p = 0 ∧ d = n)) :
    letter R M (splice R (twistedTuple G q x 0 p) 0 n p d e) = 0 := by
  rcases eq_or_ne d n with rfl | hne
  · have hp : p ≠ 0 := fun hp => h ⟨hp, rfl⟩
    rw [splice_eq_zero_of_block_lt_add R (twistedTuple G q x 0 p) e (by omega), map_zero]
  · exact letter_splice_eq_zero R (twistedTuple G q x 0 p) e hne

/-- The Taylor components of the graded Taylor expansion are the given map: the only summand
leaving a single letter is the one collapsing the whole word, whose preceding twist is empty. -/
@[simp]
theorem ReducedTensorWords.letter_comp_gradedCoderiv (G : InternalGrading R M)
    (F : ReducedTensorWords R M →ₗ[R] M) (q : ℤ) :
    letter R M ∘ₗ gradedCoderiv G F q = F := by
  refine linearMap_ext R M fun n x ↦ ?_
  have hn : 0 < n.1 := n.2
  simp only [LinearMap.coe_comp, Function.comp_apply]
  rw [of_tprod_eq_subword R hn x,
    gradedCoderiv_subword G F q x (K := n.1) (le_refl n.1)]
  simp only [map_sum]
  refine (Finset.sum_eq_single 0 ?_ ?_).trans ?_
  · intro p _ hp
    refine Finset.sum_eq_zero fun d hd ↦ ?_
    simp only [Finset.mem_range] at hd
    exact letter_splice_twisted_eq_zero G q x (by omega)
  · intro hp
    exact absurd hp (by simp [hn])
  · refine (Finset.sum_eq_single n.1 ?_ ?_).trans ?_
    · intro d hd hd'
      simp only [Finset.mem_range] at hd
      rcases Nat.eq_zero_or_pos d with rfl | hd'
      · rw [splice_zero_length R (twistedTuple G q x 0 0) 0 n.1 0, map_zero]
      · have hcon : ¬((0 : ℕ) = 0 ∧ d = n.1) := by omega
        rw [letter_splice_twisted_eq_zero G q x hcon]
    · intro hcon
      exact absurd hcon (by simp)
    · exact letter_splice_self R (twistedTuple G q x 0 0)
        (F (subword R x 0 n)) hn (by omega)

/-- A graded coderivation whose letter component raises degrees by `q` raises degrees by `q`:
being determined by its letter component, it inherits homogeneity from it. -/
theorem ReducedTensorWords.IsGradedCoderivation.isHomogeneous (G : InternalGrading R M) (q : ℤ)
    (b : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M)
    (hb : IsGradedCoderivation G q b)
    (hhom : LinearMap.IsHomogeneous (letter R M ∘ₗ b) (gradedPiece G) (fun e => G.piece e) q) :
    LinearMap.IsHomogeneous b (gradedPiece G) (gradedPiece G) q := by
  rw [IsGradedCoderivation.eq_of_letter_comp_eq hb (isGradedCoderivation_gradedCoderiv G
    (letter R M ∘ₗ b) q) (letter_comp_gradedCoderiv G (letter R M ∘ₗ b) q).symm]
  exact isHomogeneous_gradedCoderiv G (letter R M ∘ₗ b) q hhom

end Letter

/-! ### Degree zero -/

/-- A degree-`0` graded coderivation is a coderivation: the twist of degree zero is the identity,
so the Koszul sign drops out of the co-Leibniz rule. -/
theorem ReducedTensorWords.IsGradedCoderivation.isCoderivation (G : InternalGrading R M)
    {b : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M}
    (hb : IsGradedCoderivation G 0 b) : IsCoderivation R b := by
  rw [isCoderivation_iff]
  have heq := hb
  simp only [IsGradedCoderivation] at heq
  rw [InternalGrading.parityTwist_zero, ReducedTensorWords.map_id, LinearMap.rTensor_id,
    LinearMap.comp_id, ← LinearMap.add_comp] at heq
  exact heq

/-- A coderivation is a degree-`0` graded coderivation. -/
theorem ReducedTensorWords.IsCoderivation.isGradedCoderivation (G : InternalGrading R M)
    {b : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M}
    (hb : IsCoderivation R b) : IsGradedCoderivation G 0 b := by
  rw [isCoderivation_iff] at hb
  simp only [IsGradedCoderivation]
  rw [hb, InternalGrading.parityTwist_zero, ReducedTensorWords.map_id, LinearMap.rTensor_id,
    LinearMap.comp_id, ← LinearMap.add_comp]

/-- At degree zero the graded Taylor expansion is the ungraded one. -/
@[simp]
theorem ReducedTensorWords.gradedCoderiv_zero (G : InternalGrading R M)
    (F : ReducedTensorWords R M →ₗ[R] M) :
    gradedCoderiv G F 0 = coderiv R F :=
  IsCoderivation.eq_of_letter_comp_eq
    ((isGradedCoderivation_gradedCoderiv G F 0).isCoderivation G)
    (isCoderivation_coderiv R F)
    (by rw [letter_comp_gradedCoderiv, letter_comp_coderiv])



/-! ### The submodule of graded coderivations -/

/-- The degree-`q` graded coderivations of the reduced tensor coalgebra form an `R`-submodule of
its endomorphisms: both sides of the twisted co-Leibniz identity depend linearly on the
endomorphism `b`. -/
noncomputable def ReducedTensorWords.gradedCoderivations (G : InternalGrading R M) (q : ℤ) :
    Submodule R (ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M) where
  carrier := {b | IsGradedCoderivation G q b}
  add_mem' {b₁ b₂} hb₁ hb₂ := by
    change IsGradedCoderivation G q (b₁ + b₂)
    rw [isGradedCoderivation_iff]
    refine LinearMap.ext fun z => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.add_apply]
    rw [map_add, hb₁.deconcatenation_apply, hb₂.deconcatenation_apply,
      LinearMap.rTensor_add, LinearMap.lTensor_add]
    simp only [LinearMap.add_apply]
    abel
  zero_mem' := by
    change IsGradedCoderivation G q 0
    rw [isGradedCoderivation_iff]
    simp [LinearMap.zero_comp]
  smul_mem' r x hx := by
    change IsGradedCoderivation G q (r • x)
    rw [isGradedCoderivation_iff]
    refine LinearMap.ext fun z => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.add_apply,
      LinearMap.rTensor_smul, LinearMap.lTensor_smul, LinearMap.smul_apply]
    rw [map_smul, hx.deconcatenation_apply, smul_add]

/-- Membership in `gradedCoderivations` is, by definition, being a graded coderivation. -/
@[simp]
theorem ReducedTensorWords.mem_gradedCoderivations (G : InternalGrading R M) {q : ℤ}
    {b : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M} :
    b ∈ gradedCoderivations G q ↔ IsGradedCoderivation G q b :=
  Iff.rfl

/-- The graded coderivation/Taylor correspondence: a degree-`q` graded coderivation is determined
by its letter component, and every linear map from tensor words to letters is the letter component
of exactly one such coderivation, namely its graded Taylor expansion `gradedCoderiv G F q`.  This
is the signed analogue of `ReducedTensorWords.coderivEquivTaylor`. -/
noncomputable def ReducedTensorWords.gradedCoderivEquivTaylor (G : InternalGrading R M) (q : ℤ) :
    gradedCoderivations G q ≃ₗ[R] (ReducedTensorWords R M →ₗ[R] M) where
  toFun b := letter R M ∘ₗ (b : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M)
  invFun F := ⟨gradedCoderiv G F q, (mem_gradedCoderivations G).2
    (isGradedCoderivation_gradedCoderiv G F q)⟩
  left_inv b := by
    have hb : IsGradedCoderivation G q
        (b : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M) :=
      (mem_gradedCoderivations G).1 b.property
    have key : (gradedCoderiv G (letter R M ∘ₗ (b : _)) q :
        ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M) =
          (b : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M) :=
      IsGradedCoderivation.eq_of_letter_comp_eq
        (isGradedCoderivation_gradedCoderiv G (letter R M ∘ₗ (b : _)) q) hb
        (by rw [letter_comp_gradedCoderiv])
    exact Subtype.ext key
  right_inv F := letter_comp_gradedCoderiv G F q
  map_add' b₁ b₂ := LinearMap.comp_add _ _ _
  map_smul' r b := LinearMap.comp_smul _ _ _

@[simp]
theorem ReducedTensorWords.gradedCoderivEquivTaylor_apply (G : InternalGrading R M) (q : ℤ)
    (b : gradedCoderivations G q) :
    gradedCoderivEquivTaylor G q b =
      letter R M ∘ₗ (b : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M) :=
  by rfl

@[simp]
theorem ReducedTensorWords.gradedCoderivEquivTaylor_symm_apply (G : InternalGrading R M) (q : ℤ)
    (F : ReducedTensorWords R M →ₗ[R] M) :
    (gradedCoderivEquivTaylor G q).symm F =
      ⟨gradedCoderiv G F q, (mem_gradedCoderivations G).2
        (isGradedCoderivation_gradedCoderiv G F q)⟩ :=
  by rfl

end GradedCoderiv

end TauCeti
