/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.RingTheory.Finiteness.Basic
import TauCeti.Algebra.DirectSum.Internal

/-!
# Internally graded modules

This file packages a `ℤ`-graded module as a total module together with an internal direct-sum
decomposition. The total-module presentation is convenient for DG and `A∞` operations, while
`DirectSum.IsInternal` ensures that every element is a finite, uniquely determined sum of
homogeneous elements.

Mathlib already provides the direct-sum equivalence and its induction principle through
`DirectSum.Decomposition`.  An `InternalGrading` retains the family of homogeneous submodules and
the proof that it is internal; the instance below makes Mathlib's decomposition API available
without duplicating it.

The file also records that a finitely generated internally graded module has only finitely many
nonzero pieces, the Koszul twist operator used to encode Koszul signs on homogeneous elements, and
the letterwise tuple operation that applies it on a half-open index interval.

## Main definitions

* `InternalGrading`: an internal `ℤ`-grading of a module.
* `InternalGrading.koszulTwist`: the operator scaling degree-`e` elements by `(-1)^(q * e)`.
* `InternalGrading.twistedTuple`: a tuple with a consecutive block of letters Koszul-twisted.

## Main results

* `TauCeti.InternalGrading.ext`: internal gradings are determined by their homogeneous pieces.
* `TauCeti.InternalGrading.finite_piece_ne_bot`: a finitely generated internally graded module has
  only finitely many nonzero homogeneous pieces.
* `TauCeti.InternalGrading.koszulTwist_apply_of_mem`: the twist acts by the Koszul scalar on
  each homogeneous piece.
* `TauCeti.InternalGrading.koszulTwist_comp`: twists compose by adding the twist parameters.

This is the first graded-module target in Layer 0 of the `DGAInfinity` roadmap.  Later files use
Mathlib's decomposition API to define maps of nonzero degree, shifts, tensor-product gradings, and
signed multilinear operations.
-/

public section

open scoped DirectSum

namespace TauCeti

universe u v w

variable (R : Type u) (M : Type v) [Semiring R] [AddCommMonoid M] [Module R M]

/-- An internal integer grading of an `R`-module `M`.

The `isInternal` field says that the canonical map from the external direct sum of the `piece p`
to `M` is bijective.  Thus elements of `M` have unique finite homogeneous decompositions. -/
structure InternalGrading where
  /-- The submodule of elements of degree `p`. -/
  piece : ℤ → Submodule R M
  /-- The homogeneous pieces form an internal direct sum. -/
  isInternal : DirectSum.IsInternal piece

namespace InternalGrading

variable {R M}

/-- Two internal gradings of the same module are equal as soon as their homogeneous pieces
agree. -/
@[ext]
theorem ext : ∀ {G H : InternalGrading R M}, (∀ p, G.piece p = H.piece p) → G = H
  | ⟨_, _⟩, ⟨_, _⟩, h => by
    obtain rfl := funext h
    rfl

/-- The decomposition attached to an internal grading. -/
noncomputable instance (G : InternalGrading R M) : DirectSum.Decomposition G.piece :=
  G.isInternal.chooseDecomposition

/-- An additive map that vanishes on every homogeneous piece except degree `i` sees only the
degree-`i` component of each argument. -/
theorem map_eq_map_decompose {N : Type w} [AddCommMonoid N] (G : InternalGrading R M)
    (f : M →+ N) {i : ℤ}
    (hf : ∀ j (x : M), x ∈ G.piece j → j ≠ i → f x = 0) (x : M) :
    f x = f (DirectSum.decompose G.piece x i : M) := by
  classical
  conv_lhs => rw [← DirectSum.sum_support_decompose G.piece x]
  rw [map_sum]
  refine Finset.sum_eq_single i (fun j _ hj ↦ ?_) fun hi ↦ ?_
  · exact hf j _ (DirectSum.decompose G.piece x j).2 hj
  · rw [DFinsupp.notMem_support_iff.mp hi, Submodule.coe_zero, map_zero]

end InternalGrading

section FiniteSupport

variable {R : Type u} {M : Type v} [Semiring R] [AddCommMonoid M] [Module R M]

private theorem InternalGrading.finite_piece_ne_bot_aux (G : InternalGrading R M)
    [Module.Finite R M] : {p | G.piece p ≠ ⊥}.Finite :=
  Submodule.finite_ne_bot_of_iSupIndep_of_fg G.isInternal.submodule_iSupIndep
    (by rw [G.isInternal.submodule_iSup_eq_top]; exact Module.Finite.fg_top)

/-- A finitely generated internally graded module has only finitely many nonzero homogeneous
pieces. -/
theorem InternalGrading.finite_piece_ne_bot (G : InternalGrading R M) [Module.Finite R M] :
    {p | G.piece p ≠ ⊥}.Finite :=
  G.finite_piece_ne_bot_aux

/-- Summing the homogeneous components over the finite set of nonzero pieces reconstructs the
original element. -/
theorem InternalGrading.sum_decompose_toFinset (G : InternalGrading R M)
    (hG : {p | G.piece p ≠ ⊥}.Finite) (x : M) :
    ∑ p ∈ hG.toFinset, (DirectSum.decompose G.piece x p : M) = x := by
  classical
  conv_rhs => rw [← DirectSum.sum_support_decompose G.piece x]
  refine (Finset.sum_subset (fun p hp ↦ ?_) fun p _ hp ↦ ?_).symm
  · refine hG.mem_toFinset.mpr fun hbot ↦ DFinsupp.mem_support_iff.mp hp
      (Submodule.coe_eq_zero.mp
        ((Submodule.eq_bot_iff _).mp hbot _ (DirectSum.decompose G.piece x p).2))
  · rw [DFinsupp.notMem_support_iff.mp hp]
    simp

end FiniteSupport

section KoszulTwist

variable {R : Type u} {M : Type v} [CommRing R] [AddCommMonoid M] [Module R M]

/-- The Koszul twist of parameter `q`: on the homogeneous piece of degree `e` it acts as the
scalar `(-1)^(q * e)`.

This is multiplication by the same coefficient that `MultilinearMap.koszulSign` records for a
single homogeneous input of degree `e`.  Downstream modules express their Koszul signs through this
operator: the sign acquired by moving an operation of degree `q` past homogeneous inputs of total
degree `D` is the scalar by which `koszulTwist G q` scales those inputs. -/
noncomputable def InternalGrading.koszulTwist (G : InternalGrading R M) (q : ℤ) : M →ₗ[R] M :=
  DirectSum.coeLinearMap (fun e => G.piece e) ∘ₗ
    DirectSum.toModule R ℤ (⨁ e : ℤ, G.piece e)
      (fun e => (((q * e).negOnePow : ℤ) : R) •
        DirectSum.lof R ℤ (fun e => G.piece e) e) ∘ₗ
    (DirectSum.decomposeLinearEquiv (ℳ := G.piece)).toLinearMap

/-- The tuple `x` with exactly the letters at positions in the half-open interval `[a, a + p)`
Koszul-twisted.  Downstream, the Taylor summand collapsing the block of length `d` starting at
`a + p` is supported on this tuple: the collapse carries the Koszul sign of moving the operation
past those preceding letters, and twisting them is how that sign is encoded. -/
noncomputable def InternalGrading.twistedTuple (G : InternalGrading R M) (q : ℤ) {n : ℕ}
    (x : Fin n → M) (a p : ℕ) : Fin n → M :=
  fun i => if a ≤ i.val ∧ i.val < a + p then koszulTwist G q (x i) else x i

end KoszulTwist

section KoszulTwistLemmas

variable {R : Type u} {M : Type v} [CommRing R] [AddCommMonoid M] [Module R M]

/-- On a homogeneous element of degree `e`, the Koszul twist of parameter `q` acts as the scalar
`(-1)^(q * e)`. -/
theorem InternalGrading.koszulTwist_apply_of_mem (G : InternalGrading R M) {x : M} {e : ℤ}
    (hx : x ∈ G.piece e) (q : ℤ) :
    koszulTwist G q x = (((q * e).negOnePow : ℤ) : R) • x := by
  rw [koszulTwist]
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    DirectSum.decomposeLinearEquiv_apply]
  rw [DirectSum.decompose_of_mem (ℳ := G.piece) hx,
    ← DirectSum.lof_eq_of R ℤ (fun i : ℤ => G.piece i)]
  simp [DirectSum.toModule_lof]

/-- The Koszul twist preserves each homogeneous piece. -/
theorem InternalGrading.koszulTwist_mem_piece (G : InternalGrading R M) {x : M} {e : ℤ}
    (hx : x ∈ G.piece e) (q : ℤ) :
    koszulTwist G q x ∈ G.piece e := by
  rw [InternalGrading.koszulTwist_apply_of_mem G hx q]
  exact Submodule.smul_mem _ _ hx

/-- The Koszul twist of parameter zero is the identity. -/
@[simp]
theorem InternalGrading.koszulTwist_zero (G : InternalGrading R M) :
    koszulTwist G 0 = LinearMap.id := by
  refine DirectSum.decompose_lhom_ext (ℳ := G.piece) fun e => ?_
  ext x
  simp only [LinearMap.comp_apply]
  have h := InternalGrading.koszulTwist_apply_of_mem G (Submodule.coe_mem x) 0
  simpa using h

/-- Koszul twists compose by adding their parameters. -/
theorem InternalGrading.koszulTwist_comp (G : InternalGrading R M) (q q' : ℤ) :
    koszulTwist G q ∘ₗ koszulTwist G q' = koszulTwist G (q + q') := by
  refine DirectSum.decompose_lhom_ext (ℳ := G.piece) fun e => ?_
  ext x
  have hx : (x : M) ∈ G.piece e := Submodule.coe_mem x
  have : koszulTwist G q (koszulTwist G q' (x : M)) = koszulTwist G (q + q') (x : M) := by
    rw [koszulTwist_apply_of_mem G hx q', map_smul, koszulTwist_apply_of_mem G hx q,
      koszulTwist_apply_of_mem G hx (q + q'), smul_smul]
    congr 1
    rw [← Int.cast_mul, ← Units.val_mul, ← Int.negOnePow_add, add_mul, add_comm]
  simpa [LinearMap.comp_apply] using this

/-- The Koszul twist of any parameter is an involution. -/
@[simp]
theorem InternalGrading.koszulTwist_comp_self (G : InternalGrading R M) (q : ℤ) :
    koszulTwist G q ∘ₗ koszulTwist G q = LinearMap.id := by
  rw [koszulTwist_comp, ← two_mul]
  refine DirectSum.decompose_lhom_ext (ℳ := G.piece) fun e => ?_
  ext x
  have hx : (x : M) ∈ G.piece e := Submodule.coe_mem x
  have : koszulTwist G (2 * q) (x : M) = (x : M) := by
    rw [koszulTwist_apply_of_mem G hx (2 * q), mul_assoc, Int.negOnePow_two_mul]
    simp
  simpa [LinearMap.comp_apply] using this

/-- Evaluation of `twistedTuple` on an index inside the twisted interval `[a, a + p)`. -/
@[simp]
theorem InternalGrading.twistedTuple_apply_of_mem_Ico (G : InternalGrading R M) (q : ℤ)
    {n : ℕ} (x : Fin n → M) (a p : ℕ) (i : Fin n) (hi : a ≤ i.val ∧ i.val < a + p) :
    twistedTuple G q x a p i = koszulTwist G q (x i) :=
  ite_eq_left hi

/-- Evaluation of `twistedTuple` on an index outside the twisted interval `[a, a + p)`. -/
@[simp]
theorem InternalGrading.twistedTuple_apply_of_not_mem_Ico (G : InternalGrading R M) (q : ℤ)
    {n : ℕ} (x : Fin n → M) (a p : ℕ) (i : Fin n) (hi : ¬(a ≤ i.val ∧ i.val < a + p)) :
    twistedTuple G q x a p i = x i :=
  ite_eq_right hi

/-- Unfolding of `twistedTuple` as a branch on membership in `[a, a + p)`. -/
@[simp]
theorem InternalGrading.twistedTuple_apply (G : InternalGrading R M) (q : ℤ) {n : ℕ}
    (x : Fin n → M) (a p : ℕ) (i : Fin n) :
    twistedTuple G q x a p i =
      if a ≤ i.val ∧ i.val < a + p then koszulTwist G q (x i) else x i := by
  split_ifs with h
  · exact twistedTuple_apply_of_mem_Ico G q x a p i h
  · exact twistedTuple_apply_of_not_mem_Ico G q x a p i h

/-- Twisting an empty interval leaves the tuple unchanged. -/
@[simp]
theorem InternalGrading.twistedTuple_zero_length (G : InternalGrading R M) (q : ℤ) {n : ℕ}
    (x : Fin n → M) (a : ℕ) : twistedTuple G q x a 0 = x := by
  funext i
  exact twistedTuple_apply_of_not_mem_Ico G q x a 0 i (by omega)

/-- The Koszul twist of parameter zero leaves every letter of the tuple unchanged. -/
@[simp]
theorem InternalGrading.twistedTuple_zero_twist (G : InternalGrading R M) {n : ℕ}
    (x : Fin n → M) (a p : ℕ) : twistedTuple G 0 x a p = x := by
  funext i
  simp [twistedTuple]

end KoszulTwistLemmas

end TauCeti
