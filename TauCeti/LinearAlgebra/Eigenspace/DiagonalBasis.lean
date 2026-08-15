/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.Basis.Basic

/-!
# Invariant subspaces of an endomorphism diagonal in a basis

An endomorphism `f` of a module that is diagonal in a basis `b`, so `f (b i) = a i • b i`, scales
the `i`-th coordinate of every vector by the eigenvalue `a i`.  When the eigenvalues are pairwise
distinct, that is when `a` is injective, this pins down the invariant subspaces: an `f`-invariant
subspace contains every basis vector occurring in one of its elements, hence is spanned by the
basis vectors it contains, and a nonzero eigenvector of `f` is a multiple of a single basis
vector.  Neither is automatic for an operator with repeated eigenvalues.

The mechanism is that a coordinate of a vector `w` can be cleared without disturbing the others:
`f w - a j • w` again lies in any invariant subspace containing `w`, and its `k`-th coordinate is
`(a k - a j) * b.repr w k`, which vanishes at `k = j` and, by injectivity of `a`, at no other
index where `w` had a nonzero coordinate.  An induction on the number of nonzero coordinates then
strips a vector down to a single basis vector.

Mathlib records the neighbouring facts in eigenspace language: eigenspaces for distinct
eigenvalues are independent (`Module.End.eigenspaces_iSupIndep`), and eigenvectors for distinct
eigenvalues are linearly independent (`Module.End.eigenvectors_linearIndependent'`); neither says
what an invariant subspace looks like.  `TauCeti.iSup_inf_iInf_eigenspace_of_invariant` does cut
an invariant submodule out by eigenspaces, but for a commuting family over an algebraically
closed field, in finite dimension, and with semisimple restrictions.  A diagonalizing basis
carries all of that for free and in coordinates, which is the form used here: no finiteness, no
algebraic closedness, and the answer names the basis vectors involved.

## Main results

* `Module.Basis.repr_apply_of_apply_basis`: the coordinates of `f w` are those of `w` scaled by
  the eigenvalues.
* `Module.Basis.self_mem_of_repr_ne_zero` and `Module.Basis.eq_span_self_mem`: an invariant
  subspace contains every basis vector occurring in one of its elements, and is spanned by the
  basis vectors it contains.
* `Module.Basis.exists_eq_and_mem_span_singleton`: a nonzero eigenvector of `f` is a multiple of
  a single basis vector, whose eigenvalue is its eigenvalue.
-/

public section

namespace TauCeti

variable {ι K V : Type*}

/-! ### The coordinates are scaled by the eigenvalues -/

section CommSemiring

variable [CommSemiring K] [AddCommMonoid V] [Module K V] {f : V →ₗ[K] V} {a : ι → K}

/-- **An endomorphism diagonal in a basis scales the coordinates**: if `f (b i) = a i • b i` for
every `i`, then `f` multiplies the `i`-th coordinate of every vector by `a i`. -/
theorem _root_.Module.Basis.repr_apply_of_apply_basis (b : Module.Basis ι K V)
    (hf : ∀ i, f (b i) = a i • b i) (w : V) (i : ι) :
    b.repr (f w) i = a i * b.repr w i := by
  have key : (Finsupp.lapply i).comp ((b.repr : V →ₗ[K] ι →₀ K).comp f)
      = (a i • Finsupp.lapply i).comp (b.repr : V →ₗ[K] ι →₀ K) := by
    refine b.ext fun j => ?_
    rcases eq_or_ne j i with rfl | hj
    · simp [hf j]
    · simp [hf j, hj]
  simpa using LinearMap.congr_fun key w

/-- A vector whose only possibly nonzero coordinate is the `i`-th one is that coordinate times
the `i`-th basis vector. -/
private theorem eq_smul_of_support_subset_singleton {b : Module.Basis ι K V} {w : V} {i : ι}
    (h : (b.repr w).support ⊆ {i}) : w = b.repr w i • b i :=
  calc w = b.repr.symm (b.repr w) := (b.repr.symm_apply_apply w).symm
    _ = b.repr.symm (Finsupp.single i (b.repr w i)) :=
        congrArg _ (Finsupp.support_subset_singleton.1 h)
    _ = b.repr w i • b i := b.repr_symm_single i _

end CommSemiring

/-! ### Invariant subspaces are spanned by basis vectors -/

section Field

variable [Field K] [AddCommGroup V] [Module K V] {f : V →ₗ[K] V} {a : ι → K}
  {W : Submodule K V}

/-- **Clearing a coordinate**: subtracting from `f w` the multiple `a j • w` kills the `j`-th
coordinate and multiplies the `k`-th one by `a k - a j`. -/
private theorem repr_sub_smul_apply (b : Module.Basis ι K V) (hf : ∀ i, f (b i) = a i • b i)
    (w : V) (j k : ι) :
    b.repr (f w - a j • w) k = (a k - a j) * b.repr w k := by
  rw [map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply,
    b.repr_apply_of_apply_basis hf, smul_eq_mul, sub_mul]

/-- The cleared vector has strictly smaller support: it loses the `j`-th coordinate and gains
none. -/
private theorem support_repr_sub_smul_subset [DecidableEq ι] (b : Module.Basis ι K V)
    (hf : ∀ i, f (b i) = a i • b i) (w : V) (j : ι) :
    (b.repr (f w - a j • w)).support ⊆ (b.repr w).support.erase j := by
  intro k hk
  have hk0 : b.repr (f w - a j • w) k ≠ 0 := Finsupp.mem_support_iff.1 hk
  rw [repr_sub_smul_apply b hf w j k] at hk0
  refine Finset.mem_erase.2 ⟨?_, Finsupp.mem_support_iff.2 (right_ne_zero_of_mul hk0)⟩
  rintro rfl
  exact hk0 (by rw [sub_self, zero_mul])

private theorem self_mem_aux (b : Module.Basis ι K V) (hf : ∀ i, f (b i) = a i • b i)
    (ha : Function.Injective a) (hW : ∀ v ∈ W, f v ∈ W) :
    ∀ (n : ℕ) (w : V), w ∈ W → (b.repr w).support.card ≤ n →
      ∀ i : ι, b.repr w i ≠ 0 → b i ∈ W := by
  classical
  intro n
  induction n with
  | zero =>
    intro w _ hcard i hi
    have hsupp : (b.repr w).support = ∅ := Finset.card_eq_zero.1 (Nat.le_zero.1 hcard)
    exact absurd (Finsupp.notMem_support_iff.1 (by rw [hsupp]; exact Finset.notMem_empty i)) hi
  | succ n ih =>
    intro w hw hcard i hi
    by_cases hsub : (b.repr w).support ⊆ {i}
    · -- the `i`-th coordinate is the only nonzero one, so `b i` is a multiple of `w`;
      -- naming that coordinate keeps it from being rewritten along with `w` below
      set c := b.repr w i
      have hmem : c⁻¹ • w ∈ W := W.smul_mem _ hw
      rwa [eq_smul_of_support_subset_singleton hsub, smul_smul, inv_mul_cancel₀ hi,
        one_smul] at hmem
    · -- otherwise some other coordinate `j` is nonzero, and can be cleared
      obtain ⟨j, hjs, hji⟩ := Finset.not_subset.1 hsub
      have hjne : j ≠ i := fun h => hji (Finset.mem_singleton.2 h)
      have hmem : f w - a j • w ∈ W := W.sub_mem (hW w hw) (W.smul_mem _ hw)
      have hcard' : (b.repr (f w - a j • w)).support.card ≤ n := by
        have hle := Finset.card_le_card (support_repr_sub_smul_subset b hf w j)
        rw [Finset.card_erase_of_mem hjs] at hle
        have hpos : 0 < (b.repr w).support.card := Finset.card_pos.2 ⟨j, hjs⟩
        omega
      refine ih _ hmem hcard' i ?_
      rw [repr_sub_smul_apply b hf w j i]
      exact mul_ne_zero (sub_ne_zero.2 fun h => hjne (ha h).symm) hi

/-- **An invariant subspace contains every basis vector occurring in one of its elements**, when
the endomorphism is diagonal in the basis with pairwise distinct eigenvalues: the coordinates of
an element can then be separated by repeatedly clearing one of them. -/
theorem _root_.Module.Basis.self_mem_of_repr_ne_zero (b : Module.Basis ι K V)
    (hf : ∀ i, f (b i) = a i • b i) (ha : Function.Injective a) (hW : ∀ v ∈ W, f v ∈ W) {w : V}
    (hw : w ∈ W) {i : ι} (hi : b.repr w i ≠ 0) : b i ∈ W :=
  self_mem_aux b hf ha hW _ w hw le_rfl i hi

/-- **An invariant subspace is spanned by the basis vectors it contains**, when the endomorphism
is diagonal in the basis with pairwise distinct eigenvalues. -/
theorem _root_.Module.Basis.eq_span_self_mem (b : Module.Basis ι K V)
    (hf : ∀ i, f (b i) = a i • b i) (ha : Function.Injective a) (hW : ∀ v ∈ W, f v ∈ W) :
    W = Submodule.span K {v | ∃ i : ι, b i = v ∧ v ∈ W} := by
  refine le_antisymm (fun w hw => ?_) (Submodule.span_le.2 ?_)
  · rw [← b.linearCombination_repr w, Finsupp.linearCombination_apply, Finsupp.sum]
    refine Submodule.sum_mem _ fun k hk => ?_
    exact Submodule.smul_mem _ _ (Submodule.subset_span
      ⟨k, rfl, b.self_mem_of_repr_ne_zero hf ha hW hw (Finsupp.mem_support_iff.1 hk)⟩)
  · rintro v ⟨-, -, hv⟩
    exact hv

/-- **A nonzero eigenvector is a multiple of a single basis vector**, when the endomorphism is
diagonal in the basis with pairwise distinct eigenvalues, and its eigenvalue is the eigenvalue of
that basis vector. -/
theorem _root_.Module.Basis.exists_eq_and_mem_span_singleton (b : Module.Basis ι K V)
    (hf : ∀ i, f (b i) = a i • b i) (ha : Function.Injective a) {w : V} (hw : w ≠ 0) {c : K}
    (hfw : f w = c • w) : ∃ i : ι, a i = c ∧ w ∈ Submodule.span K {b i} := by
  classical
  have hcoord : ∀ k : ι, a k * b.repr w k = c * b.repr w k := by
    intro k
    rw [← b.repr_apply_of_apply_basis hf, hfw, map_smul, Finsupp.smul_apply, smul_eq_mul]
  have hrne : b.repr w ≠ 0 := fun h => hw (b.repr.map_eq_zero_iff.1 h)
  obtain ⟨i, hi⟩ := Finsupp.ne_iff.1 hrne
  rw [Finsupp.coe_zero, Pi.zero_apply] at hi
  have hci : a i = c := mul_right_cancel₀ hi (hcoord i)
  refine ⟨i, hci, ?_⟩
  have hsupp : (b.repr w).support ⊆ {i} := fun k hk =>
    Finset.mem_singleton.2
      (ha ((mul_right_cancel₀ (Finsupp.mem_support_iff.1 hk) (hcoord k)).trans hci.symm))
  rw [eq_smul_of_support_subset_singleton hsupp]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

end Field

end TauCeti
