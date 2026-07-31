/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Lie.CartanSubalgebra
public import Mathlib.Algebra.Lie.Weights.Cartan
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.Matrix.IsDiag

/-!
# The diagonal Cartan subalgebra of `gl n R`

The general linear Lie algebra `gl n R` is `Matrix n n R` with the commutator bracket. This file
builds its *diagonal Cartan subalgebra*: the diagonal matrices form an abelian, self-normalizing
Lie subalgebra, hence a Cartan subalgebra in the sense of `LieSubalgebra.IsCartanSubalgebra`. It
also records the resulting dictionary between `n`-tuples and weights, and computes the adjoint
action of the diagonal on the matrix units, which exhibits the matrix units as root vectors.

The Killing form of `gl n R` is degenerate, so none of Mathlib's `LieAlgebra.IsKilling` machinery
(in particular `LieAlgebra.IsKilling.rootSystem`) applies to it, and its Cartan subalgebra has to be
produced by hand.

## Main definitions

* `TauCeti.diagonalCartan R n`: the diagonal matrices, as a `LieSubalgebra R (Matrix n n R)`.
* `TauCeti.diagonalEquiv R n`: the linear equivalence `(n → R) ≃ₗ[R] diagonalCartan R n` given by
  `Matrix.diagonal`.
* `TauCeti.diagonalCartanBasis R n`: the basis of `diagonalCartan R n` by the diagonal matrix
  units, whence `TauCeti.finrank_diagonalCartan`.
* `TauCeti.glWeightEquiv R n`: the linear equivalence between `n`-tuples and weights, sending
  `μ : n → R` to the functional `A ↦ ∑ i, μ i * A i i` on the diagonal Cartan.

## Main results

* `TauCeti.instIsCartanSubalgebraDiagonalCartan`: `diagonalCartan R n` is a Cartan subalgebra.
* `TauCeti.normalizer_diagonalCartan`: the diagonal Cartan is self-normalizing.
* `TauCeti.lie_single_of_mem_diagonalCartan`: for diagonal `A`, the matrix unit `Eᵢⱼ` is an
  eigenvector of `ad A` with eigenvalue the difference `A i i - A j j`.
* `TauCeti.single_mem_rootSpace`: consequently `Eᵢⱼ` lies in the root space for the weight
  `εᵢ - εⱼ`.

## Implementation notes

Everything here is stated over an arbitrary commutative ring `R` and an arbitrary finite index
type `n`; no field, characteristic, or algebraic closure hypothesis is used. The self-normalizing
argument needs only the single matrix unit `Eᵢᵢ` as a test element, and abelianness is
`Matrix.commute_diagonal`.

Mathlib does not register `LieRing.ofAssociativeRing` as a global instance, so, as in
`Mathlib/Algebra/Lie/Matrix.lean`, it is a local instance here.

## References

This implements the opening `gl n` targets (`diagonalCartan`, `mem_diagonalCartan_iff`, its
`IsCartanSubalgebra` instance, and `glWeightEquiv`) of Layer 9 of
`TauCetiRoadmap/RepresentationTheory/LieHighestWeight/README.md`.
-/

@[expose] public section

namespace TauCeti

open Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

variable {R : Type*} [CommRing R] {n : Type*} [DecidableEq n] [Fintype n]

/-- Two diagonal matrices commute, so their Lie bracket vanishes. -/
theorem lie_eq_zero_of_isDiag {A B : Matrix n n R} (hA : A.IsDiag) (hB : B.IsDiag) :
    ⁅A, B⁆ = 0 := by
  obtain ⟨d, rfl⟩ : ∃ d, A = diagonal d := ⟨diag A, hA.diagonal_diag.symm⟩
  obtain ⟨e, rfl⟩ : ∃ e, B = diagonal e := ⟨diag B, hB.diagonal_diag.symm⟩
  rw [LieRing.of_associative_ring_bracket, (commute_diagonal d e).eq, sub_self]

variable (R n)

/-- The diagonal matrices, as a Lie subalgebra of `gl n R = Matrix n n R`.

This is the standard Cartan subalgebra of `gl n R`; see
`TauCeti.instIsCartanSubalgebraDiagonalCartan`. -/
def diagonalCartan : LieSubalgebra R (Matrix n n R) where
  carrier := {A | A.IsDiag}
  add_mem' hA hB := hA.add hB
  zero_mem' := isDiag_zero
  smul_mem' c _ hA := hA.smul c
  lie_mem' hA hB := by simp [lie_eq_zero_of_isDiag hA hB]

variable {R n}

theorem mem_diagonalCartan_iff_isDiag {A : Matrix n n R} :
    A ∈ diagonalCartan R n ↔ A.IsDiag := Iff.rfl

/-- The entrywise description of the diagonal Cartan subalgebra. -/
theorem mem_diagonalCartan_iff {A : Matrix n n R} :
    A ∈ diagonalCartan R n ↔ ∀ i j, i ≠ j → A i j = 0 :=
  ⟨fun h _ _ hij => h hij, fun h _ _ hij => h _ _ hij⟩

@[simp]
theorem diagonal_mem_diagonalCartan (d : n → R) : diagonal d ∈ diagonalCartan R n :=
  isDiag_diagonal d

@[simp]
theorem single_self_mem_diagonalCartan (i : n) (c : R) : single i i c ∈ diagonalCartan R n := by
  rw [← diagonal_single]
  exact diagonal_mem_diagonalCartan _

instance : IsLieAbelian (diagonalCartan R n) where
  trivial A B := Subtype.ext (by simpa using lie_eq_zero_of_isDiag A.2 B.2)

/-! ### The adjoint action of the diagonal on the matrix units -/

/-- The matrix unit `Eᵢⱼ` is an eigenvector of `ad A` for every diagonal `A`, with eigenvalue the
difference `A i i - A j j` of the corresponding diagonal entries. This is the computation that makes
the functionals `εᵢ - εⱼ` the roots of `gl n R`. -/
theorem lie_single_of_mem_diagonalCartan {A : Matrix n n R} (hA : A ∈ diagonalCartan R n)
    (i j : n) (c : R) : ⁅A, single i j c⁆ = (A i i - A j j) • single i j c := by
  obtain ⟨d, rfl⟩ : ∃ d, A = diagonal d :=
    ⟨diag A, (mem_diagonalCartan_iff_isDiag.mp hA).diagonal_diag.symm⟩
  ext a b
  by_cases h : i = a ∧ j = b
  · obtain ⟨rfl, rfl⟩ := h
    simp only [LieRing.of_associative_ring_bracket, Matrix.sub_apply, diagonal_mul, mul_diagonal,
      single_apply_same, Matrix.smul_apply, smul_eq_mul, diagonal_apply_eq]
    ring
  · simp [LieRing.of_associative_ring_bracket, h]

/-! ### Self-normalizing, and the Cartan subalgebra instance -/

variable (R n)

@[simp]
theorem normalizer_diagonalCartan : (diagonalCartan R n).normalizer = diagonalCartan R n := by
  refine le_antisymm (fun X hX => mem_diagonalCartan_iff.mpr fun i j hij => ?_)
    (diagonalCartan R n).le_normalizer
  have h := (LieSubalgebra.mem_normalizer_iff _ X).mp hX _ (single_self_mem_diagonalCartan i 1)
  rw [mem_diagonalCartan_iff] at h
  have hentry : ⁅X, single i i (1 : R)⁆ i j = -X i j := by
    rw [LieRing.of_associative_ring_bracket]
    simp [Ne.symm hij]
  simpa [hentry] using h i j hij

instance instIsCartanSubalgebraDiagonalCartan : (diagonalCartan R n).IsCartanSubalgebra where
  nilpotent := inferInstance
  self_normalizing := normalizer_diagonalCartan R n

/-! ### Coordinates on the diagonal Cartan -/

/-- The diagonal matrices are the image of `n → R` under `Matrix.diagonal`, as a linear
equivalence. -/
def diagonalEquiv : (n → R) ≃ₗ[R] diagonalCartan R n where
  toFun d := ⟨diagonal d, diagonal_mem_diagonalCartan d⟩
  map_add' _ _ := Subtype.ext (by ext a b; by_cases h : a = b <;> simp [h])
  map_smul' _ _ := Subtype.ext (by ext a b; by_cases h : a = b <;> simp [h])
  invFun A := diag (A : Matrix n n R)
  left_inv _ := diag_diagonal _
  right_inv A := Subtype.ext (mem_diagonalCartan_iff_isDiag.mp A.2).diagonal_diag

@[simp]
theorem coe_diagonalEquiv (d : n → R) :
    (diagonalEquiv R n d : Matrix n n R) = diagonal d := rfl

@[simp]
theorem diagonalEquiv_symm_apply (A : diagonalCartan R n) :
    (diagonalEquiv R n).symm A = diag (A : Matrix n n R) := rfl

/-- The diagonal matrix units form a basis of the diagonal Cartan subalgebra. -/
noncomputable def diagonalCartanBasis : Module.Basis n R (diagonalCartan R n) :=
  Module.Basis.ofEquivFun (diagonalEquiv R n).symm

@[simp]
theorem coe_diagonalCartanBasis (i : n) :
    (diagonalCartanBasis R n i : Matrix n n R) = single i i 1 := by
  rw [diagonalCartanBasis, Module.Basis.coe_ofEquivFun, LinearEquiv.symm_symm, coe_diagonalEquiv,
    diagonal_single]

@[simp]
theorem diagonalCartanBasis_repr (A : diagonalCartan R n) (i : n) :
    (diagonalCartanBasis R n).repr A i = (A : Matrix n n R) i i := by
  rw [diagonalCartanBasis, Module.Basis.ofEquivFun_repr_apply, diagonalEquiv_symm_apply, diag_apply]

instance : Module.Free R (diagonalCartan R n) :=
  Module.Free.of_basis (diagonalCartanBasis R n)

instance : Module.Finite R (diagonalCartan R n) :=
  Module.Finite.of_basis (diagonalCartanBasis R n)

theorem finrank_diagonalCartan [StrongRankCondition R] :
    Module.finrank R (diagonalCartan R n) = Fintype.card n := by
  rw [Module.finrank_eq_card_basis (diagonalCartanBasis R n)]

variable {R n}

theorem sum_smul_diagonalCartanBasis (A : diagonalCartan R n) :
    ∑ i, (A : Matrix n n R) i i • diagonalCartanBasis R n i = A := by
  simpa using (diagonalCartanBasis R n).sum_repr A

/-! ### Weights of `gl n R` are `n`-tuples -/

variable (R n)

/-- Weights of `gl n R` are `n`-tuples: the linear equivalence sending `μ : n → R` to the functional
`A ↦ ∑ i, μ i * A i i` on the diagonal Cartan subalgebra. -/
noncomputable def glWeightEquiv : (n → R) ≃ₗ[R] Module.Dual R (diagonalCartan R n) where
  toFun mu :=
    { toFun A := ∑ i, mu i * (A : Matrix n n R) i i
      map_add' A B := by simp [mul_add, Finset.sum_add_distrib]
      map_smul' c A := by simp [Finset.mul_sum, mul_left_comm] }
  map_add' mu nu := by ext; simp [add_mul, Finset.sum_add_distrib]
  map_smul' c mu := by ext; simp [Finset.mul_sum, mul_assoc]
  invFun f i := f (diagonalCartanBasis R n i)
  left_inv mu := by ext i; simp [single_apply, Finset.sum_ite_eq]
  right_inv f := by
    ext A
    conv_rhs => rw [← sum_smul_diagonalCartanBasis A]
    simp [mul_comm]

variable {R n}

@[simp]
theorem glWeightEquiv_apply (mu : n → R) (A : diagonalCartan R n) :
    glWeightEquiv R n mu A = ∑ i, mu i * (A : Matrix n n R) i i := rfl

@[simp]
theorem glWeightEquiv_symm_apply (f : Module.Dual R (diagonalCartan R n)) (i : n) :
    (glWeightEquiv R n).symm f i = f (diagonalCartanBasis R n i) := rfl

/-- The functional `εᵢ - εⱼ` reads off the difference of two diagonal entries. -/
theorem glWeightEquiv_sub_single_apply (i j : n) (A : diagonalCartan R n) :
    glWeightEquiv R n (Pi.single i 1 - Pi.single j 1) A
      = (A : Matrix n n R) i i - (A : Matrix n n R) j j := by
  simp only [glWeightEquiv_apply, Pi.sub_apply, Pi.single_apply, sub_mul, ite_mul, one_mul,
    zero_mul, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- The matrix unit `Eᵢⱼ` lies in the root space of `gl n R` for the weight `εᵢ - εⱼ`. For `i ≠ j`
this identifies the roots of `gl n R` relative to the diagonal Cartan; for `i = j` it says that the
diagonal Cartan lies in the zero root space. -/
theorem single_mem_rootSpace (i j : n) (c : R) :
    single i j c ∈ LieAlgebra.rootSpace (diagonalCartan R n)
      (glWeightEquiv R n (Pi.single i 1 - Pi.single j 1)) := by
  rw [LieAlgebra.rootSpace, LieModule.mem_genWeightSpace]
  refine fun A => ⟨1, ?_⟩
  simp only [pow_one, LinearMap.sub_apply, LieModule.toEnd_apply_apply, LinearMap.smul_apply,
    Module.End.one_apply, LieSubalgebra.coe_bracket_of_module, glWeightEquiv_sub_single_apply,
    lie_single_of_mem_diagonalCartan A.2 i j c, sub_self]

end TauCeti
