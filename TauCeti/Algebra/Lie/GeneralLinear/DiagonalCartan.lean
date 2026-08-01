/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Lie.Weights.Cartan
public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.LinearAlgebra.Matrix.IsDiag

/-!
# The diagonal Cartan subalgebra of `gl n R`

The general linear Lie algebra `gl n R` is `Matrix n n R` with the commutator bracket. This file
builds its *diagonal Cartan subalgebra*: the diagonal matrices form an abelian, self-normalizing
Lie subalgebra, hence a Cartan subalgebra in the sense of `LieSubalgebra.IsCartanSubalgebra`. It
also records the resulting dictionary between `n`-tuples and weights, and computes the adjoint
action of the diagonal on the matrix units, which places each matrix unit in the root space of a
difference of coordinate functionals.

This development cannot assume `LieAlgebra.IsKilling` for `gl n R`: whenever `R` is nontrivial and
`n` is nonempty the identity matrix is a nonzero element of the radical of the Killing form of
`gl n R`, since it is central and so has vanishing adjoint action. So none of Mathlib's
`LieAlgebra.IsKilling` machinery (in particular `LieAlgebra.IsKilling.rootSystem`) is available
here, and the Cartan subalgebra has to be produced by hand.

## Main definitions

* `TauCeti.diagonalCartan R n`: the diagonal matrices, as a `LieSubalgebra R (Matrix n n R)`.
* `TauCeti.diagonalEquiv R n`: the linear equivalence `(n → R) ≃ₗ[R] diagonalCartan R n` given by
  `Matrix.diagonal`.
* `TauCeti.diagonalCartanBasis R n`: the basis of `diagonalCartan R n` by the diagonal matrix
  units, whence `TauCeti.finrank_diagonalCartan`.
* `TauCeti.glWeightEquiv R n`: the linear equivalence between `n`-tuples and weights, sending
  `μ : n → R` to the functional `A ↦ ∑ i, μ i * A i i` on the diagonal Cartan.
* `TauCeti.glRoot R n i j`: the weight `εᵢ - εⱼ`, the candidate roots of `gl n R`.

## Main results

* `TauCeti.instIsCartanSubalgebraDiagonalCartan`: `diagonalCartan R n` is a Cartan subalgebra.
* `TauCeti.diagonalCartan_normalizer_eq_self`: the diagonal Cartan is self-normalizing.
* `TauCeti.lie_apply_of_mem_diagonalCartan`: the adjoint action of a diagonal matrix is entrywise
  scaling, by `A a a - A b b` in the `(a, b)` entry.
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

public section

namespace TauCeti

open Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

variable {R : Type*} [CommRing R] {n : Type*} [DecidableEq n] [Fintype n]

/-- Two diagonal matrices commute, so their Lie bracket vanishes. -/
theorem lie_eq_zero_of_isDiag {A B : Matrix n n R} (hA : A.IsDiag) (hB : B.IsDiag) :
    ⁅A, B⁆ = 0 := by
  obtain ⟨d, rfl⟩ : ∃ d, A = diagonal d := ⟨diag A, hA.diagonal_diag.symm⟩
  obtain ⟨e, rfl⟩ : ∃ e, B = diagonal e := ⟨diag B, hB.diagonal_diag.symm⟩
  exact (commute_diagonal d e).lie_eq

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

/-- Membership in the diagonal Cartan subalgebra is `Matrix.IsDiag`. -/
@[simp]
theorem mem_diagonalCartan_iff_isDiag {A : Matrix n n R} :
    A ∈ diagonalCartan R n ↔ A.IsDiag := Iff.rfl

/-- The entrywise description of the diagonal Cartan subalgebra. -/
theorem mem_diagonalCartan_iff {A : Matrix n n R} :
    A ∈ diagonalCartan R n ↔ ∀ i j, i ≠ j → A i j = 0 :=
  ⟨fun h _ _ hij => h hij, fun h _ _ hij => h _ _ hij⟩

/-- Every diagonal matrix lies in the diagonal Cartan subalgebra. -/
theorem diagonal_mem_diagonalCartan (d : n → R) : diagonal d ∈ diagonalCartan R n :=
  isDiag_diagonal d

/-- The diagonal matrix units lie in the diagonal Cartan subalgebra. -/
theorem single_self_mem_diagonalCartan (i : n) (c : R) : single i i c ∈ diagonalCartan R n := by
  rw [← diagonal_single]
  exact diagonal_mem_diagonalCartan _

instance : IsLieAbelian (diagonalCartan R n) where
  trivial A B := Subtype.ext (by simpa using lie_eq_zero_of_isDiag A.2 B.2)

/-! ### The adjoint action of the diagonal -/

/-- The adjoint action of a diagonal matrix is entrywise scaling: `⁅A, B⁆` has `(a, b)` entry
`(A a a - A b b) * B a b`. Every statement about weight spaces of `gl n R` for the diagonal Cartan
subalgebra ultimately comes from this formula. -/
theorem lie_apply_of_mem_diagonalCartan {A : Matrix n n R} (hA : A ∈ diagonalCartan R n)
    (B : Matrix n n R) (a b : n) : ⁅A, B⁆ a b = (A a a - A b b) * B a b := by
  obtain ⟨d, rfl⟩ : ∃ d, A = diagonal d :=
    ⟨diag A, (mem_diagonalCartan_iff_isDiag.mp hA).diagonal_diag.symm⟩
  simp only [LieRing.of_associative_ring_bracket, Matrix.sub_apply, diagonal_mul, mul_diagonal,
    diagonal_apply_eq]
  ring

/-- The matrix unit `Eᵢⱼ` is an eigenvector of `ad A` for every diagonal `A`, with eigenvalue the
difference `A i i - A j j` of the corresponding diagonal entries. This is the computation
underlying `TauCeti.single_mem_rootSpace`. -/
theorem lie_single_of_mem_diagonalCartan {A : Matrix n n R} (hA : A ∈ diagonalCartan R n)
    (i j : n) (c : R) : ⁅A, single i j c⁆ = (A i i - A j j) • single i j c := by
  ext a b
  rw [lie_apply_of_mem_diagonalCartan hA, Matrix.smul_apply, smul_eq_mul, single_apply]
  by_cases h : i = a ∧ j = b
  · obtain ⟨rfl, rfl⟩ := h; simp
  · simp [h]

/-! ### Self-normalizing, and the Cartan subalgebra instance -/

variable (R n)

/-- The diagonal Cartan subalgebra is self-normalizing: a matrix normalizing the diagonal matrices
is itself diagonal. -/
@[simp]
theorem diagonalCartan_normalizer_eq_self :
    (diagonalCartan R n).normalizer = diagonalCartan R n := by
  refine le_antisymm (fun X hX => mem_diagonalCartan_iff.mpr fun i j hij => ?_)
    (diagonalCartan R n).le_normalizer
  have h := (LieSubalgebra.mem_normalizer_iff _ X).mp hX _ (single_self_mem_diagonalCartan i 1)
  rw [mem_diagonalCartan_iff] at h
  have hentry : ⁅X, single i i (1 : R)⁆ i j = -X i j := by
    rw [LieRing.of_associative_ring_bracket]
    simp [Ne.symm hij]
  simpa [hentry] using h i j hij

/-- The diagonal matrices form a Cartan subalgebra of `gl n R`: they are nilpotent (indeed abelian)
and self-normalizing. -/
instance instIsCartanSubalgebraDiagonalCartan : (diagonalCartan R n).IsCartanSubalgebra where
  nilpotent := inferInstance
  self_normalizing := diagonalCartan_normalizer_eq_self R n

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

/-- `diagonalEquiv` sends a tuple to the corresponding diagonal matrix. -/
@[simp]
theorem diagonalEquiv_apply (d : n → R) :
    (diagonalEquiv R n d : Matrix n n R) = diagonal d := (rfl)

/-- The inverse of `diagonalEquiv` reads off the diagonal of a matrix. -/
@[simp]
theorem diagonalEquiv_symm_apply (A : diagonalCartan R n) :
    (diagonalEquiv R n).symm A = diag (A : Matrix n n R) := (rfl)

/-- The diagonal matrix units form a basis of the diagonal Cartan subalgebra. -/
noncomputable def diagonalCartanBasis : Module.Basis n R (diagonalCartan R n) :=
  Module.Basis.ofEquivFun (diagonalEquiv R n).symm

/-- The `i`-th vector of `diagonalCartanBasis` is the diagonal matrix unit `Eᵢᵢ`. -/
@[simp]
theorem diagonalCartanBasis_apply (i : n) :
    (diagonalCartanBasis R n i : Matrix n n R) = single i i 1 := by
  rw [diagonalCartanBasis, Module.Basis.coe_ofEquivFun, LinearEquiv.symm_symm, diagonalEquiv_apply,
    diagonal_single]

/-- The coordinates of a diagonal matrix in `diagonalCartanBasis` are its diagonal entries. -/
@[simp]
theorem diagonalCartanBasis_repr_apply (A : diagonalCartan R n) (i : n) :
    (diagonalCartanBasis R n).repr A i = (A : Matrix n n R) i i := by
  rw [diagonalCartanBasis, Module.Basis.ofEquivFun_repr_apply, diagonalEquiv_symm_apply, diag_apply]

instance : Module.Free R (diagonalCartan R n) :=
  Module.Free.of_basis (diagonalCartanBasis R n)

instance : Module.Finite R (diagonalCartan R n) :=
  Module.Finite.of_basis (diagonalCartanBasis R n)

/-- The diagonal Cartan subalgebra of `gl n R` has rank the number of indices. -/
theorem finrank_diagonalCartan [StrongRankCondition R] :
    Module.finrank R (diagonalCartan R n) = Fintype.card n := by
  rw [Module.finrank_eq_card_basis (diagonalCartanBasis R n)]

variable {R n}

/-- A diagonal matrix is the combination of the diagonal matrix units with its diagonal entries as
coefficients. -/
theorem sum_smul_diagonalCartanBasis (A : diagonalCartan R n) :
    ∑ i, (A : Matrix n n R) i i • diagonalCartanBasis R n i = A := by
  simpa using (diagonalCartanBasis R n).sum_repr A

/-! ### Weights of `gl n R` are `n`-tuples -/

variable (R n)

/-- Weights of `gl n R` are `n`-tuples: the linear equivalence sending `μ : n → R` to the functional
`A ↦ ∑ i, μ i * A i i` on the diagonal Cartan subalgebra, obtained by transporting the self-duality
`Module.Basis.toDualEquiv` of `diagonalCartanBasis` along `diagonalEquiv`. -/
noncomputable def glWeightEquiv : (n → R) ≃ₗ[R] Module.Dual R (diagonalCartan R n) :=
  (diagonalEquiv R n).trans (diagonalCartanBasis R n).toDualEquiv

variable {R n}

/-- The weight attached to `μ : n → R` pairs `μ` with the diagonal entries. -/
@[simp]
theorem glWeightEquiv_apply (mu : n → R) (A : diagonalCartan R n) :
    glWeightEquiv R n mu A = ∑ i, mu i * (A : Matrix n n R) i i := by
  conv_lhs => rw [← sum_smul_diagonalCartanBasis A]
  simp [glWeightEquiv, Module.Basis.toDual_apply_left, mul_comm]

/-- The tuple attached to a weight reads it off on the diagonal matrix units. -/
@[simp]
theorem glWeightEquiv_symm_apply (f : Module.Dual R (diagonalCartan R n)) (i : n) :
    (glWeightEquiv R n).symm f i = f (diagonalCartanBasis R n i) := by
  rw [glWeightEquiv, LinearEquiv.symm_trans_apply, diagonalEquiv_symm_apply, diag_apply,
    ← diagonalCartanBasis_repr_apply, ← Module.Basis.toDual_apply_left,
    ← Module.Basis.toDualEquiv_apply, LinearEquiv.apply_symm_apply]

variable (R n)

/-- The weight `εᵢ - εⱼ` of `gl n R`, as a functional on the diagonal Cartan subalgebra. For `i ≠ j`
these are the candidate roots of `gl n R`; over a nontrivial ring they are genuine roots, since
`TauCeti.single_mem_rootSpace` places the nonzero matrix unit `Eᵢⱼ` in the root space. For `i = j`
the functional is zero. -/
noncomputable def glRoot (i j : n) : Module.Dual R (diagonalCartan R n) :=
  glWeightEquiv R n (Pi.single i 1 - Pi.single j 1)

variable {R n}

/-- The functional `εᵢ - εⱼ` reads off the difference of two diagonal entries. -/
@[simp]
theorem glRoot_apply (i j : n) (A : diagonalCartan R n) :
    glRoot R n i j A = (A : Matrix n n R) i i - (A : Matrix n n R) j j := by
  simp only [glRoot, glWeightEquiv_apply, Pi.sub_apply, Pi.single_apply, sub_mul, ite_mul, one_mul,
    zero_mul, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- The functionals `εᵢ - εᵢ` vanish. -/
@[simp]
theorem glRoot_self (i : n) : glRoot R n i i = 0 := by
  ext A
  simp

/-- The matrix unit `Eᵢⱼ` lies in the root space of `gl n R`, relative to the diagonal Cartan, for
the weight `εᵢ - εⱼ`. For `i = j` this says that the diagonal Cartan lies in the zero root
space. -/
theorem single_mem_rootSpace (i j : n) (c : R) :
    single i j c ∈ LieAlgebra.rootSpace (diagonalCartan R n) (glRoot R n i j) := by
  rw [LieAlgebra.rootSpace, LieModule.mem_genWeightSpace]
  refine fun A => ⟨1, ?_⟩
  simp only [pow_one, LinearMap.sub_apply, LieModule.toEnd_apply_apply, LinearMap.smul_apply,
    Module.End.one_apply, LieSubalgebra.coe_bracket_of_module, glRoot_apply,
    lie_single_of_mem_diagonalCartan A.2 i j c, sub_self]

end TauCeti
