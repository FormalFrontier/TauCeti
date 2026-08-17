/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Constructions
public import TauCeti.Algebra.Coalgebra.Comodule.Flag.Basic
public import TauCeti.Algebra.Coalgebra.Subcomodule.Induced

/-!
# Upper-unitriangular comodule structures and extensions

An extension of upper-unitriangular comodules is again upper unitriangular. More explicitly, let
`N` be a subcomodule of `M`. A basis of `N` and a basis of `M ⧸ N` combine, using Mathlib's
`Module.Basis.sumQuot`, into a basis of `M`. If the coefficient matrices on the subcomodule and
quotient are upper unitriangular, then the combined coefficient matrix is upper unitriangular.

The coefficient matrix has the expected block form. Its diagonal blocks are the coefficient
matrices of `N` and `M ⧸ N`, its lower-left block is zero because `N` is stable, and its
upper-right block records the extension class.

This is the extension step needed by the Kolchin induction in Layer 5, "Unipotent groups", of the
ReductiveGroups roadmap. A fixed line supplies the first upper-unitriangular block; applying the
induction hypothesis to the quotient and this file to the resulting extension constructs the
complete invariant flag.

## Main declarations

* `TauCeti.Comodule.extensionBasis`: the basis of a comodule obtained from bases of a subcomodule
  and its quotient.
* `TauCeti.Comodule.coefficientMatrix_extensionBasis_castAdd_castAdd`: the subcomodule diagonal
  block.
* `TauCeti.Comodule.coefficientMatrix_extensionBasis_natAdd_natAdd`: the quotient diagonal block.
* `TauCeti.Comodule.coefficientMatrix_extensionBasis_natAdd_castAdd`: the vanishing lower-left
  block.
* `TauCeti.Comodule.coefficientMatrix_extensionBasis_isUpperUnitriangular`: closure of
  upper-unitriangular comodule structures under extensions.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, I.2.
* T. A. Springer, *Linear Algebraic Groups*, §2.4.
-/

public section

namespace TauCeti.Comodule

open Module

universe u v w

noncomputable section

attribute [local instance 1100] Module.Free.of_divisionRing Module.Flat.of_free

variable {k : Type u} {C : Type v} {M : Type w} {m n : ℕ}
variable [Field k]
variable [AddCommGroup C] [Module k C] [Coalgebra k C]
variable [AddCommGroup M] [Module k M] [Comodule k C M]

/-- The tautological linear equivalence between a subcomodule and the subtype of its exposed
underlying submodule. -/
private def toSubmoduleEquiv (N : Subcomodule k C M) : N ≃ₗ[k] N.toSubmodule where
  toFun x := ⟨x, x.2⟩
  invFun x := ⟨x, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- A basis of a subcomodule, regarded as a basis of its exposed underlying submodule. -/
private def toSubmoduleBasis (N : Subcomodule k C M) (bN : Basis (Fin m) k N) :
    Basis (Fin m) k N.toSubmodule :=
  bN.map (toSubmoduleEquiv N)

@[simp]
private theorem toSubmoduleBasis_apply (N : Subcomodule k C M) (bN : Basis (Fin m) k N)
    (i : Fin m) : ((toSubmoduleBasis N bN i : N.toSubmodule) : M) = bN i := by
  rfl

/-- The basis of a comodule obtained by putting a basis of a subcomodule before chosen lifts of a
basis of the quotient. The construction is Mathlib's `Module.Basis.sumQuot`, reindexed by the
standard equivalence `Fin m ⊕ Fin n ≃ Fin (m + n)`. -/
def extensionBasis (N : Subcomodule k C M) (bN : Basis (Fin m) k N)
    (bQ : Basis (Fin n) k (M ⧸ N.toSubmodule)) : Basis (Fin (m + n)) k M :=
  ((toSubmoduleBasis N bN).sumQuot bQ).reindex finSumFinEquiv

/-- On the first block, `extensionBasis` is the given basis of the subcomodule. -/
@[simp]
theorem extensionBasis_castAdd (N : Subcomodule k C M) (bN : Basis (Fin m) k N)
    (bQ : Basis (Fin n) k (M ⧸ N.toSubmodule)) (i : Fin m) :
    extensionBasis N bN bQ (Fin.castAdd n i) = bN i := by
  rw [extensionBasis, Basis.reindex_apply, finSumFinEquiv_symm_apply_castAdd,
    Basis.sumQuot_inl]
  exact toSubmoduleBasis_apply N bN i

/-- On the second block, the quotient classes of `extensionBasis` are the given quotient basis. -/
@[simp]
theorem extensionBasis_natAdd_mkQ (N : Subcomodule k C M) (bN : Basis (Fin m) k N)
    (bQ : Basis (Fin n) k (M ⧸ N.toSubmodule)) (j : Fin n) :
    Submodule.Quotient.mk (extensionBasis N bN bQ (Fin.natAdd m j)) = bQ j := by
  rw [extensionBasis, Basis.reindex_apply, finSumFinEquiv_symm_apply_natAdd,
    Basis.sumQuot_inr]

/-- The first-block coordinates of an element of the subcomodule in `extensionBasis` are its
coordinates in the given subcomodule basis. -/
@[simp]
theorem extensionBasis_repr_castAdd (N : Subcomodule k C M) (bN : Basis (Fin m) k N)
    (bQ : Basis (Fin n) k (M ⧸ N.toSubmodule)) (x : N) (i : Fin m) :
    (extensionBasis N bN bQ).repr x (Fin.castAdd n i) = bN.repr x i := by
  rw [extensionBasis, Basis.repr_reindex_apply, finSumFinEquiv_symm_apply_castAdd]
  -- `N` and the subtype of `N.toSubmodule` have different wrappers, so expose the tautological
  -- equivalence before applying Mathlib's quotient-basis coordinate theorem.
  change (((toSubmoduleBasis N bN).sumQuot bQ).repr
    ((toSubmoduleEquiv N x : N.toSubmodule) : M)) (Sum.inl i) = bN.repr x i
  rw [Basis.sumQuot_repr_inl]
  rfl

/-- The second-block coordinates in `extensionBasis` are the coordinates of the quotient class. -/
@[simp]
theorem extensionBasis_repr_natAdd (N : Subcomodule k C M) (bN : Basis (Fin m) k N)
    (bQ : Basis (Fin n) k (M ⧸ N.toSubmodule)) (x : M) (j : Fin n) :
    (extensionBasis N bN bQ).repr x (Fin.natAdd m j) =
      bQ.repr (N.toSubmodule.mkQ x) j := by
  rw [extensionBasis, Basis.repr_reindex_apply, finSumFinEquiv_symm_apply_natAdd,
    Basis.sumQuot_repr_inr]

/-- The subcomodule diagonal block of the combined coefficient matrix is the coefficient matrix
in the given subcomodule basis. -/
@[simp]
theorem coefficientMatrix_extensionBasis_castAdd_castAdd
    (N : Subcomodule k C M) (bN : Basis (Fin m) k N)
    (bQ : Basis (Fin n) k (M ⧸ N.toSubmodule)) (i j : Fin m) :
    coefficientMatrix (C := C) (extensionBasis N bN bQ)
        (Fin.castAdd n i) (Fin.castAdd n j) =
      coefficientMatrix (C := C) bN i j := by
  rw [coefficientMatrix_apply, extensionBasis_castAdd, coefficientMatrix_apply]
  rw [← N.subtype_apply (bN j), matrixCoefficient_map]
  congr 2
  ext x
  simp only [LinearMap.comp_apply, Subcomodule.subtype_toLinearMap,
    SMulMemClass.subtype_apply, Basis.coord_apply, extensionBasis_repr_castAdd]

/-- The lower-left block of the combined coefficient matrix vanishes. This is the matrix form of
stability of the subcomodule. -/
@[simp]
theorem coefficientMatrix_extensionBasis_natAdd_castAdd
    (N : Subcomodule k C M) (bN : Basis (Fin m) k N)
    (bQ : Basis (Fin n) k (M ⧸ N.toSubmodule)) (i : Fin n) (j : Fin m) :
    coefficientMatrix (C := C) (extensionBasis N bN bQ)
        (Fin.natAdd m i) (Fin.castAdd n j) = 0 := by
  rw [coefficientMatrix_apply, extensionBasis_castAdd, ← N.subtype_apply (bN j),
    matrixCoefficient_map]
  have hcoord :
      ((extensionBasis N bN bQ).coord (Fin.natAdd m i)).comp N.subtype.toLinearMap = 0 := by
    ext x
    simp only [LinearMap.comp_apply, Subcomodule.subtype_toLinearMap,
      SMulMemClass.subtype_apply, Basis.coord_apply, extensionBasis_repr_natAdd,
      LinearMap.zero_apply]
    have hx : N.toSubmodule.mkQ (x : M) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr x.2
    rw [hx, map_zero, Finsupp.zero_apply]
  rw [hcoord]
  simp

/-- The quotient diagonal block of the combined coefficient matrix is the coefficient matrix in
the given quotient basis. -/
@[simp]
theorem coefficientMatrix_extensionBasis_natAdd_natAdd
    (N : Subcomodule k C M) (bN : Basis (Fin m) k N)
    (bQ : Basis (Fin n) k (M ⧸ N.toSubmodule)) (i j : Fin n) :
    coefficientMatrix (C := C) (extensionBasis N bN bQ)
        (Fin.natAdd m i) (Fin.natAdd m j) =
      coefficientMatrix (C := C) bQ i j := by
  rw [coefficientMatrix_apply, coefficientMatrix_apply]
  have hcoord :
      (bQ.coord i).comp N.mkQ.toLinearMap =
        (extensionBasis N bN bQ).coord (Fin.natAdd m i) := by
    ext x
    simp only [LinearMap.comp_apply, Subcomodule.mkQ_toLinearMap, Basis.coord_apply,
      Submodule.mkQ_apply, extensionBasis_repr_natAdd]
  calc
    matrixCoefficient (R := k) (C := C)
        ((extensionBasis N bN bQ).coord (Fin.natAdd m i))
        (extensionBasis N bN bQ (Fin.natAdd m j)) =
      matrixCoefficient (R := k) (C := C) (bQ.coord i)
        (N.mkQ (extensionBasis N bN bQ (Fin.natAdd m j))) := by
          rw [matrixCoefficient_map, hcoord]
    _ = matrixCoefficient (R := k) (C := C) (bQ.coord i) (bQ j) := by
      rw [N.mkQ_apply, extensionBasis_natAdd_mkQ]

variable [One C]

/-- If the induced coefficient matrices on a subcomodule and its quotient are upper
unitriangular, then the coefficient matrix on their combined basis is upper unitriangular. -/
theorem coefficientMatrix_extensionBasis_isUpperUnitriangular
    (N : Subcomodule k C M) (bN : Basis (Fin m) k N)
    (bQ : Basis (Fin n) k (M ⧸ N.toSubmodule))
    (hN : (coefficientMatrix (C := C) bN).IsUpperUnitriangular)
    (hQ : (coefficientMatrix (C := C) bQ).IsUpperUnitriangular) :
    (coefficientMatrix (C := C) (extensionBasis N bN bQ)).IsUpperUnitriangular := by
  rw [Matrix.isUpperUnitriangular_def]
  constructor
  · intro i j hji
    obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
    obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
    cases i with
    | inl i =>
        cases j with
        | inl j =>
            rw [finSumFinEquiv_apply_left, finSumFinEquiv_apply_left,
              coefficientMatrix_extensionBasis_castAdd_castAdd]
            simp only [finSumFinEquiv_apply_left] at hji
            exact hN.isUpperTriangular ((Fin.strictMono_castAdd n).lt_iff_lt.mp hji)
        | inr j =>
            rw [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right] at hji
            -- The two `Fin` embeddings do not simplify through `<`; their underlying indices
            -- make the impossible cross-block inequality explicit.
            change m + j.val < i.val at hji
            omega
    | inr i =>
        cases j with
        | inl j =>
            rw [finSumFinEquiv_apply_right, finSumFinEquiv_apply_left,
              coefficientMatrix_extensionBasis_natAdd_castAdd]
        | inr j =>
            rw [finSumFinEquiv_apply_right, finSumFinEquiv_apply_right,
              coefficientMatrix_extensionBasis_natAdd_natAdd]
            simp only [finSumFinEquiv_apply_right] at hji
            exact hQ.isUpperTriangular ((Fin.strictMono_natAdd m).lt_iff_lt.mp hji)
  · intro i
    obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
    cases i with
    | inl i =>
        rw [finSumFinEquiv_apply_left, coefficientMatrix_extensionBasis_castAdd_castAdd]
        exact hN.apply_diag i
    | inr i =>
        rw [finSumFinEquiv_apply_right, coefficientMatrix_extensionBasis_natAdd_natAdd]
        exact hQ.apply_diag i

end

end TauCeti.Comodule
