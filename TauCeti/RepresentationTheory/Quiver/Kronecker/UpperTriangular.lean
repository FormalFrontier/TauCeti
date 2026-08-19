/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Kronecker.PathAlgebra
public import Mathlib.LinearAlgebra.Matrix.Block

/-!
# The path algebra of the `A₂` quiver

The `A₂` quiver `• → •` is the generalized Kronecker quiver on a one-element arrow type. Its path
algebra has the two trivial paths and the single arrow as a basis, and this file identifies it with
the three-dimensional algebra of upper-triangular `2 × 2` matrices.

The identification sends a path from `a` to `b` to the matrix unit `E_{b,a}`, in the row of its
*target* and the column of its *source*: with the *later factor first* convention of
`TauCeti.pathAlgebra`, an arrow acts on a left module by carrying the component at its source to
the component at its target, so it is the target that indexes the row. The single arrow runs from
`src` to `tgt`, so the matrices are upper triangular exactly when `tgt` is indexed **before**
`src`; that is the ordering `TauCeti.Quiver.Kronecker.vertexEquiv` fixes.

## Main definitions

* `TauCeti.Quiver.Kronecker.upperTriangularAlgEquiv`: the path algebra of the `A₂` quiver as the
  algebra of upper-triangular `2 × 2` matrices, that is, `Matrix.blockTriangularSubalgebra` for
  the identity ordering of `Fin 2`.

## Main results

* `TauCeti.Quiver.Kronecker.upperTriangularAlgEquiv_symm_apply`: the inverse identification reads
  a matrix off as the combination of the three paths given by its entries on and above the
  diagonal.
* `TauCeti.Quiver.Kronecker.upperTriangularAlgEquiv_vertexIdempotent_tgt`,
  `TauCeti.Quiver.Kronecker.upperTriangularAlgEquiv_vertexIdempotent_src` and
  `TauCeti.Quiver.Kronecker.upperTriangularAlgEquiv_ofArrow`: the identification sends the two
  vertex idempotents to the two diagonal matrix units and the arrow to the off-diagonal one.
* `TauCeti.Quiver.Kronecker.finrank_blockTriangularSubalgebra_eq_three`: the algebra of
  upper-triangular `2 × 2` matrices is three-dimensional, transporting
  `TauCeti.Quiver.Kronecker.finrank_pathAlgebra_eq_three` along the identification.

## References

This file supplies the “`A₂` quiver” worked example of
`TauCetiRoadmap/RepresentationTheory/QuiverRepresentations/README.md`, which asks for the path
algebra of `• → •` as the three-dimensional algebra of upper-triangular `2 × 2` matrices. See
Assem--Simson--Skowroński, *Elements of the Representation Theory of Associative Algebras I*,
Ch. II.
-/

public section

namespace TauCeti

open _root_.Quiver

universe v w

namespace Quiver.Kronecker

variable {A : Type v}

/-! ### Collapsing the paths onto the matrix units -/

section ToMatrix

variable (k : Type w) [CommSemiring k]

/-- The matrix unit a path goes to: the one in the row of its target and the column of its
source. -/
private def toMatrixUnit (x : Quiver.TotalPath (Kronecker A)) : Matrix (Fin 2) (Fin 2) k :=
  Matrix.single (vertexEquiv x.2.1) (vertexEquiv x.1) 1

/-- Concatenation of paths becomes multiplication of matrix units, the column of the first being
the row of the second. -/
private theorem toMatrixUnit_mul_toMatrixUnit_of_comp {a b c : Kronecker A} (p : Path a b)
    (q : Path c a) :
    toMatrixUnit k ⟨a, b, p⟩ * toMatrixUnit k ⟨c, a, q⟩ = toMatrixUnit k ⟨c, b, q.comp p⟩ := by
  rw [toMatrixUnit, toMatrixUnit, toMatrixUnit, Matrix.single_mul_single_same, one_mul]

/-- Two paths that do not meet go to matrix units whose product vanishes, since `vertexEquiv` is
injective. -/
private theorem toMatrixUnit_mul_toMatrixUnit_of_not_composable
    {x y : Quiver.TotalPath (Kronecker A)} (h : y.2.1 ≠ x.1) :
    toMatrixUnit k x * toMatrixUnit k y = 0 := by
  have hne : vertexEquiv x.1 ≠ vertexEquiv y.2.1 := fun hc => h (vertexEquiv.injective hc).symm
  rw [toMatrixUnit, toMatrixUnit, Matrix.single_mul_single_of_ne (h := hne)]

/-- The two trivial paths go to the two diagonal matrix units, which sum to the identity matrix.
The enumeration is left arbitrary, as `TauCeti.PathAlgebra.liftAlgHom` asks for this over any one:
`TauCeti.Quiver.Kronecker.vertexEquiv` transports the sum to the one over `Fin 2`. -/
private theorem sum_toMatrixUnit_nil (fq : Fintype (Kronecker A)) :
    ∑ v ∈ @Finset.univ (Kronecker A) fq,
        toMatrixUnit k (⟨v, v, Path.nil⟩ : Quiver.TotalPath (Kronecker A)) = 1 :=
  (Fintype.sum_equiv vertexEquiv _ (fun i => Matrix.single i i (1 : k)) fun _ => rfl).trans
    Matrix.sum_single_one

/-- The path algebra of the generalized Kronecker quiver as `2 × 2` matrices: a path goes to the
matrix unit in the row of its target and the column of its source. This is the universal property
`TauCeti.PathAlgebra.liftAlgHom` applied to `toMatrixUnit`. -/
private noncomputable def toMatrixAlgHom :
    pathAlgebra k (Kronecker A) →ₐ[k] Matrix (Fin 2) (Fin 2) k :=
  PathAlgebra.liftAlgHom k (toMatrixUnit k) (toMatrixUnit_mul_toMatrixUnit_of_comp k)
    (toMatrixUnit_mul_toMatrixUnit_of_not_composable k)
    (by intro fq; exact sum_toMatrixUnit_nil k fq)

private theorem toMatrixAlgHom_single (x : Quiver.TotalPath (Kronecker A)) (c : k) :
    toMatrixAlgHom k (PathAlgebra.single x c)
      = Matrix.single (vertexEquiv x.2.1) (vertexEquiv x.1) c := by
  rw [toMatrixAlgHom, PathAlgebra.liftAlgHom_single, toMatrixUnit, Matrix.smul_single,
    smul_eq_mul, mul_one]

end ToMatrix

/-! ### The identification with the upper-triangular matrices -/

variable [Unique A]

section AlgEquiv

variable (k : Type w) [CommSemiring k]

/-- The linear map assembling a matrix into a combination of the three paths of the `A₂` quiver.
It inverts `toMatrixAlgHom` on the upper-triangular matrices, discarding the entry below the
diagonal, which no path reaches. -/
private noncomputable def ofMatrixLinear :
    Matrix (Fin 2) (Fin 2) k →ₗ[k] pathAlgebra k (Kronecker A) where
  toFun M :=
    PathAlgebra.single ⟨tgt, tgt, Path.nil⟩ (M 0 0)
      + PathAlgebra.single ⟨src, tgt, arrowPath default⟩ (M 0 1)
      + PathAlgebra.single ⟨src, src, Path.nil⟩ (M 1 1)
  map_add' M N := by
    simp only [Matrix.add_apply, PathAlgebra.single_add]
    abel
  map_smul' r M := by
    simp only [Matrix.smul_apply, smul_eq_mul, RingHom.id_apply, smul_add,
      PathAlgebra.smul_single]

private theorem ofMatrixLinear_toMatrixAlgHom (f : pathAlgebra k (Kronecker A)) :
    ofMatrixLinear k (toMatrixAlgHom k f) = f := by
  induction f using PathAlgebra.induction_linear with
  | zero => simp
  | add f g ihf ihg => rw [map_add, map_add, ihf, ihg]
  | single x c =>
    rcases totalPath_eq_or x with h | h | h <;> subst h <;>
      simp [toMatrixAlgHom_single, ofMatrixLinear]

private theorem toMatrixAlgHom_ofMatrixLinear {M : Matrix (Fin 2) (Fin 2) k}
    (hM : M.BlockTriangular (id : Fin 2 → Fin 2)) :
    toMatrixAlgHom k (ofMatrixLinear (A := A) k M) = M := by
  have h₁₀ : M 1 0 = 0 := hM (by norm_num)
  rw [ofMatrixLinear]
  simp only [LinearMap.coe_mk, AddHom.coe_mk, map_add, toMatrixAlgHom_single, vertexEquiv_src,
    vertexEquiv_tgt]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h₁₀]

private theorem range_toMatrixAlgHom : (toMatrixAlgHom (A := A) k).range
      = Matrix.blockTriangularSubalgebra k k (id : Fin 2 → Fin 2) := by
  refine le_antisymm ?_ fun M hM => ⟨ofMatrixLinear k M, toMatrixAlgHom_ofMatrixLinear k hM⟩
  rintro _ ⟨f, rfl⟩
  rw [Matrix.mem_blockTriangularSubalgebra]
  induction f using PathAlgebra.induction_linear with
  | zero => simp
  | add f g ihf ihg => simpa [map_add] using ihf.add ihg
  | single x c =>
    rcases totalPath_eq_or x with h | h | h <;> subst h <;>
      simpa [toMatrixAlgHom_single] using Matrix.blockTriangular_single (by norm_num) c

/-- **The path algebra of the `A₂` quiver is the algebra of upper-triangular `2 × 2` matrices.**
A path goes to the matrix unit in the row of its target and the column of its source, so the two
vertex idempotents go to the two diagonal matrix units and the arrow to the entry above the
diagonal. -/
noncomputable def upperTriangularAlgEquiv :
    pathAlgebra k (Kronecker A) ≃ₐ[k] Matrix.blockTriangularSubalgebra k k (id : Fin 2 → Fin 2) :=
  (AlgEquiv.ofInjective (toMatrixAlgHom k)
        (Function.LeftInverse.injective (ofMatrixLinear_toMatrixAlgHom k))).trans
    (Subalgebra.equivOfEq _ _ (range_toMatrixAlgHom k))

private theorem coe_upperTriangularAlgEquiv (f : pathAlgebra k (Kronecker A)) :
    (upperTriangularAlgEquiv (A := A) k f : Matrix (Fin 2) (Fin 2) k) = toMatrixAlgHom k f := by
  rw [upperTriangularAlgEquiv, AlgEquiv.trans_apply, Subalgebra.equivOfEq_apply,
    AlgEquiv.ofInjective_apply]

/-- The identification sends a path to the matrix unit in the row of its target and the column of
its source. -/
@[simp]
theorem upperTriangularAlgEquiv_single (x : Quiver.TotalPath (Kronecker A)) (c : k) :
    (upperTriangularAlgEquiv (A := A) k (PathAlgebra.single x c) : Matrix (Fin 2) (Fin 2) k)
      = Matrix.single (vertexEquiv x.2.1) (vertexEquiv x.1) c := by
  rw [coe_upperTriangularAlgEquiv, toMatrixAlgHom_single]

/-- The inverse identification reads an upper-triangular matrix off as a combination of the three
paths: the two diagonal entries carry the trivial paths, and the entry above the diagonal carries
the arrow. The entry below the diagonal, which vanishes, is reached by no path. -/
@[simp]
theorem upperTriangularAlgEquiv_symm_apply
    (M : Matrix.blockTriangularSubalgebra k k (id : Fin 2 → Fin 2)) :
    (upperTriangularAlgEquiv (A := A) k).symm M
      = PathAlgebra.single ⟨tgt, tgt, Path.nil⟩ ((M : Matrix (Fin 2) (Fin 2) k) 0 0)
        + PathAlgebra.single ⟨src, tgt, arrowPath default⟩ ((M : Matrix (Fin 2) (Fin 2) k) 0 1)
        + PathAlgebra.single ⟨src, src, Path.nil⟩ ((M : Matrix (Fin 2) (Fin 2) k) 1 1) := by
  rw [AlgEquiv.symm_apply_eq]
  refine Subtype.ext ?_
  rw [coe_upperTriangularAlgEquiv]
  exact (toMatrixAlgHom_ofMatrixLinear (A := A) k
    (Matrix.mem_blockTriangularSubalgebra.mp M.2)).symm

/-- The vertex idempotent at the target goes to the first diagonal matrix unit. -/
@[simp]
theorem upperTriangularAlgEquiv_vertexIdempotent_tgt :
    (upperTriangularAlgEquiv (A := A) k (PathAlgebra.vertexIdempotent k tgt) :
        Matrix (Fin 2) (Fin 2) k) = Matrix.single 0 0 1 := by
  rw [PathAlgebra.vertexIdempotent_eq_single, upperTriangularAlgEquiv_single, vertexEquiv_tgt]

/-- The vertex idempotent at the source goes to the second diagonal matrix unit. -/
@[simp]
theorem upperTriangularAlgEquiv_vertexIdempotent_src :
    (upperTriangularAlgEquiv (A := A) k (PathAlgebra.vertexIdempotent k src) :
        Matrix (Fin 2) (Fin 2) k) = Matrix.single 1 1 1 := by
  rw [PathAlgebra.vertexIdempotent_eq_single, upperTriangularAlgEquiv_single, vertexEquiv_src]

/-- The arrow goes to the matrix unit above the diagonal: it is the arrow that makes the algebra
triangular rather than diagonal.

This is not `@[simp]`: its left-hand side is not in simp-normal form, since `ofArrow_eq_ofPath`
and `toPath_arrow` rewrite an arrow to the length-one path it traces. -/
theorem upperTriangularAlgEquiv_ofArrow (a : A) :
    (upperTriangularAlgEquiv (A := A) k (PathAlgebra.ofArrow (arrow a)) :
        Matrix (Fin 2) (Fin 2) k) = Matrix.single 0 1 1 := by
  rw [PathAlgebra.ofArrow_eq_ofPath, toPath_arrow, PathAlgebra.ofPath_eq_single,
    upperTriangularAlgEquiv_single, vertexEquiv_src, vertexEquiv_tgt]

end AlgEquiv

/-! ### The dimension -/

section Field

variable (k : Type w) [Field k]

/-- The algebra of upper-triangular `2 × 2` matrices is three-dimensional, since it is the path
algebra of the `A₂` quiver. -/
theorem finrank_blockTriangularSubalgebra_eq_three :
    Module.finrank k (Matrix.blockTriangularSubalgebra k k (id : Fin 2 → Fin 2)) = 3 := by
  rw [← (upperTriangularAlgEquiv (A := Unit) k).toLinearEquiv.finrank_eq]
  exact finrank_pathAlgebra_eq_three (A := Unit) k

end Field

end Quiver.Kronecker

end TauCeti
