/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.RepresentationTheory.Quiver.Kronecker.PathAlgebra
public import Mathlib.Data.Matrix.Basis
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

* `TauCeti.Quiver.Kronecker.vertexEquiv`: the two vertices as indices in `Fin 2`, the target
  first.
* `TauCeti.Quiver.Kronecker.upperTriangularAlgEquiv`: the path algebra of the `A₂` quiver as the
  algebra of upper-triangular `2 × 2` matrices, that is, `Matrix.blockTriangularSubalgebra` for
  the identity ordering of `Fin 2`.

## Main results

* `TauCeti.Quiver.Kronecker.totalPath_eq_or`: the `A₂` quiver has exactly three paths, the two
  trivial ones and its arrow.
* `TauCeti.Quiver.Kronecker.upperTriangularAlgEquiv_vertexIdempotent_tgt`,
  `TauCeti.Quiver.Kronecker.upperTriangularAlgEquiv_vertexIdempotent_src` and
  `TauCeti.Quiver.Kronecker.upperTriangularAlgEquiv_ofArrow`: the identification sends the two
  vertex idempotents to the two diagonal matrix units and the arrow to the off-diagonal one.
* `TauCeti.Quiver.Kronecker.finrank_pathAlgebra_eq_three` and
  `TauCeti.Quiver.Kronecker.finrank_blockTriangularSubalgebra_eq_three`: both algebras are
  three-dimensional.

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

/-! ### Indexing the vertices, target first -/

/-- The two vertices of the generalized Kronecker quiver as indices in `Fin 2`, **the target
first**: `tgt` is `0` and `src` is `1`.

The order is the one that makes the path algebra upper triangular rather than lower triangular. A
path is sent to the matrix unit in the row of its target and the column of its source, because an
arrow acts on a left module from its source to its target; so the arrows, all of which run from
`src` to `tgt`, occupy entries above the diagonal exactly when `tgt` comes first. -/
def vertexEquiv : Kronecker A ≃ Fin 2 where
  toFun
    | .src => 1
    | .tgt => 0
  invFun i := if i = 0 then tgt else src
  left_inv v := by cases v <;> rfl
  right_inv i := by fin_cases i <;> rfl

@[simp]
theorem vertexEquiv_src : vertexEquiv (src : Kronecker A) = 1 :=
  -- The parentheses keep this an ordinary proof term rather than an exported `rfl` theorem, which
  -- would force `vertexEquiv` to be `@[expose]`.
  (rfl)

@[simp]
theorem vertexEquiv_tgt : vertexEquiv (tgt : Kronecker A) = 0 := (rfl)

/-! ### Collapsing the paths onto the matrix units -/

section ToMatrix

variable (k : Type w) [CommSemiring k]

/-- The linear map sending a path to the matrix unit in the row of its target and the column of
its source. -/
private noncomputable def toMatrixLinear :
    pathAlgebra k (Kronecker A) →ₗ[k] Matrix (Fin 2) (Fin 2) k :=
  (pathAlgebraBasis k (Kronecker A)).constr k fun x =>
    Matrix.single (vertexEquiv x.2.1) (vertexEquiv x.1) 1

private theorem toMatrixLinear_single (x : Quiver.TotalPath (Kronecker A)) (c : k) :
    toMatrixLinear k (PathAlgebra.single x c)
      = Matrix.single (vertexEquiv x.2.1) (vertexEquiv x.1) c := by
  have hb : pathAlgebraBasis k (Kronecker A) x = PathAlgebra.ofPath x :=
    congrFun (coe_pathAlgebraBasis k (Kronecker A)) x
  have hx : (PathAlgebra.single x c : pathAlgebra k (Kronecker A))
      = c • pathAlgebraBasis k (Kronecker A) x := by
    rw [hb, PathAlgebra.ofPath_eq_single, PathAlgebra.smul_single, mul_one]
  rw [hx, map_smul, toMatrixLinear, Module.Basis.constr_basis, Matrix.smul_single, smul_eq_mul,
    mul_one]

/-- The two vertex idempotents go to the two diagonal matrix units, which sum to the identity
matrix. -/
private theorem toMatrixLinear_one :
    toMatrixLinear k (1 : pathAlgebra k (Kronecker A)) = 1 := by
  rw [PathAlgebra.one_def, sum_univ, map_add, PathAlgebra.vertexIdempotent_eq_single,
    PathAlgebra.vertexIdempotent_eq_single, toMatrixLinear_single, toMatrixLinear_single,
    ← Matrix.sum_single_one, Fin.sum_univ_two]
  simp [add_comm]

/-- Concatenation of paths becomes multiplication of matrix units: two paths meet exactly when the
column of the first matrix unit is the row of the second, since `vertexEquiv` is injective. -/
private theorem toMatrixLinear_mul (f g : pathAlgebra k (Kronecker A)) :
    toMatrixLinear k (f * g) = toMatrixLinear k f * toMatrixLinear k g := by
  induction f using PathAlgebra.induction_linear with
  | zero => simp
  | add f₁ f₂ ih₁ ih₂ => simp [add_mul, ih₁, ih₂]
  | single x r =>
    induction g using PathAlgebra.induction_linear with
    | zero => simp
    | add g₁ g₂ ih₁ ih₂ => simp [mul_add, ih₁, ih₂]
    | single y s =>
      by_cases h : y.2.1 = x.1
      · obtain ⟨x₁, x₂, p⟩ := x
        obtain ⟨y₁, y₂, q⟩ := y
        subst h
        rw [PathAlgebra.single_mul_single_of_comp, toMatrixLinear_single, toMatrixLinear_single,
          toMatrixLinear_single, Matrix.single_mul_single_same]
      · have hne : vertexEquiv x.1 ≠ vertexEquiv y.2.1 :=
          fun hc => h (vertexEquiv.injective hc).symm
        rw [PathAlgebra.single_mul_single_of_not_composable h, map_zero, toMatrixLinear_single,
          toMatrixLinear_single, Matrix.single_mul_single_of_ne (h := hne)]

/-- The path algebra of the generalized Kronecker quiver as `2 × 2` matrices: a path goes to the
matrix unit in the row of its target and the column of its source. -/
private noncomputable def toMatrixAlgHom :
    pathAlgebra k (Kronecker A) →ₐ[k] Matrix (Fin 2) (Fin 2) k :=
  AlgHom.ofLinearMap (toMatrixLinear k) (toMatrixLinear_one k) (toMatrixLinear_mul k)

private theorem toMatrixAlgHom_single (x : Quiver.TotalPath (Kronecker A)) (c : k) :
    toMatrixAlgHom k (PathAlgebra.single x c)
      = Matrix.single (vertexEquiv x.2.1) (vertexEquiv x.1) c :=
  toMatrixLinear_single k x c

end ToMatrix

/-! ### The three paths of the `A₂` quiver -/

variable [Unique A]

/-- The `A₂` quiver has exactly three paths: the trivial path at each vertex, and its arrow. -/
theorem totalPath_eq_or (x : Quiver.TotalPath (Kronecker A)) :
    x = ⟨tgt, tgt, Path.nil⟩ ∨ x = ⟨src, tgt, arrowPath default⟩ ∨
      x = ⟨src, src, Path.nil⟩ := by
  obtain ⟨a, b, p⟩ := x
  cases a <;> cases b
  · exact Or.inr (Or.inr (by rw [path_src_src_eq_nil p]))
  · refine Or.inr (Or.inl ?_)
    have h := arrowPath_pathEquivArrow p
    rw [Unique.eq_default (pathEquivArrow p)] at h
    rw [h]
  · exact isEmptyElim p
  · exact Or.inl (by rw [path_tgt_tgt_eq_nil p])

/-! ### The identification with the upper-triangular matrices -/

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

private theorem range_toMatrixAlgHom :
    (toMatrixAlgHom (A := A) k).range
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

/-- The identification sends a path to the matrix unit in the row of its target and the column of
its source. -/
@[simp]
theorem upperTriangularAlgEquiv_single (x : Quiver.TotalPath (Kronecker A)) (c : k) :
    (upperTriangularAlgEquiv (A := A) k (PathAlgebra.single x c) : Matrix (Fin 2) (Fin 2) k)
      = Matrix.single (vertexEquiv x.2.1) (vertexEquiv x.1) c :=
  toMatrixAlgHom_single k x c

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

/-- The path algebra of the `A₂` quiver is three-dimensional: the two trivial paths and the
arrow. -/
theorem finrank_pathAlgebra_eq_three :
    Module.finrank k (pathAlgebra k (Kronecker A)) = 3 := by
  letI : Fintype A := Fintype.ofFinite A
  rw [TauCeti.finrank_pathAlgebra k, card_totalPath, Fintype.card_unique]

/-- The algebra of upper-triangular `2 × 2` matrices is three-dimensional. -/
theorem finrank_blockTriangularSubalgebra_eq_three :
    Module.finrank k (Matrix.blockTriangularSubalgebra k k (id : Fin 2 → Fin 2)) = 3 := by
  rw [← (upperTriangularAlgEquiv (A := Unit) k).toLinearEquiv.finrank_eq]
  exact finrank_pathAlgebra_eq_three k

end Field

end Quiver.Kronecker

end TauCeti
