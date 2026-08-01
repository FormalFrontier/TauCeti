/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Category.CommBialgCat
public import Mathlib.LinearAlgebra.Matrix.MvPolynomial
public import Mathlib.RingTheory.Coalgebra.GroupLike

/-!
# The matrix-monoid coordinate bialgebra

For a commutative semiring `R`, this file equips the polynomial coordinate algebra
`R[Xᵢⱼ]` of square matrices with the explicit bialgebra structure dual to matrix
multiplication. Its comultiplication and counit satisfy

`Δ(Xᵢⱼ) = ∑ₖ Xᵢₖ ⊗ Xₖⱼ` and `ε(Xᵢⱼ) = if i = j then 1 else 0`.

The structure is a named `Bialgebra` value rather than a global instance. This distinction is
essential: `MvPolynomial` is definitionally an additive monoid algebra, and importing the
monoid-algebra bialgebra gives its variables a different, group-like comultiplication. Over a
commutative ring, `coordinateBialgebra` locally selects the matrix-coordinate structure and
stores it in a `CommBialgCat` object, providing a collision-free boundary for statements using
typeclass-selected coalgebra operations.

The determinant of the generic matrix is group-like for this bundled structure. This is the
algebraic input for subsequently localizing at the determinant to construct the coordinate Hopf
algebra of `GLₙ`; localization and the antipode are deliberately not constructed here.

The construction includes `n = 0` and requires no nontriviality hypothesis on the base.

## Main declarations

* `TauCeti.MatrixMonoid.comul`: matrix-multiplication comultiplication on `R[Xᵢⱼ]`.
* `TauCeti.MatrixMonoid.counit`: identity-matrix counit on `R[Xᵢⱼ]`.
* `TauCeti.MatrixMonoid.bialgebra`: the explicit matrix-coordinate bialgebra dictionary.
* `TauCeti.MatrixMonoid.coordinateBialgebra`: the selected commutative bialgebra object.
* `TauCeti.MatrixMonoid.isGroupLikeElem_determinant`: the generic determinant is group-like.

## References

The coordinate formulas are standard; see J. S. Milne, *Algebraic Groups*, §§3.3--3.6 and
4.2. The same construction appears in the Stacks Project, Example 39.5.4,
[Tag 022W](https://stacks.math.columbia.edu/tag/022W). The role of determinant localization in
constructing `GLₙ` is described in Milne, §2.8.
-/

public section

open scoped TensorProduct

namespace TauCeti

namespace MatrixMonoid

open Algebra.TensorProduct

universe u

/-- The polynomial coordinate algebra of the monoid of `n × n` matrices over `R`. -/
abbrev CoordinateRing (R : Type u) [CommSemiring R] (n : ℕ) :=
  MvPolynomial (Fin n × Fin n) R

section Semiring

variable (R : Type u) [CommSemiring R] (n : ℕ)

/-- The generic `n × n` matrix, whose `(i, j)` entry is the variable `X (i, j)`. -/
noncomputable abbrev genericMatrix : Matrix (Fin n) (Fin n) (CoordinateRing R n) :=
  Matrix.mvPolynomialX (Fin n) (Fin n) R

/-- The comultiplication dual to multiplication of square matrices. -/
noncomputable def comul :
    CoordinateRing R n →ₐ[R] CoordinateRing R n ⊗[R] CoordinateRing R n :=
  MvPolynomial.aeval fun ij : Fin n × Fin n =>
    ∑ k : Fin n, MvPolynomial.X (ij.1, k) ⊗ₜ[R] MvPolynomial.X (k, ij.2)

/-- The counit dual to the identity matrix. -/
noncomputable def counit : CoordinateRing R n →ₐ[R] R :=
  MvPolynomial.aeval fun ij : Fin n × Fin n =>
    (1 : Matrix (Fin n) (Fin n) R) ij.1 ij.2

/-- The matrix-coordinate comultiplication sends a generic entry to the corresponding entry of
the product of the generic matrices in the two tensor factors. -/
@[simp]
theorem comul_X (i j : Fin n) :
    comul R n (MvPolynomial.X (i, j)) =
      ∑ k : Fin n, MvPolynomial.X (i, k) ⊗ₜ[R] MvPolynomial.X (k, j) := by
  simp [comul]

/-- The matrix-coordinate counit sends a generic entry to the corresponding identity-matrix
entry. -/
@[simp]
theorem counit_X (i j : Fin n) :
    counit R n (MvPolynomial.X (i, j)) = if i = j then 1 else 0 := by
  simp [counit, Matrix.one_apply]

/-- Applying the counit entrywise to the generic matrix gives the identity matrix. -/
@[simp]
theorem map_counit_genericMatrix :
    (genericMatrix R n).map (counit R n) = 1 := by
  simpa only [genericMatrix, counit, AlgHom.mapMatrix_apply] using
    Matrix.mvPolynomialX_mapMatrix_aeval R (1 : Matrix (Fin n) (Fin n) R)

/-- Applying the comultiplication entrywise to the generic matrix gives the product of its
left-tensor and right-tensor copies. The order represents ordinary matrix multiplication, not
the opposite monoid. -/
theorem map_comul_genericMatrix :
    (genericMatrix R n).map (comul R n) =
      (genericMatrix R n).map
          (includeLeft : CoordinateRing R n →ₐ[R]
            CoordinateRing R n ⊗[R] CoordinateRing R n) *
        (genericMatrix R n).map
          (includeRight : CoordinateRing R n →ₐ[R]
            CoordinateRing R n ⊗[R] CoordinateRing R n) := by
  ext i j
  simp [Matrix.mul_apply, genericMatrix]

/-- The matrix-coordinate bialgebra structure on the polynomial algebra `R[Xᵢⱼ]`.

This is intentionally a named value, not an instance. Callers that need typeclass-selected
coalgebra operations should use `coordinateBialgebra`, or install this value in a deliberately
local scope. -/
@[instance_reducible]
noncomputable def bialgebra : Bialgebra R (CoordinateRing R n) :=
  Bialgebra.ofAlgHom (comul R n) (counit R n)
    (by
      apply MvPolynomial.algHom_ext
      rintro ⟨i, j⟩
      simp only [AlgHom.comp_apply, comul_X, map_sum, map_tmul, AlgHom.id_apply]
      simp only [TensorProduct.sum_tmul, TensorProduct.tmul_sum]
      simp only [map_sum]
      rw [Finset.sum_comm]
      rfl)
    (by
      apply MvPolynomial.algHom_ext
      rintro ⟨i, j⟩
      simp only [AlgHom.comp_apply, comul_X, map_sum, map_tmul, counit_X, AlgHom.id_apply]
      rw [Finset.sum_eq_single i]
      · simp
      · intro k _ hki
        simp [hki.symm]
      · simp)
    (by
      apply MvPolynomial.algHom_ext
      rintro ⟨i, j⟩
      simp only [AlgHom.comp_apply, comul_X, map_sum, map_tmul, counit_X, AlgHom.id_apply]
      rw [Finset.sum_eq_single j]
      · simp
      · intro k _ hkj
        simp [hkj]
      · simp)

-- These private defining equations are elaborated with compatibility transparency so that Lean
-- recognizes the module structure stored in the opaque bialgebra as the canonical one. Their
-- public wrappers below are the abstraction boundary used by downstream code.
set_option backward.isDefEq.respectTransparency false in
private theorem bialgebra_comul_def :
    (bialgebra R n).toCoalgebra.toCoalgebraStruct.comul = (comul R n).toLinearMap :=
  rfl

/-- Selecting `bialgebra R n` makes its comultiplication the explicit matrix-multiplication map
`comul R n`. The equality is heterogeneous because opacity also hides the dictionary's stored
module structure. -/
theorem bialgebra_comul :
    HEq (letI : Module R (CoordinateRing R n) := (bialgebra R n).toAlgebra.toModule
      letI : Coalgebra R (CoordinateRing R n) := (bialgebra R n).toCoalgebra
      Coalgebra.comul (R := R) (A := CoordinateRing R n)) (comul R n).toLinearMap :=
  heq_of_eq (bialgebra_comul_def R n)

set_option backward.isDefEq.respectTransparency false in
private theorem bialgebra_counit_def :
    (bialgebra R n).toCoalgebra.toCoalgebraStruct.counit = (counit R n).toLinearMap :=
  rfl

/-- Selecting `bialgebra R n` makes its counit the explicit identity-matrix map `counit R n`.
As for `bialgebra_comul`, opacity makes the map equality heterogeneous. -/
theorem bialgebra_counit :
    HEq (letI : Module R (CoordinateRing R n) := (bialgebra R n).toAlgebra.toModule
      letI : Coalgebra R (CoordinateRing R n) := (bialgebra R n).toCoalgebra
      Coalgebra.counit (R := R) (A := CoordinateRing R n)) (counit R n).toLinearMap :=
  heq_of_eq (bialgebra_counit_def R n)

set_option backward.isDefEq.respectTransparency false in
private theorem bialgebra_comul_X_def (i j : Fin n) :
    letI : Module R (CoordinateRing R n) := (bialgebra R n).toAlgebra.toModule
    (bialgebra R n).toCoalgebra.toCoalgebraStruct.comul (MvPolynomial.X (i, j)) =
      ∑ k : Fin n, MvPolynomial.X (i, k) ⊗ₜ[R] MvPolynomial.X (k, j) := by
  rw [eq_of_heq (bialgebra_comul R n), AlgHom.toLinearMap_apply]
  exact comul_X R n i j

/-- Under `bialgebra R n`, comultiplication has the matrix-multiplication formula on generators. -/
@[simp]
theorem bialgebra_comul_X (i j : Fin n) :
    letI : Module R (CoordinateRing R n) := (bialgebra R n).toAlgebra.toModule
    letI : Coalgebra R (CoordinateRing R n) := (bialgebra R n).toCoalgebra
    Coalgebra.comul (R := R) (A := CoordinateRing R n) (MvPolynomial.X (i, j)) =
      ∑ k : Fin n, MvPolynomial.X (i, k) ⊗ₜ[R] MvPolynomial.X (k, j) :=
  bialgebra_comul_X_def R n i j

set_option backward.isDefEq.respectTransparency false in
private theorem bialgebra_counit_X_def (i j : Fin n) :
    (bialgebra R n).toCoalgebra.toCoalgebraStruct.counit (MvPolynomial.X (i, j)) =
      if i = j then 1 else 0 := by
  rw [eq_of_heq (bialgebra_counit R n), AlgHom.toLinearMap_apply]
  exact counit_X R n i j

/-- Under `bialgebra R n`, the counit has the identity-matrix formula on generators. -/
@[simp]
theorem bialgebra_counit_X (i j : Fin n) :
    letI : Module R (CoordinateRing R n) := (bialgebra R n).toAlgebra.toModule
    letI : Coalgebra R (CoordinateRing R n) := (bialgebra R n).toCoalgebra
    Coalgebra.counit (R := R) (A := CoordinateRing R n) (MvPolynomial.X (i, j)) =
      if i = j then 1 else 0 :=
  bialgebra_counit_X_def R n i j

end Semiring

section Ring

variable (R : Type u) [CommRing R] (n : ℕ)

/-- The determinant of the generic `n × n` matrix. -/
noncomputable def determinant : CoordinateRing R n :=
  Matrix.det (genericMatrix R n)

private theorem determinant_def_internal :
    determinant R n = Matrix.det (genericMatrix R n) :=
  rfl

/-- The generic determinant is the determinant of `genericMatrix`. -/
theorem determinant_def : determinant R n = Matrix.det (genericMatrix R n) :=
  determinant_def_internal R n

/-- Evaluating the generic determinant at the identity-matrix counit gives one. -/
@[simp]
theorem counit_determinant : counit R n (determinant R n) = 1 := by
  rw [determinant_def, AlgHom.map_det, AlgHom.mapMatrix_apply, map_counit_genericMatrix,
    Matrix.det_one]

/-- Matrix-multiplication comultiplication sends the generic determinant to its tensor square. -/
@[simp]
theorem comul_determinant :
    comul R n (determinant R n) = determinant R n ⊗ₜ[R] determinant R n := by
  rw [determinant_def, AlgHom.map_det, AlgHom.mapMatrix_apply, map_comul_genericMatrix,
    Matrix.det_mul]
  rw [← AlgHom.mapMatrix_apply (includeLeft : CoordinateRing R n →ₐ[R]
        CoordinateRing R n ⊗[R] CoordinateRing R n) (genericMatrix R n),
      ← AlgHom.mapMatrix_apply (includeRight : CoordinateRing R n →ₐ[R]
        CoordinateRing R n ⊗[R] CoordinateRing R n) (genericMatrix R n)]
  rw [← AlgHom.map_det, ← AlgHom.map_det]
  simp

/-- The polynomial coordinate algebra of the matrix monoid, bundled with the selected
matrix-coordinate bialgebra structure.

The object stores `bialgebra R n`; it does not depend on whichever bialgebra instance may be
available globally for the raw `MvPolynomial` carrier. -/
@[expose]
noncomputable def coordinateBialgebra : CommBialgCat R :=
  letI : Bialgebra R (CoordinateRing R n) := bialgebra R n
  CommBialgCat.of R (CoordinateRing R n)

set_option backward.isDefEq.respectTransparency false in
private theorem coordinateBialgebra_comul_def (x : CoordinateRing R n) :
    Coalgebra.comul (R := R) (A := coordinateBialgebra R n)
        (x : coordinateBialgebra R n) = comul R n x :=
  rfl

/-- The bundled coordinate bialgebra uses the explicit matrix-multiplication comultiplication.
The equality is heterogeneous because the opaque dictionary also hides its module structure. -/
theorem coordinateBialgebra_comul (x : CoordinateRing R n) :
    HEq (Coalgebra.comul (R := R) (A := coordinateBialgebra R n)
        (x : coordinateBialgebra R n)) (comul R n x) :=
  heq_of_eq (coordinateBialgebra_comul_def R n x)

set_option backward.isDefEq.respectTransparency false in
private theorem coordinateBialgebra_counit_def (x : CoordinateRing R n) :
    Coalgebra.counit (R := R) (A := coordinateBialgebra R n)
        (x : coordinateBialgebra R n) = counit R n x :=
  rfl

/-- The bundled coordinate bialgebra uses the explicit identity-matrix counit. -/
theorem coordinateBialgebra_counit (x : CoordinateRing R n) :
    Coalgebra.counit (R := R) (A := coordinateBialgebra R n)
        (x : coordinateBialgebra R n) = counit R n x :=
  coordinateBialgebra_counit_def R n x

set_option backward.isDefEq.respectTransparency false in
private theorem coordinateBialgebra_comul_X_def (i j : Fin n) :
    Coalgebra.comul (R := R) (A := coordinateBialgebra R n)
        (MvPolynomial.X (i, j) : coordinateBialgebra R n) =
      ∑ k : Fin n,
        (MvPolynomial.X (i, k) : coordinateBialgebra R n) ⊗ₜ[R]
          (MvPolynomial.X (k, j) : coordinateBialgebra R n) := by
  rw [eq_of_heq (coordinateBialgebra_comul R n (MvPolynomial.X (i, j)))]
  exact comul_X R n i j

/-- The bundled coordinate bialgebra retains the matrix-multiplication comultiplication on its
generic entries. -/
@[simp]
theorem coordinateBialgebra_comul_X (i j : Fin n) :
    Coalgebra.comul (R := R) (A := coordinateBialgebra R n)
        (MvPolynomial.X (i, j) : coordinateBialgebra R n) =
      (∑ k : Fin n,
        (MvPolynomial.X (i, k) : coordinateBialgebra R n) ⊗ₜ[R]
          (MvPolynomial.X (k, j) : coordinateBialgebra R n) :
        coordinateBialgebra R n ⊗[R] coordinateBialgebra R n) :=
  coordinateBialgebra_comul_X_def R n i j

set_option backward.isDefEq.respectTransparency false in
private theorem coordinateBialgebra_counit_X_def (i j : Fin n) :
    Coalgebra.counit (R := R) (A := coordinateBialgebra R n)
        (MvPolynomial.X (i, j) : coordinateBialgebra R n) =
      if i = j then 1 else 0 := by
  rw [coordinateBialgebra_counit]
  exact counit_X R n i j

/-- The bundled coordinate bialgebra retains the identity-matrix counit on its generic
entries. -/
@[simp]
theorem coordinateBialgebra_counit_X (i j : Fin n) :
    Coalgebra.counit (R := R) (A := coordinateBialgebra R n)
        (MvPolynomial.X (i, j) : coordinateBialgebra R n) =
      if i = j then 1 else 0 :=
  coordinateBialgebra_counit_X_def R n i j

set_option backward.isDefEq.respectTransparency false in
private theorem isGroupLikeElem_determinant_def :
    IsGroupLikeElem (A := coordinateBialgebra R n) R
      (determinant R n : coordinateBialgebra R n) := by
  constructor
  · rw [coordinateBialgebra_counit]
    exact counit_determinant R n
  · rw [eq_of_heq (coordinateBialgebra_comul R n (determinant R n))]
    exact comul_determinant R n

/-- The determinant of the generic matrix is group-like in the matrix-coordinate bialgebra. -/
theorem isGroupLikeElem_determinant :
    IsGroupLikeElem (A := coordinateBialgebra R n) R
      (determinant R n : coordinateBialgebra R n) :=
  isGroupLikeElem_determinant_def R n

end Ring

end MatrixMonoid

end TauCeti
