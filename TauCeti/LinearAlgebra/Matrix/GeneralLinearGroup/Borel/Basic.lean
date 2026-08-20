/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `TauCeti.diagGL` supplies the diagonal section below.
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal
-- The upper-unitriangular subgroup is the kernel of the diagonal projection.
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UpperUnitriangular.Basic

/-!
# Upper-triangular general linear groups

For a commutative ring `R`, the upper-triangular general linear group consists of the invertible
upper-triangular matrices over `R`. Reading off the diagonal defines a group homomorphism

```text
B_m(R) → (m → Rˣ).
```

Its kernel is exactly the upper-unitriangular subgroup. The specialization to `m = Fin 2` is
`TauCeti.GL2Borel`; its pair-valued diagonal coordinates and its representation-theoretic API are
defined in `TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Borel`.

## Main declarations

* `TauCeti.upperTriangularGroup`: the subgroup of upper-triangular elements of `GL m R`.
* `TauCeti.UpperTriangularGroup.diag`: the diagonal homomorphism to `m → Rˣ`.
* `TauCeti.UpperTriangularGroup.diagonalHom`: its section by diagonal matrices.
* `TauCeti.UpperTriangularGroup.ker_diag`: identification of the diagonal kernel.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, I.2.
* T. A. Springer, *Linear Algebraic Groups*, §2.4.
-/

public section

namespace TauCeti

open Matrix

universe u

variable (m : Type*) [Fintype m] [LinearOrder m] (R : Type u) [CommRing R]

/-- The upper-triangular subgroup of `GL_m(R)` for a finite linearly ordered index type `m`. -/
def upperTriangularGroup : Subgroup (GL m R) where
  carrier := {g | (g : Matrix m m R).IsUpperTriangular}
  one_mem' := Matrix.blockTriangular_one
  mul_mem' := by
    intro g h hg hh
    simpa only [Set.mem_ofPred_eq, Units.val_mul] using hg.mul hh
  inv_mem' := by
    intro g hg
    simpa only [Set.mem_ofPred_eq, Matrix.coe_units_inv] using
      Matrix.blockTriangular_inv_of_blockTriangular hg

namespace UpperTriangularGroup

variable {m R}

/-- Membership in the upper-triangular group means that the underlying matrix is upper
triangular. -/
@[simp]
theorem mem_iff {g : GL m R} :
    g ∈ upperTriangularGroup m R ↔ (g : Matrix m m R).IsUpperTriangular :=
  Iff.rfl

/-- The matrix underlying an element of the upper-triangular group is upper triangular. -/
theorem isUpperTriangular (g : upperTriangularGroup m R) :
    ((g : GL m R) : Matrix m m R).IsUpperTriangular :=
  g.2

/-- The diagonal projection from the upper-triangular group to the coordinatewise unit group.

Reading off the diagonal is multiplicative on upper-triangular matrices, so it is a homomorphism
to `m → R`; `MonoidHom.toHomUnits` lifts it to the units of that product ring because the source
is a group, and `MulEquiv.piUnits` distributes those units over the product. -/
def diag : upperTriangularGroup m R →* (m → Rˣ) :=
  MulEquiv.piUnits.toMonoidHom.comp <| MonoidHom.toHomUnits
    { toFun := fun g i ↦ ((g : GL m R) : Matrix m m R) i i
      map_one' := by
        funext i
        simp
      map_mul' := fun g h ↦ funext fun i ↦
        Matrix.mul_apply_diag_of_isUpperTriangular (isUpperTriangular g) (isUpperTriangular h) i }

/-- The value in `R` of the `i`-th coordinate of `diag g` is the `i`-th diagonal entry of `g`. -/
@[simp]
theorem diag_apply_val (g : upperTriangularGroup m R) (i : m) :
    ((diag g i : Rˣ) : R) = ((g : GL m R) : Matrix m m R) i i := by
  simp [diag]

/-- The diagonal matrices give a homomorphic section of the diagonal projection. -/
def diagonalHom : (m → Rˣ) →* upperTriangularGroup m R :=
  (diagGL (k := R) (ι := m)).codRestrict (upperTriangularGroup m R) fun t ↦
    mem_iff.mpr fun i j hji ↦ by
      rw [diagGL_coe]
      exact Matrix.diagonal_apply_ne _ (ne_of_gt hji)

/-- The matrix underlying `diagonalHom t` is the corresponding diagonal matrix. -/
@[simp]
theorem coe_diagonalHom (t : m → Rˣ) :
    (((diagonalHom t : upperTriangularGroup m R) : GL m R) : Matrix m m R) =
      Matrix.diagonal fun i ↦ (t i : R) := by
  exact diagGL_coe t

/-- The entries of `diagonalHom t` vanish off the diagonal and equal `t i` on it. -/
@[simp]
theorem diagonalHom_apply (t : m → Rˣ) (i j : m) :
    (((diagonalHom t : upperTriangularGroup m R) : GL m R) : Matrix m m R) i j =
      if i = j then (t i : R) else 0 := by
  rw [coe_diagonalHom]
  exact Matrix.diagonal_apply ..

/-- Diagonal matrices form a section of the diagonal projection. -/
@[simp]
theorem diag_diagonalHom (t : m → Rˣ) : diag (diagonalHom t) = t := by
  funext i
  apply Units.ext
  simp

/-- The diagonal projection is surjective. -/
theorem diag_surjective : Function.Surjective (diag (m := m) (R := R)) :=
  fun t ↦ ⟨diagonalHom t, diag_diagonalHom t⟩

/-- The upper-unitriangular group is a subgroup of the upper-triangular group. -/
theorem upperUnitriangularGroup_le_upperTriangularGroup :
    upperUnitriangularGroup m R ≤ upperTriangularGroup m R :=
  fun _ hg ↦ mem_iff.mpr (UpperUnitriangularGroup.mem_iff.mp hg).isUpperTriangular

/-- Membership in the kernel of the diagonal projection is upper-unitriangularity of the
underlying matrix. -/
@[simp]
theorem mem_ker_diag_iff {g : upperTriangularGroup m R} :
    g ∈ (diag (m := m) (R := R)).ker ↔ (g : GL m R) ∈ upperUnitriangularGroup m R := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro hg
    apply UpperUnitriangularGroup.mem_iff.mpr
    rw [Matrix.isUpperUnitriangular_def]
    refine ⟨isUpperTriangular g, fun i ↦ ?_⟩
    have hi := congrFun hg i
    simpa only [diag_apply_val, Pi.one_apply, Units.val_one] using congrArg Units.val hi
  · intro hg
    funext i
    apply Units.ext
    simpa only [diag_apply_val, Pi.one_apply, Units.val_one] using
      UpperUnitriangularGroup.apply_diag ⟨(g : GL m R), hg⟩ i

/-- The kernel of the diagonal projection is the upper-unitriangular subgroup, viewed inside the
upper-triangular group. -/
theorem ker_diag :
    (diag (m := m) (R := R)).ker =
      (upperUnitriangularGroup m R).subgroupOf (upperTriangularGroup m R) := by
  ext g
  rw [Subgroup.mem_subgroupOf, mem_ker_diag_iff]

end UpperTriangularGroup

end TauCeti
