/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `Group.IsSolvable` occurs in the statement of
-- `TauCeti.UpperTriangularGroup.instIsSolvable`.
public import Mathlib.GroupTheory.Solvable
-- `MulEquiv.piUnits` packages a family of units as a unit in the product ring.
public import Mathlib.Algebra.Group.Pi.Units
-- The nilpotence of the upper-unitriangular subgroup supplies the solvable kernel below.
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UpperUnitriangular.Nilpotent

/-!
# Upper-triangular general linear groups

For a commutative ring `R`, the upper-triangular general linear group consists of the invertible
upper-triangular matrices over `R`. Reading off the diagonal defines a group homomorphism

```text
B_m(R) → (m → Rˣ).
```

Its kernel is exactly the upper-unitriangular group `U_m(R)`. Since `U_m(R)` is nilpotent and the
diagonal group is abelian, this proves that `B_m(R)` is solvable.

This continues the "Lie--Kolchin; solvable groups" milestone in Layer 5 of the ReductiveGroups
roadmap. That milestone's scheme-level property,
`TauCeti.geometricallySolvablePointsCommHopfAlgProperty`, asks for a solvable abstract group of
geometric points, and its one worked Borel example, for `GL₂`, is proved by transporting the
abstract-group solvability `TauCeti.GL2Borel.instIsSolvable` along the points equivalence
`TauCeti.GeneralLinear.Borel.pointsMulEquiv`. The theorem below is that same input for every `m`,
so the argument carries over to the upper-triangular Borel of `GLₘ`.

## Main declarations

* `TauCeti.upperTriangularGroup`: the subgroup of upper-triangular elements of `GL m R`.
* `TauCeti.UpperTriangularGroup.diag`: the diagonal homomorphism to `m → Rˣ`.
* `TauCeti.UpperTriangularGroup.diagonalHom`: its section by diagonal matrices.
* `TauCeti.UpperTriangularGroup.upperUnitriangularHom`: the inclusion `U_m(R) → B_m(R)`.
* `TauCeti.UpperTriangularGroup.range_upperUnitriangularHom_eq_ker_diag`: exactness at `B_m(R)`.
* `TauCeti.UpperTriangularGroup.instIsSolvable`: upper-triangular general linear groups are
  solvable.

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
    change ((g⁻¹ : GL m R) : Matrix m m R).IsUpperTriangular
    rw [Matrix.coe_units_inv]
    exact Matrix.blockTriangular_inv_of_blockTriangular hg

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

/-- The diagonal entry of an upper-triangular invertible matrix, packaged as a unit. -/
def diagonalUnit (g : upperTriangularGroup m R) (i : m) : Rˣ where
  val := ((g : GL m R) : Matrix m m R) i i
  inv := g.1.inv i i
  val_inv := by
    have h := congrFun (congrFun (Units.val_inv g.1) i) i
    have hginv := isUpperTriangular (g⁻¹)
    change g.1.inv.IsUpperTriangular at hginv
    rw [Matrix.mul_apply_diag_of_isUpperTriangular (isUpperTriangular g)
      hginv i, Matrix.one_apply_eq] at h
    exact h
  inv_val := by
    have h := congrFun (congrFun (Units.inv_val g.1) i) i
    have hginv := isUpperTriangular (g⁻¹)
    change g.1.inv.IsUpperTriangular at hginv
    rw [Matrix.mul_apply_diag_of_isUpperTriangular hginv
      (isUpperTriangular g) i, Matrix.one_apply_eq] at h
    exact h

/-- The diagonal projection from the upper-triangular group to the coordinatewise unit group. -/
def diag : upperTriangularGroup m R →* (m → Rˣ) where
  toFun g i := diagonalUnit g i
  map_one' := by
    funext i
    apply Units.ext
    simp [diagonalUnit]
  map_mul' g h := by
    funext i
    apply Units.ext
    exact Matrix.mul_apply_diag_of_isUpperTriangular
      (isUpperTriangular g) (isUpperTriangular h) i

/-- The value in `R` of the `i`-th coordinate of `diag g` is the `i`-th diagonal entry of `g`. -/
@[simp]
theorem diag_apply_val (g : upperTriangularGroup m R) (i : m) :
    ((diag g i : Rˣ) : R) = ((g : GL m R) : Matrix m m R) i i :=
  by simp [diag, diagonalUnit]

/-- The diagonal matrices give a homomorphic section of the diagonal projection. -/
def diagonalHom : (m → Rˣ) →* upperTriangularGroup m R :=
  ((Units.map (Matrix.diagonalRingHom m R).toMonoidHom).comp
    (MulEquiv.piUnits).symm.toMonoidHom).codRestrict (upperTriangularGroup m R) fun t ↦ by
      change (Matrix.diagonal fun i ↦ (t i : R)).IsUpperTriangular
      intro i j hji
      exact Matrix.diagonal_apply_ne _ (ne_of_gt hji)

/-- The matrix underlying `diagonalHom t` has `t` on the diagonal and zero elsewhere. -/
@[simp]
theorem diagonalHom_apply (t : m → Rˣ) (i j : m) :
    (((diagonalHom t : upperTriangularGroup m R) : GL m R) : Matrix m m R) i j =
      if i = j then (t i : R) else 0 := by
  simp [diagonalHom, Matrix.diagonal_apply]

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
  fun _ hg ↦ (UpperUnitriangularGroup.mem_iff.mp hg).isUpperTriangular

/-- The inclusion of the upper-unitriangular group in the upper-triangular group. -/
def upperUnitriangularHom :
    upperUnitriangularGroup m R →* upperTriangularGroup m R :=
  Subgroup.inclusion upperUnitriangularGroup_le_upperTriangularGroup

/-- The inclusion into the upper-triangular group does not change the underlying `GL_m`
element. -/
@[simp]
theorem coe_upperUnitriangularHom (g : upperUnitriangularGroup m R) :
    ((upperUnitriangularHom g : upperTriangularGroup m R) : GL m R) = g :=
  by simp [upperUnitriangularHom]

/-- The kernel of the diagonal homomorphism is exactly the image of the upper-unitriangular
subgroup. -/
theorem range_upperUnitriangularHom_eq_ker_diag :
    (upperUnitriangularHom (m := m) (R := R)).range = (diag (m := m) (R := R)).ker := by
  ext g
  constructor
  · rintro ⟨u, rfl⟩
    rw [MonoidHom.mem_ker]
    funext i
    apply Units.ext
    exact UpperUnitriangularGroup.apply_diag u i
  · intro hg
    have hdiag : ∀ i,
        ((g : GL m R) : Matrix m m R) i i = 1 := by
      intro i
      have hi := congrFun (MonoidHom.mem_ker.mp hg) i
      exact congrArg Units.val hi
    let u : upperUnitriangularGroup m R :=
      ⟨g.1, UpperUnitriangularGroup.mem_iff.mpr (by
        rw [Matrix.isUpperUnitriangular_def]
        exact ⟨isUpperTriangular g, hdiag⟩)⟩
    exact ⟨u, rfl⟩

/-- The upper-triangular subgroup of `GL_m(R)` is solvable over every commutative ring.

The diagonal quotient is abelian, while the kernel of the diagonal projection is the nilpotent
upper-unitriangular group. -/
instance instIsSolvable : Group.IsSolvable (upperTriangularGroup m R) := by
  apply Group.isSolvable_of_ker_le_range
    (upperUnitriangularHom (m := m) (R := R)) (diag (m := m) (R := R))
  rw [range_upperUnitriangularHom_eq_ker_diag]

end UpperTriangularGroup

end TauCeti
