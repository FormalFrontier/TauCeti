/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.LinearAlgebra.GeneralLinearGroup.Unipotent
public import TauCeti.LinearAlgebra.Matrix.Triangular
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Upper-unitriangular matrix groups

For a commutative ring `R`, the upper-unitriangular group `Uₙ(R)` consists of the invertible
upper-triangular matrices whose diagonal entries are all one. This file packages these matrices
as a subgroup of `GLₙ(R)`, proves functoriality in `R`, and verifies that their natural linear
action is unipotent.

The nilpotence calculation is valid over every ring: if `N` is a strictly upper-triangular
`n × n` matrix, then `N ^ n = 0`. Applying it to `g - 1` proves that every element of `Uₙ(R)`
is unipotent. This is the matrix-group input for the upper-unitriangular embedding
characterization in Layer 5, "Unipotent groups", of the ReductiveGroups roadmap.

## Main declarations

* `TauCeti.upperUnitriangularGroup`: the subgroup `Uₙ(R)` of `GLₙ(R)`.
* `TauCeti.UpperUnitriangularGroup.map`: base change along a ring homomorphism.
* `TauCeti.UpperUnitriangularGroup.isUnipotent_toLin`: the natural representation of every
  element of `Uₙ(R)` is unipotent.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, I.2.
* T. A. Springer, *Linear Algebraic Groups*, §2.4.
-/

public section

namespace Matrix

variable {R : Type*} {m : Type*} [Fintype m] [LinearOrder m] [CommRing R]

/-- Package an upper-unitriangular matrix as an element of the general linear group. -/
noncomputable def IsUpperUnitriangular.toGL {M : Matrix m m R} (hM : M.IsUpperUnitriangular) :
    GL m R :=
  Matrix.GeneralLinearGroup.mk'' M hM.isUnit_det

/-- The matrix underlying `IsUpperUnitriangular.toGL` is the original matrix. -/
@[simp]
theorem IsUpperUnitriangular.coe_toGL {M : Matrix m m R} (hM : M.IsUpperUnitriangular) :
    (hM.toGL : Matrix m m R) = M := by
  rfl

end Matrix

namespace TauCeti

open Matrix

universe u

variable (m : Type*) [Fintype m] [LinearOrder m] (R : Type u) [CommRing R]

/-- The upper-unitriangular subgroup of `GLₘ(R)` for a finite linearly ordered index type `m`. -/
def upperUnitriangularGroup : Subgroup (GL m R) where
  carrier := {g | (g : Matrix m m R).IsUpperUnitriangular}
  one_mem' := Matrix.isUpperUnitriangular_one
  mul_mem' := by
    intro g h hg hh
    simpa only [Set.mem_ofPred_eq, Matrix.GeneralLinearGroup.coe_mul] using hg.mul hh
  inv_mem' := by
    intro g hg
    let _ : Invertible (g : Matrix m m R) := g.invertible
    simpa only [Set.mem_ofPred_eq, Matrix.GeneralLinearGroup.coe_inv] using hg.inv

namespace UpperUnitriangularGroup

variable {m R}

/-- Membership in the upper-unitriangular group means that the underlying matrix is upper
unitriangular. -/
@[simp]
theorem mem_iff {g : GL m R} :
    g ∈ upperUnitriangularGroup m R ↔ (g : Matrix m m R).IsUpperUnitriangular :=
  Iff.rfl

/-- The underlying matrix of an element of `Uₙ(R)` is upper unitriangular. -/
theorem isUpperUnitriangular (g : upperUnitriangularGroup m R) :
    ((g : GL m R) : Matrix m m R).IsUpperUnitriangular :=
  g.2

/-- An upper-unitriangular matrix is upper triangular. -/
theorem isUpperTriangular (g : upperUnitriangularGroup m R) :
    ((g : GL m R) : Matrix m m R).IsUpperTriangular :=
  (isUpperUnitriangular g).isUpperTriangular

/-- Every diagonal entry of an upper-unitriangular matrix is one. -/
@[simp]
theorem apply_diag (g : upperUnitriangularGroup m R) (i : m) :
    ((g : GL m R) : Matrix m m R) i i = 1 :=
  (isUpperUnitriangular g).apply_diag i

/-- Packaging an upper-unitriangular matrix as an element of `GLₘ(R)` lands in the
upper-unitriangular subgroup. -/
theorem toGL_mem_upperUnitriangularGroup {M : Matrix m m R}
    (hM : M.IsUpperUnitriangular) : hM.toGL ∈ upperUnitriangularGroup m R := by
  simpa only [mem_iff, hM.coe_toGL] using hM

/-- Applying a ring homomorphism entrywise gives the base-change homomorphism between
upper-unitriangular groups. -/
def map {S : Type*} [CommRing S] (f : R →+* S) :
    upperUnitriangularGroup m R →* upperUnitriangularGroup m S where
  toFun g := ⟨Matrix.GeneralLinearGroup.map (n := m) f g, by
    rw [mem_iff, Matrix.isUpperUnitriangular_def]
    constructor
    · intro i j hji
      rw [Matrix.GeneralLinearGroup.map_apply, isUpperTriangular g hji, map_zero]
    · intro i
      rw [Matrix.GeneralLinearGroup.map_apply, apply_diag g i, map_one]⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' g h := Subtype.ext ((Matrix.GeneralLinearGroup.map (n := m) f).map_mul g h)

/-- The underlying `GLₘ` element of base change is Mathlib's base change map. -/
@[simp]
theorem coe_map {S : Type*} [CommRing S] (f : R →+* S)
    (g : upperUnitriangularGroup m R) :
    ((map f g : upperUnitriangularGroup m S) : GL m S) =
      Matrix.GeneralLinearGroup.map f g :=
  by simp [map]

/-- Base change acts entrywise on upper-unitriangular matrices. -/
theorem map_apply {S : Type*} [CommRing S] (f : R →+* S)
    (g : upperUnitriangularGroup m R) (i j : m) :
    (map f g : GL m S) i j = f ((g : GL m R) i j) := by
  rw [coe_map, Matrix.GeneralLinearGroup.map_apply]

/-- Base change along the identity ring homomorphism is the identity. -/
@[simp]
theorem map_id :
    map (m := m) (RingHom.id R) = MonoidHom.id (upperUnitriangularGroup m R) := by
  ext g i j
  simp only [map_apply, RingHom.id_apply, MonoidHom.id_apply]

/-- Successive base changes agree with base change along the composite ring homomorphism. -/
@[simp]
theorem map_comp {S T : Type*} [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T) :
    map (m := m) (g.comp f) = (map (m := m) g).comp (map (m := m) f) := by
  apply MonoidHom.ext
  intro x
  apply Subtype.ext
  ext i j
  simp only [map_apply, RingHom.coe_comp, Function.comp_apply,
    MonoidHom.coe_comp]

/-- The natural linear action of every upper-unitriangular matrix is unipotent. -/
theorem isUnipotent_toLin (g : upperUnitriangularGroup m R) :
    GeneralLinearGroup.IsUnipotent
      (Matrix.GeneralLinearGroup.toLin (g : GL m R)) :=
  (TauCeti.GeneralLinearGroup.isUnipotent_toLin_iff m R (g : GL m R)).2
    (isUpperUnitriangular g).isNilpotent_sub_one

end UpperUnitriangularGroup

end TauCeti
