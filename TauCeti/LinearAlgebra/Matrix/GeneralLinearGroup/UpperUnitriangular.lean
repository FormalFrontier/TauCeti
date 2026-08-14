/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.LinearAlgebra.GeneralLinearGroup.Unipotent
public import TauCeti.LinearAlgebra.Matrix.Triangular
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.RingTheory.Nilpotent.Lemmas

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

* `Matrix.IsUpperUnitriangular`: an upper-triangular matrix with diagonal one.
* `Matrix.isNilpotent_of_isUpperTriangular_of_diag_eq_zero`: strict upper triangularity implies
  nilpotence.
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

variable {R : Type*} {m : Type*} [CommRing R] [LinearOrder m]

/-- A square matrix is upper unitriangular when it is upper triangular and every diagonal entry
is one. -/
def IsUpperUnitriangular (M : Matrix m m R) : Prop :=
  M.IsUpperTriangular ∧ ∀ i, M i i = 1

/-- Characterization of upper-unitriangular matrices by triangularity and their diagonal. -/
theorem isUpperUnitriangular_iff (M : Matrix m m R) :
    M.IsUpperUnitriangular ↔ M.IsUpperTriangular ∧ ∀ i, M i i = 1 :=
  Iff.rfl

/-- The identity matrix is upper unitriangular. -/
@[simp]
theorem isUpperUnitriangular_one : IsUpperUnitriangular (1 : Matrix m m R) := by
  refine ⟨blockTriangular_one, ?_⟩
  simp

/-- A product of upper-unitriangular matrices is upper unitriangular. -/
theorem IsUpperUnitriangular.mul {M N : Matrix m m R}
    [Fintype m]
    (hM : M.IsUpperUnitriangular) (hN : N.IsUpperUnitriangular) :
    (M * N).IsUpperUnitriangular := by
  refine ⟨hM.1.mul hN.1, fun i ↦ ?_⟩
  rw [mul_apply_diag_of_isUpperTriangular hM.1 hN.1, hM.2 i, hN.2 i, one_mul]

/-- The inverse of an invertible upper-unitriangular matrix is upper unitriangular. -/
theorem IsUpperUnitriangular.inv {M : Matrix m m R} [Fintype m] [Invertible M]
    (hM : M.IsUpperUnitriangular) : M⁻¹.IsUpperUnitriangular := by
  refine ⟨blockTriangular_inv_of_blockTriangular hM.1, fun i ↦ ?_⟩
  exact inv_apply_diag_of_isUpperTriangular hM.1 (hM.2 i)

/-- Applying a ring homomorphism entrywise preserves upper-unitriangular matrices. -/
theorem IsUpperUnitriangular.map {S : Type*} [CommRing S] (f : R →+* S)
    {M : Matrix m m R} (hM : M.IsUpperUnitriangular) :
    (M.map f).IsUpperUnitriangular := by
  refine ⟨hM.1.map f, fun i ↦ ?_⟩
  simp [hM.2 i]

section Fin

variable {n : ℕ}

/-- A power of a strictly upper-triangular matrix vanishes at `(i, j)` when the exponent is
larger than the distance from `i` to `j`. -/
private theorem pow_apply_eq_zero_of_lt_add {M : Matrix (Fin n) (Fin n) R}
    (hM : ∀ i j, j ≤ i → M i j = 0) (k : ℕ) (i j : Fin n)
    (hji : j.1 < i.1 + k) : (M ^ k) i j = 0 := by
  induction k generalizing i j with
  | zero =>
      simp only [pow_zero]
      rw [one_apply_ne]
      intro hij
      subst j
      omega
  | succ k ih =>
      rw [pow_succ, mul_apply]
      apply Finset.sum_eq_zero
      intro l _
      by_cases hil : i.1 + k ≤ l.1
      · rw [hM l j (by omega), mul_zero]
      · rw [ih (i := i) (j := l) (by omega), zero_mul]

/-- A strictly upper-triangular `n × n` matrix has `n`-th power zero. -/
theorem pow_card_eq_zero_of_isUpperTriangular_of_diag_eq_zero
    {M : Matrix (Fin n) (Fin n) R} (htri : M.IsUpperTriangular)
    (hdiag : ∀ i, M i i = 0) : M ^ n = 0 := by
  apply Matrix.ext
  intro i j
  have hstrict : ∀ a b : Fin n, b ≤ a → M a b = 0 := by
    intro a b hba
    by_cases hab : a = b
    · subst b
      exact hdiag a
    · exact htri (lt_of_le_of_ne hba fun h ↦ hab h.symm)
  exact pow_apply_eq_zero_of_lt_add hstrict n i j (by omega)

/-- A strictly upper-triangular square matrix is nilpotent. -/
theorem isNilpotent_of_isUpperTriangular_of_diag_eq_zero
    {M : Matrix (Fin n) (Fin n) R} (htri : M.IsUpperTriangular)
    (hdiag : ∀ i, M i i = 0) : _root_.IsNilpotent M :=
  ⟨n, pow_card_eq_zero_of_isUpperTriangular_of_diag_eq_zero htri hdiag⟩

end Fin

end Matrix

namespace TauCeti

open Matrix

universe u

variable (n : ℕ) (R : Type u) [CommRing R]

/-- The upper-unitriangular subgroup `Uₙ(R)` of `GLₙ(R)`. -/
def upperUnitriangularGroup : Subgroup (GL (Fin n) R) where
  carrier := {g | (g : Matrix (Fin n) (Fin n) R).IsUpperUnitriangular}
  one_mem' := Matrix.isUpperUnitriangular_one
  mul_mem' := by
    intro g h hg hh
    simpa only [Set.mem_ofPred_eq, Matrix.GeneralLinearGroup.coe_mul] using hg.mul hh
  inv_mem' := by
    intro g hg
    let _ : Invertible (g : Matrix (Fin n) (Fin n) R) := g.invertible
    simpa only [Set.mem_ofPred_eq, Matrix.GeneralLinearGroup.coe_inv] using hg.inv

/-- The type of upper-unitriangular `n × n` matrices over `R`. -/
abbrev UpperUnitriangularGroup := upperUnitriangularGroup n R

namespace UpperUnitriangularGroup

variable {n R}

/-- Membership in `Uₙ(R)` means upper triangularity with every diagonal entry equal to one. -/
@[simp]
theorem mem_iff {g : GL (Fin n) R} :
    g ∈ upperUnitriangularGroup n R ↔
      (g : Matrix (Fin n) (Fin n) R).IsUpperTriangular ∧
        ∀ i, (g : Matrix (Fin n) (Fin n) R) i i = 1 :=
  Iff.rfl

/-- The underlying matrix of an element of `Uₙ(R)` is upper unitriangular. -/
theorem isUpperUnitriangular (g : UpperUnitriangularGroup n R) :
    ((g : GL (Fin n) R) : Matrix (Fin n) (Fin n) R).IsUpperUnitriangular :=
  (Matrix.isUpperUnitriangular_iff _).2 (mem_iff.1 g.2)

/-- An upper-unitriangular matrix is upper triangular. -/
theorem isUpperTriangular (g : UpperUnitriangularGroup n R) :
    ((g : GL (Fin n) R) : Matrix (Fin n) (Fin n) R).IsUpperTriangular :=
  (isUpperUnitriangular g).1

/-- Every diagonal entry of an upper-unitriangular matrix is one. -/
@[simp]
theorem apply_self (g : UpperUnitriangularGroup n R) (i : Fin n) :
    ((g : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i i = 1 :=
  (isUpperUnitriangular g).2 i

/-- Applying a ring homomorphism entrywise gives the base-change homomorphism between
upper-unitriangular groups. -/
@[expose] def map {S : Type*} [CommRing S] (f : R →+* S) :
    UpperUnitriangularGroup n R →* UpperUnitriangularGroup n S where
  toFun g := ⟨Matrix.GeneralLinearGroup.map (n := Fin n) f g,
    (mem_iff).2 ((Matrix.isUpperUnitriangular_iff _).1
      ((isUpperUnitriangular g).map f))⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' g h := Subtype.ext ((Matrix.GeneralLinearGroup.map (n := Fin n) f).map_mul g h)

/-- Base change acts entrywise on upper-unitriangular matrices. -/
@[simp]
theorem map_apply_coe {S : Type*} [CommRing S] (f : R →+* S)
    (g : UpperUnitriangularGroup n R) :
    (((map f g : UpperUnitriangularGroup n S) : GL (Fin n) S) :
      Matrix (Fin n) (Fin n) S) =
      (((g : GL (Fin n) R) : Matrix (Fin n) (Fin n) R).map f) :=
  rfl

/-- Base change along the identity ring homomorphism is the identity. -/
@[simp]
theorem map_id :
    map (RingHom.id R) = MonoidHom.id (UpperUnitriangularGroup n R) := by
  ext g i j
  rfl

/-- Successive base changes agree with base change along the composite ring homomorphism. -/
@[simp]
theorem map_comp {S T : Type*} [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T) :
    map (n := n) (g.comp f) = (map (n := n) g).comp (map (n := n) f) := by
  apply MonoidHom.ext
  intro x
  apply Subtype.ext
  ext i j
  rfl

/-- The natural linear action of every upper-unitriangular matrix is unipotent. -/
theorem isUnipotent_toLin (g : UpperUnitriangularGroup n R) :
    GeneralLinearGroup.IsUnipotent
      (Matrix.GeneralLinearGroup.toLin (g : GL (Fin n) R)) := by
  rw [GeneralLinearGroup.isUnipotent_def]
  have htri :
      (((g : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) - 1).IsUpperTriangular :=
    (isUpperTriangular g).sub blockTriangular_one
  have hdiag : ∀ i,
      (((g : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) - 1) i i = 0 := by
    intro i
    simp
  have hnil : _root_.IsNilpotent
      (((g : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) - 1) :=
    Matrix.isNilpotent_of_isUpperTriangular_of_diag_eq_zero htri hdiag
  rw [← Matrix.isNilpotent_toLin'_iff] at hnil
  rw [map_sub] at hnil
  rw [Matrix.toLin'_one] at hnil
  simpa only [Matrix.GeneralLinearGroup.coe_toLin, Matrix.toLin'_apply',
    Module.End.one_eq_id] using hnil

end UpperUnitriangularGroup

end TauCeti
