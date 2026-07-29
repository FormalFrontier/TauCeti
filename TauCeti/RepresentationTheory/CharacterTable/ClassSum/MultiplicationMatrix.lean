/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.ClassSum.StructureConstants
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# The class-multiplication matrices of a finite group

The centre of the group algebra `k[G]` of a finite group has the class sums `K_C` as a `k`-basis
(`TauCeti.classSumBasis`), and multiplication in that basis is described by the structure constants
`aᵢⱼₖ` (`TauCeti.structureConstant`). This file records the matrices of that multiplication.

The **class-multiplication matrix** `classMultMatrix Cᵢ` is the integer matrix with entries
`(Mᵢ)ⱼₖ = aᵢₖⱼ`. The index order is not an accident: it makes `Mᵢ` exactly the matrix of left
multiplication by `K_{Cᵢ}` on the centre, taken in the class-sum basis, which is Mathlib's
`Algebra.leftMulMatrix`. That identification (`TauCeti.classMultMatrix_map_intCast`) is the content
of the file, and everything else follows from it:

* `TauCeti.classMultMatrix_commute`: the matrices `Mᵢ` commute pairwise, because the centre is a
  commutative ring and `Algebra.leftMulMatrix` is an algebra homomorphism;
* `TauCeti.classMultMatrix_injective`: distinct classes give distinct matrices;
* `TauCeti.classMultMatrix_mk_one`: the matrix at the class of `1` is the identity matrix;
* `TauCeti.classMultMatrix_mulVec`: `Mᵢ` acts on the coordinate vector of a central element by
  multiplication by `K_{Cᵢ}`.

Since `TauCeti.structureConstant` is a genuine `def` on `[Fintype G] [DecidableEq G]` data, so is
`classMultMatrix`; these integers and matrices are the whole input to the Burnside--Dixon--Schneider
character-table algorithm, where the values of a central character on the class sums appear as a
common eigenvector of the family `{Mᵢ}`.

## References

This implements the object `classMultMatrix` and the milestone `classMultMatrix_commute` of Layer 5
of the
[character theory roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CharacterTheory/README.md)
and its
[suggested declarations](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CharacterTheory/Suggested.lean).
-/

public section

namespace TauCeti

open scoped Matrix

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

section Center

variable (k : Type*) [CommSemiring k]

/-- The class sum of the conjugacy class of `1`, as an element of the centre, is `1`. -/
@[simp]
theorem classSumCenter_mk_one : classSumCenter (k := k) (ConjClasses.mk (1 : G)) = 1 := by
  apply Subtype.ext
  simp

/-- **The structure constants are the matrix of multiplication by a class sum**, entrywise: the
matrix of left multiplication by `K_{Cᵢ}` on the centre of `k[G]`, in the class-sum basis, has
`(Cⱼ, Cₖ)` entry `aᵢₖⱼ`. -/
theorem leftMulMatrix_classSumCenter_apply (Cᵢ Cⱼ Cₖ : ConjClasses G) :
    Algebra.leftMulMatrix (classSumBasis (k := k)) (classSumCenter Cᵢ) Cⱼ Cₖ =
      (structureConstant Cᵢ Cₖ Cⱼ : k) := by
  obtain ⟨g, rfl⟩ := ConjClasses.exists_rep Cⱼ
  rw [Algebra.leftMulMatrix_eq_repr_mul, classSumBasis_apply, classSumBasis_repr_apply,
    centerToConjClasses_mk, MulMemClass.coe_mul, classSumCenter_coe, classSumCenter_coe]
  exact coeff_classSum_mul k Cᵢ Cₖ g

end Center

section MultMatrix

/-- **The class-multiplication matrix** of a conjugacy class `Cᵢ` of a finite group: the integer
matrix with `(Cⱼ, Cₖ)` entry the structure constant `aᵢₖⱼ`.

The transposed index order is fixed so that `classMultMatrix Cᵢ` is the matrix of left
multiplication by the class sum `K_{Cᵢ}` on the centre of the group algebra, taken in the class-sum
basis (`TauCeti.classMultMatrix_map_intCast`). -/
@[expose] def classMultMatrix (Cᵢ : ConjClasses G) : Matrix (ConjClasses G) (ConjClasses G) ℤ :=
  Matrix.of fun Cⱼ Cₖ => (structureConstant Cᵢ Cₖ Cⱼ : ℤ)

@[simp]
theorem classMultMatrix_apply (Cᵢ Cⱼ Cₖ : ConjClasses G) :
    classMultMatrix Cᵢ Cⱼ Cₖ = (structureConstant Cᵢ Cₖ Cⱼ : ℤ) :=
  rfl

/-- **The class-multiplication matrix is the matrix of multiplication by the class sum**: pushing
`classMultMatrix Cᵢ` into any commutative ring `k` gives the matrix of left multiplication by
`K_{Cᵢ}` on the centre of `k[G]`, taken in the class-sum basis. -/
theorem classMultMatrix_map_intCast (k : Type*) [CommRing k] (Cᵢ : ConjClasses G) :
    (classMultMatrix Cᵢ).map (Int.cast : ℤ → k) =
      Algebra.leftMulMatrix (classSumBasis (k := k)) (classSumCenter Cᵢ) := by
  ext Cⱼ Cₖ
  rw [Matrix.map_apply, classMultMatrix_apply, leftMulMatrix_classSumCenter_apply,
    Int.cast_natCast]

/-- The class-multiplication matrix over `ℤ` is itself a matrix of multiplication by a class sum,
namely in the centre of the integral group algebra `ℤ[G]`. -/
theorem classMultMatrix_eq_leftMulMatrix (Cᵢ : ConjClasses G) :
    classMultMatrix Cᵢ = Algebra.leftMulMatrix (classSumBasis (k := ℤ)) (classSumCenter Cᵢ) := by
  rw [← classMultMatrix_map_intCast ℤ Cᵢ]
  ext Cⱼ Cₖ
  simp

/-- **The class-multiplication matrices commute pairwise.** They are the images of the class sums
under an algebra homomorphism out of the centre of `ℤ[G]`, which is commutative. -/
theorem classMultMatrix_commute (Cᵢ Cⱼ : ConjClasses G) :
    Commute (classMultMatrix Cᵢ) (classMultMatrix (G := G) Cⱼ) := by
  rw [classMultMatrix_eq_leftMulMatrix, classMultMatrix_eq_leftMulMatrix]
  exact (Commute.all _ _).map _

/-- **Distinct conjugacy classes have distinct class-multiplication matrices**: multiplication by a
class sum determines it, and the class sums are a basis of the centre. -/
theorem classMultMatrix_injective :
    Function.Injective (classMultMatrix (G := G)) := by
  intro Cᵢ Cⱼ h
  rw [classMultMatrix_eq_leftMulMatrix, classMultMatrix_eq_leftMulMatrix] at h
  have hb : (classSumBasis (k := ℤ)) Cᵢ = (classSumBasis (k := ℤ)) Cⱼ := by
    rw [classSumBasis_apply, classSumBasis_apply]
    exact Algebra.leftMulMatrix_injective (classSumBasis (k := ℤ)) h
  exact (classSumBasis (k := ℤ)).injective hb

/-- The class-multiplication matrix at the conjugacy class of `1` is the identity matrix: the class
sum of `{1}` is the unit of the group algebra. -/
@[simp]
theorem classMultMatrix_mk_one : classMultMatrix (ConjClasses.mk (1 : G)) = 1 := by
  rw [classMultMatrix_eq_leftMulMatrix, classSumCenter_mk_one, map_one]

/-- **The class-multiplication matrix acts by multiplication by the class sum**: it sends the vector
of class-sum coordinates of a central element `z` to the coordinates of `K_{Cᵢ} * z`. -/
theorem classMultMatrix_mulVec (k : Type*) [CommRing k] (Cᵢ : ConjClasses G)
    (z : Subalgebra.center k (MonoidAlgebra k G)) :
    (classMultMatrix Cᵢ).map (Int.cast : ℤ → k) *ᵥ centerToConjClasses z =
      centerToConjClasses (classSumCenter Cᵢ * z) := by
  have hrepr : ∀ w : Subalgebra.center k (MonoidAlgebra k G),
      ((classSumBasis (k := k)).repr w : ConjClasses G → k) = centerToConjClasses w :=
    fun w => funext fun C => classSumBasis_repr_apply w C
  rw [classMultMatrix_map_intCast, ← hrepr z, ← hrepr (classSumCenter Cᵢ * z)]
  exact Algebra.leftMulMatrix_mulVec_repr _ _ _

end MultMatrix

end TauCeti
