/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.GraphAutomorphism
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Basic
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Transvection

/-!
# The standard general-linear subgroup of the symplectic group

For a commutative ring `R`, an invertible matrix `A` acts on a free module and contragrediently
on its dual.  On the direct sum this gives the symplectic matrix

```text
             [ A       0    ]
levi(A)  =   [              ].
             [ 0   (A⁻¹)ᵀ ]
```

This file packages that construction as the injective homomorphism
`TauCeti.GLSymplectic.leviHom : GL l R →* GLSymplectic l R`, transports it to the
`Fin (m + m)` coordinates used by the symplectic group scheme, and identifies the images of
elementary transvections with the difference-root subgroups.  It follows that over a field the
image of `SL_m` under the Levi embedding belongs to every subgroup containing all difference-root
elements.

The last statement is the diagonal-block input to symplectic Gaussian generation.  Together with
the upper- and lower-unipotent generation steps, it will identify the field-valued points of the
full-weight type-`C` Chevalley carrier with the standard symplectic group.  No claim about the
whole symplectic group is made here.

## Main definitions

* `TauCeti.GLSymplectic.leviHom`: the general-linear Levi embedding in sum coordinates.
* `TauCeti.GLSymplecticFin.leviHom`: the same embedding in `Fin (m + m)` coordinates.

## Main results

* `TauCeti.GLSymplectic.leviHom_injective` and
  `TauCeti.GLSymplecticFin.leviHom_injective`: both presentations are embeddings.
* `TauCeti.GLSymplecticFin.leviHom_transvection`: an elementary transvection maps to the
  corresponding difference-root element.
* `TauCeti.GLSymplecticFin.leviHom_toGL_mem_of_difference`: over a field, every element of the
  determinant-one Levi subgroup lies in any subgroup containing the difference-root elements.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §§4.4 and 5.2.
* T. A. Springer, *Linear Algebraic Groups*, 2nd ed., §8.1.

This advances the explicit type-`C` Chevalley--Demazure construction in Layer 9 of
`TauCetiRoadmap/ReductiveGroups/README.md`.  The type-`C` branch of milestone L0 of
`TauCetiRoadmap/CFSGStatement/README.md` consumes the resulting pinned carrier; the next carrier
step is the field-valued symplectic generation theorem, whose Levi factor is supplied here.
-/

public section

open Matrix

namespace TauCeti

universe u

namespace GLSymplectic

variable {l : Type*} [DecidableEq l] [Fintype l]
variable {R : Type u} [CommRing R]

/-- The block-diagonal matrix `diag(A, (A⁻¹)ᵀ)` is symplectic. -/
private theorem leviMatrix_mem (A : GL l R) :
    Matrix.fromBlocks (A : Matrix l l R) 0 0
        ((A⁻¹ : GL l R) : Matrix l l R)ᵀ ∈ Matrix.symplecticGroup l R := by
  apply fromBlocks_diagonal_mem
  rw [← Matrix.transpose_mul, ← Units.val_mul]
  simp

/-- The element of the symplectic group underlying the Levi homomorphism. -/
private noncomputable def leviElement (A : GL l R) : GLSymplectic l R :=
  ⟨ofSymplecticGroup l R
    ⟨Matrix.fromBlocks (A : Matrix l l R) 0 0
      ((A⁻¹ : GL l R) : Matrix l l R)ᵀ, leviMatrix_mem A⟩,
    ofSymplecticGroup_mem l R _⟩

@[simp]
private theorem coe_leviElement (A : GL l R) :
    (((leviElement A : GLSymplectic l R) : GL (l ⊕ l) R) :
        Matrix (l ⊕ l) (l ⊕ l) R) =
      Matrix.fromBlocks (A : Matrix l l R) 0 0
        ((A⁻¹ : GL l R) : Matrix l l R)ᵀ := by
  exact coe_ofSymplecticGroup l R _

/-- The general-linear group embedded as the standard Levi subgroup of the symplectic group:
`A ↦ diag(A, (A⁻¹)ᵀ)`. -/
noncomputable def leviHom : GL l R →* GLSymplectic l R where
  toFun := leviElement
  map_one' := by
    apply (mulEquivSymplecticGroup l R).injective
    apply Subtype.ext
    simpa only [coe_mulEquivSymplecticGroup, coe_leviElement, map_one,
      Submonoid.coe_one, Units.val_one, inv_one, Matrix.transpose_one] using
      (Matrix.fromBlocks_one (l := l) (m := l) (α := R))
  map_mul' A B := by
    apply (mulEquivSymplecticGroup l R).injective
    apply Subtype.ext
    simp only [coe_mulEquivSymplecticGroup, coe_leviElement, map_mul, Submonoid.coe_mul]
    rw [Matrix.fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Units.val_mul]
    rw [_root_.mul_inv_rev, Units.val_mul, Matrix.transpose_mul]

/-- The matrix underlying the Levi embedding is `diag(A, (A⁻¹)ᵀ)`. -/
@[simp]
theorem coe_leviHom (A : GL l R) :
    (((leviHom A : GLSymplectic l R) : GL (l ⊕ l) R) :
        Matrix (l ⊕ l) (l ⊕ l) R) =
      Matrix.fromBlocks (A : Matrix l l R) 0 0
        ((A⁻¹ : GL l R) : Matrix l l R)ᵀ := by
  rw [leviHom]
  exact coe_leviElement A

/-- The general-linear Levi homomorphism is injective. -/
theorem leviHom_injective : Function.Injective (leviHom : GL l R → GLSymplectic l R) := by
  intro A B hAB
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  have h := congrArg
    (fun M : GLSymplectic l R =>
      (((M : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R) (Sum.inl i) (Sum.inl j))) hAB
  simpa only [coe_leviHom, Matrix.fromBlocks_apply₁₁] using h

/-- The Levi embedding commutes with extension of the value ring. -/
@[simp]
theorem map_leviHom {S : Type*} [CommRing S] (f : R →+* S) (A : GL l R) :
    GLSymplectic.map l f (leviHom A) =
      leviHom (Matrix.GeneralLinearGroup.map f A) := by
  apply Subtype.ext
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rw [coe_map, Matrix.GeneralLinearGroup.map_apply, coe_leviHom, coe_leviHom]
  have hinv := congrArg
    (fun g : GL l S => (g : Matrix l l S))
    (Matrix.GeneralLinearGroup.map_inverseTranspose f A)
  rw [Matrix.GeneralLinearGroup.coe_inverseTranspose] at hinv
  have hinv_apply (a b : l) :
      f (((A⁻¹ : GL l R) : Matrix l l R)ᵀ a b) =
        (((Matrix.GeneralLinearGroup.map f A)⁻¹ : GL l S) : Matrix l l S)ᵀ a b := by
    have h := congrFun (congrFun hinv a) b
    simpa only [Matrix.GeneralLinearGroup.map_apply,
      Matrix.GeneralLinearGroup.coe_inverseTranspose] using h
  cases i with
  | inl i =>
      cases j with
      | inl j => simp only [Matrix.fromBlocks_apply₁₁, Matrix.GeneralLinearGroup.map_apply]
      | inr j => simp only [Matrix.fromBlocks_apply₁₂, Matrix.zero_apply, map_zero]
  | inr i =>
      cases j with
      | inl j => simp only [Matrix.fromBlocks_apply₂₁, Matrix.zero_apply, map_zero]
      | inr j =>
          simpa only [Matrix.fromBlocks_apply₂₂] using hinv_apply i j

end GLSymplectic

namespace GLSymplecticFin

variable {m : ℕ} {R : Type u} [CommRing R]

/-- The standard general-linear Levi embedding in the `Fin (m + m)` coordinates used by the
symplectic group scheme. -/
noncomputable def leviHom : GL (Fin m) R →* GLSymplecticFin m R :=
  (mulEquivGLSymplectic m R).symm.toMonoidHom.comp GLSymplectic.leviHom

/-- Transporting the `Fin`-indexed Levi embedding to sum coordinates recovers
`TauCeti.GLSymplectic.leviHom`. -/
@[simp]
theorem mulEquivGLSymplectic_leviHom (A : GL (Fin m) R) :
    mulEquivGLSymplectic m R (leviHom A) = GLSymplectic.leviHom A := by
  rw [leviHom]
  simp

/-- The matrix underlying the `Fin`-indexed Levi embedding is the block-diagonal Levi matrix,
transported from sum coordinates along `finSumFinEquiv`. -/
@[simp]
theorem coe_leviHom (A : GL (Fin m) R) :
    (((leviHom A : GLSymplecticFin m R) : GL (Fin (m + m)) R) :
        Matrix (Fin (m + m)) (Fin (m + m)) R) =
      (Matrix.fromBlocks (A : Matrix (Fin m) (Fin m) R) 0 0
        ((A⁻¹ : GL (Fin m) R) : Matrix (Fin m) (Fin m) R)ᵀ).submatrix
          finSumFinEquiv.symm finSumFinEquiv.symm := by
  ext i j
  have h := congrArg
    (fun M : GLSymplectic (Fin m) R =>
      (((M : GL (Fin m ⊕ Fin m) R) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) R)
        (finSumFinEquiv.symm i) (finSumFinEquiv.symm j)))
    (mulEquivGLSymplectic_leviHom A)
  simpa only [coe_mulEquivGLSymplectic, coe_reindexGL, Matrix.submatrix_apply,
    Equiv.apply_symm_apply, GLSymplectic.coe_leviHom] using h

/-- The `Fin`-indexed Levi embedding commutes with extension of the value ring. -/
@[simp]
theorem map_leviHom {S : Type*} [CommRing S] (f : R →+* S) (A : GL (Fin m) R) :
    GLSymplecticFin.map m R f (leviHom A) =
      leviHom (Matrix.GeneralLinearGroup.map f A) := by
  apply (mulEquivGLSymplectic m S).injective
  have hmap :
      mulEquivGLSymplectic m S (GLSymplecticFin.map m R f (leviHom A)) =
        GLSymplectic.map (Fin m) f (mulEquivGLSymplectic m R (leviHom A)) := by
    apply Subtype.ext
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    simp only [coe_mulEquivGLSymplectic, GLSymplecticFin.coe_map,
      GLSymplectic.coe_map, coe_reindexGL, Matrix.GeneralLinearGroup.map_apply,
      Matrix.submatrix_apply]
  rw [hmap, mulEquivGLSymplectic_leviHom, GLSymplectic.map_leviHom,
    mulEquivGLSymplectic_leviHom]

/-- The `Fin`-indexed Levi homomorphism is injective. -/
theorem leviHom_injective : Function.Injective (leviHom : GL (Fin m) R → GLSymplecticFin m R) :=
  (mulEquivGLSymplectic m R).symm.injective.comp GLSymplectic.leviHom_injective

/-- An elementary transvection maps under the symplectic Levi embedding to the corresponding
difference-root element. -/
@[simp]
theorem leviHom_transvection {i j : Fin m} (hij : i ≠ j) (c : R) :
    leviHom (Matrix.SpecialLinearGroup.transvection hij c).toGL =
      differenceShortRootUnit hij c := by
  apply (mulEquivGLSymplectic m R).injective
  rw [mulEquivGLSymplectic_leviHom]
  apply Subtype.ext
  have hfirst := reindexGL_transvectionUnit (R := R)
    (Sum.inl i) (Sum.inl j) (Sum.inl_injective.ne hij) c
  have hsecond := reindexGL_transvectionUnit (R := R)
    (Sum.inr j) (Sum.inr i) (Sum.inr_injective.ne hij.symm) (-c)
  rw [coe_mulEquivGLSymplectic, coe_differenceShortRootUnit, map_mul, hfirst, hsecond]
  apply Matrix.GeneralLinearGroup.ext
  intro a b
  rw [GLSymplectic.coe_leviHom]
  have hinv :
      Matrix.GeneralLinearGroup.inverseTranspose
          (transvectionUnit hij c) = transvectionUnit hij.symm (-c) :=
    inverseTranspose_transvectionUnit hij c
  have hcoeInv := congrArg
    (fun g : GL (Fin m) R => (g : Matrix (Fin m) (Fin m) R)) hinv
  rw [Matrix.GeneralLinearGroup.coe_inverseTranspose] at hcoeInv
  rw [toGL_transvection_eq_transvectionUnit hij c, hcoeInv]
  symm
  simpa only [coe_transvectionUnit] using
    congrFun (congrFun (coe_differenceShortRootTransvectionUnits hij c) a) b

/-- Over a field, every determinant-one element of the general-linear Levi subgroup belongs to
any subgroup containing all difference-root elements. -/
theorem leviHom_toGL_mem_of_difference {K : Type*} [Field K]
    (H : Subgroup (GLSymplecticFin m K))
    (hdifference : ∀ {i j : Fin m} (hij : i ≠ j) (c : K),
      differenceShortRootUnit hij c ∈ H)
    (A : Matrix.SpecialLinearGroup (Fin m) K) : leviHom A.toGL ∈ H := by
  let P : Subgroup (Matrix.SpecialLinearGroup (Fin m) K) :=
    H.comap (leviHom.comp Matrix.SpecialLinearGroup.toGL)
  have hclosure : Subgroup.closure
      (Set.range (Matrix.TransvectionStruct.toSpecialLinearGroup :
        Matrix.TransvectionStruct (Fin m) K → Matrix.SpecialLinearGroup (Fin m) K)) ≤ P := by
    apply (Subgroup.closure_le P).mpr
    rintro _ ⟨t, rfl⟩
    obtain ⟨i, j, hij, c⟩ := t
    dsimp only [P]
    apply (Subgroup.mem_comap).mpr
    rw [MonoidHom.comp_apply, Matrix.TransvectionStruct.toSpecialLinearGroup_mk,
      leviHom_transvection]
    exact hdifference hij c
  have htop := Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field
    (ι := Fin m) (K := K)
  have hA : A ∈ P := by
    apply hclosure
    rw [htop]
    exact Subgroup.mem_top A
  exact Subgroup.mem_comap.mp hA

end GLSymplecticFin

end TauCeti
