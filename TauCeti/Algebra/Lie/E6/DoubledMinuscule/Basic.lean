/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.E6.Minuscule.Basic

import Mathlib.Data.Matrix.Block

/-!
# The doubled minuscule representation of type E6

The nontrivial diagram automorphism of type `E₆` exchanges the minuscule representations `V(ϖ₁)`
and `V(ϖ₆) = V(ϖ₁)ˣ`. Consequently the `27`-dimensional carrier alone does not admit the pinned
diagram symmetry. This file constructs the graph-stable direct sum `V(ϖ₁) ⊕ V(ϖ₆)` over `ℤ`.

The first block is `TauCeti.E6Minuscule.serreRepresentation`. The second is its contragredient:
the Cartan matrices are negated and the raising and lowering matrices are exchanged and negated.
The resulting `54`-dimensional block matrices satisfy the type-`E₆` Serre relations and have the
weights `TauCeti.DynkinType.e6DoubledMinusculeWeight`.

This is the representation input for the graph-stable full-weight type-`E₆`
Chevalley--Demazure carrier required by Layer 9 of the ReductiveGroups roadmap.

## Main declarations

* `TauCeti.E6DoubledMinuscule.serreRepresentation`: the integral doubled minuscule
  representation.
* `TauCeti.E6DoubledMinuscule.cartanGeneratorMatrix`, `raisingMatrix`, and `loweringMatrix`: its
  block-diagonal Chevalley generators.
* `TauCeti.E6DoubledMinuscule.isSerreSystem`: these generators satisfy the type-`E₆` Serre
  relations.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate V.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§13.4 and 27.
* R. W. Carter, *Simple Groups of Lie Type*, §12.2.
-/

public section

open scoped Matrix

namespace TauCeti.E6DoubledMinuscule

open TauCeti.DynkinType

attribute [local instance 100] LieRing.ofAssociativeRing LieRing.instLieAlgebra

/-- The contragredient of the integral minuscule representation. -/
private noncomputable def dualSerreRepresentation :
    Matrix.ToLieAlgebra ℤ (CartanMatrix.E 6)ᵀ →ₗ⁅ℤ⁆ Matrix (Fin 27) (Fin 27) ℤ :=
  TauCeti.serreLift TauCeti.E6Minuscule.isSerreSystem.neg_swap

@[simp]
private theorem dualSerreRepresentation_serreH (i : Fin 6) :
    dualSerreRepresentation (TauCeti.serreH ℤ (CartanMatrix.E 6)ᵀ i) =
      -TauCeti.E6Minuscule.cartanGeneratorMatrix i :=
  TauCeti.serreLift_serreH TauCeti.E6Minuscule.isSerreSystem.neg_swap i

@[simp]
private theorem dualSerreRepresentation_serreE (i : Fin 6) :
    dualSerreRepresentation (TauCeti.serreE ℤ (CartanMatrix.E 6)ᵀ i) =
      -TauCeti.E6Minuscule.loweringMatrix i :=
  TauCeti.serreLift_serreE TauCeti.E6Minuscule.isSerreSystem.neg_swap i

@[simp]
private theorem dualSerreRepresentation_serreF (i : Fin 6) :
    dualSerreRepresentation (TauCeti.serreF ℤ (CartanMatrix.E 6)ᵀ i) =
      -TauCeti.E6Minuscule.raisingMatrix i :=
  TauCeti.serreLift_serreF TauCeti.E6Minuscule.isSerreSystem.neg_swap i

/-- The integral Cartan generators on `V(ϖ₁) ⊕ V(ϖ₆)`. -/
def cartanGeneratorMatrix (i : Fin 6) :
    Matrix (Fin 27 ⊕ Fin 27) (Fin 27 ⊕ Fin 27) ℤ :=
  Matrix.fromBlocks (TauCeti.E6Minuscule.cartanGeneratorMatrix i) 0 0
    (-TauCeti.E6Minuscule.cartanGeneratorMatrix i)

/-- The integral raising matrices on `V(ϖ₁) ⊕ V(ϖ₆)`. -/
def raisingMatrix (i : Fin 6) : Matrix (Fin 27 ⊕ Fin 27) (Fin 27 ⊕ Fin 27) ℤ :=
  Matrix.fromBlocks (TauCeti.E6Minuscule.raisingMatrix i) 0 0
    (-TauCeti.E6Minuscule.loweringMatrix i)

/-- The integral lowering matrices on `V(ϖ₁) ⊕ V(ϖ₆)`. -/
def loweringMatrix (i : Fin 6) : Matrix (Fin 27 ⊕ Fin 27) (Fin 27 ⊕ Fin 27) ℤ :=
  Matrix.fromBlocks (TauCeti.E6Minuscule.loweringMatrix i) 0 0
    (-TauCeti.E6Minuscule.raisingMatrix i)

/-- The integral `54`-dimensional representation `V(ϖ₁) ⊕ V(ϖ₆)` of the type-`E₆` Serre
presentation. -/
noncomputable def serreRepresentation :
    Matrix.ToLieAlgebra ℤ (CartanMatrix.E 6)ᵀ →ₗ⁅ℤ⁆
      Matrix (Fin 27 ⊕ Fin 27) (Fin 27 ⊕ Fin 27) ℤ where
  toFun x := Matrix.fromBlocks (TauCeti.E6Minuscule.serreRepresentation x) 0 0
    (dualSerreRepresentation x)
  map_add' x y := by
    simpa only [map_add, add_zero] using
      (Matrix.fromBlocks_add (TauCeti.E6Minuscule.serreRepresentation x) 0 0
        (dualSerreRepresentation x) (TauCeti.E6Minuscule.serreRepresentation y) 0 0
        (dualSerreRepresentation y)).symm
  map_smul' c x := by
    rw [map_smul, map_smul]
    simpa only [RingHom.id_apply, smul_zero] using
      (Matrix.fromBlocks_smul c (TauCeti.E6Minuscule.serreRepresentation x) 0 0
        (dualSerreRepresentation x)).symm
  map_lie' := by
    simp [Ring.lie_def, Matrix.fromBlocks_multiply, sub_eq_add_neg,
      Matrix.fromBlocks_neg, Matrix.fromBlocks_add]

/-- The doubled representation is the block-diagonal sum of the minuscule representation and its
contragredient. -/
private theorem serreRepresentation_apply (x : Matrix.ToLieAlgebra ℤ (CartanMatrix.E 6)ᵀ) :
    serreRepresentation x =
      Matrix.fromBlocks (TauCeti.E6Minuscule.serreRepresentation x) 0 0
        (dualSerreRepresentation x) :=
  (rfl)

/-- The doubled representation sends a Cartan generator to its block-diagonal Cartan matrix. -/
@[simp]
theorem serreRepresentation_serreH (i : Fin 6) :
    serreRepresentation (TauCeti.serreH ℤ (CartanMatrix.E 6)ᵀ i) = cartanGeneratorMatrix i := by
  rw [serreRepresentation_apply]
  simp [dualSerreRepresentation, cartanGeneratorMatrix]

/-- The doubled representation sends a positive generator to its raising matrix. -/
@[simp]
theorem serreRepresentation_serreE (i : Fin 6) :
    serreRepresentation (TauCeti.serreE ℤ (CartanMatrix.E 6)ᵀ i) = raisingMatrix i := by
  rw [serreRepresentation_apply]
  simp [dualSerreRepresentation, raisingMatrix]

/-- The doubled representation sends a negative generator to its lowering matrix. -/
@[simp]
theorem serreRepresentation_serreF (i : Fin 6) :
    serreRepresentation (TauCeti.serreF ℤ (CartanMatrix.E 6)ᵀ i) = loweringMatrix i := by
  rw [serreRepresentation_apply]
  simp [dualSerreRepresentation, loweringMatrix]

/-- **The integral doubled minuscule matrices satisfy the type-`E₆` Serre relations.** -/
theorem isSerreSystem :
    TauCeti.IsSerreSystem ℤ (CartanMatrix.E 6)ᵀ cartanGeneratorMatrix raisingMatrix
      loweringMatrix := by
  have h := (TauCeti.isSerreSystem_serre (R := ℤ) (CM := (CartanMatrix.E 6)ᵀ)).map
    serreRepresentation
  have hH : serreRepresentation ∘ TauCeti.serreH ℤ (CartanMatrix.E 6)ᵀ =
      cartanGeneratorMatrix := by
    funext i
    exact serreRepresentation_serreH i
  have hE : serreRepresentation ∘ TauCeti.serreE ℤ (CartanMatrix.E 6)ᵀ = raisingMatrix := by
    funext i
    exact serreRepresentation_serreE i
  have hF : serreRepresentation ∘ TauCeti.serreF ℤ (CartanMatrix.E 6)ᵀ = loweringMatrix := by
    funext i
    exact serreRepresentation_serreF i
  rwa [hH, hE, hF] at h

/-- The simple reflection on the doubled weight basis, preserving each minuscule summand. -/
def reflection (i : Fin 6) : Equiv.Perm (Fin 27 ⊕ Fin 27) :=
  Equiv.sumCongr (e6MinusculeReflection i) (e6MinusculeReflection i)

/-- A simple reflection negates the corresponding simple-coroot coordinate of every doubled
minuscule weight. -/
@[simp]
theorem e6DoubledMinusculeWeight_reflection_apply_self (i : Fin 6)
    (a : Fin 27 ⊕ Fin 27) :
    e6DoubledMinusculeWeight (reflection i a) i = -e6DoubledMinusculeWeight a i := by
  cases a <;>
    simp [reflection, TauCeti.E6Minuscule.e6MinusculeWeight_reflection_apply_self]

/-- Every simple reflection on the doubled minuscule basis is an involution. -/
@[simp]
theorem reflection_apply_apply (i : Fin 6) (a : Fin 27 ⊕ Fin 27) :
    reflection i (reflection i a) = a := by
  cases a <;> simp [reflection]

/-- The sign of the Chevalley root-matrix coefficient on each minuscule summand. The dual block
has the negative structure constants. -/
def summandSign : Fin 27 ⊕ Fin 27 → ℤ
  | .inl _ => 1
  | .inr _ => -1

/-- The Cartan generators are diagonal with the doubled minuscule weights on the diagonal. -/
@[simp]
theorem cartanGeneratorMatrix_apply (i : Fin 6) (a b : Fin 27 ⊕ Fin 27) :
    cartanGeneratorMatrix i a b =
      if a = b then e6DoubledMinusculeWeight b i else 0 := by
  cases a <;> cases b <;>
    simp [cartanGeneratorMatrix, Matrix.fromBlocks,
      TauCeti.E6Minuscule.cartanGeneratorMatrix_apply]
  all_goals split_ifs <;> simp_all

/-- Entry formula for a simple raising matrix on the doubled minuscule basis. -/
@[simp]
theorem raisingMatrix_apply (i : Fin 6) (a b : Fin 27 ⊕ Fin 27) :
    raisingMatrix i a b =
      if e6DoubledMinusculeWeight b i = -1 ∧ a = reflection i b then summandSign b else 0 := by
  cases a <;> cases b <;>
    simp [raisingMatrix, reflection, summandSign, Matrix.fromBlocks,
      TauCeti.E6Minuscule.raisingMatrix_apply, TauCeti.E6Minuscule.loweringMatrix_apply]
  all_goals split_ifs <;> simp_all

/-- Entry formula for a simple lowering matrix on the doubled minuscule basis. -/
@[simp]
theorem loweringMatrix_apply (i : Fin 6) (a b : Fin 27 ⊕ Fin 27) :
    loweringMatrix i a b =
      if e6DoubledMinusculeWeight b i = 1 ∧ a = reflection i b then summandSign b else 0 := by
  cases a <;> cases b <;>
    simp [loweringMatrix, reflection, summandSign, Matrix.fromBlocks,
      TauCeti.E6Minuscule.raisingMatrix_apply, TauCeti.E6Minuscule.loweringMatrix_apply]
  all_goals split_ifs <;> omega

end TauCeti.E6DoubledMinuscule
