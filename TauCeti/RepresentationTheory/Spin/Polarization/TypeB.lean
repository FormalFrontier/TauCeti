/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Quadratic.Realization
public import TauCeti.RepresentationTheory.Spin.Polarization.Basic
public import Mathlib.Algebra.Lie.Classical
public import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-!
# The type-B matrix model of an odd polarization

An odd polarization whose orthogonal remainder contains a vector of coordinate one identifies the
quadratic space with the standard split odd space. This file compares the resulting basis with
Mathlib's matrix model of the type-`B` Lie algebra and then with the quadratic elements of the
Clifford algebra.

The normalization is fixed by `LieAlgebra.Orthogonal.JB`: the distinguished remainder vector has
polar self-pairing `2`, while the two isotropic families pair by the identity matrix. Keeping the
coordinate-one hypothesis explicit makes the comparison usable over any field of characteristic
different from two without choosing a square root or hiding a basis choice.

## Main definitions

* `TauCeti.SpinPolarizationData.typeBBasis`: the odd hyperbolic basis, with the remainder first.
* `TauCeti.SpinPolarizationData.typeBQuadraticEquiv`: the standard type-`B` matrix algebra
  identified with the quadratic Clifford Lie algebra.

## Roadmap

This supplies the matrix-to-Clifford bridge needed by the full-weight type-`B` Chevalley carrier
in Layer 9 of `TauCetiRoadmap/ReductiveGroups/README.md`. The next carrier step is to evaluate the
comparison on the numbered root vectors and prove their divided powers preserve the integral
spinor lattice.

## References

* N. Bourbaki, *Groupes et algèbres de Lie*, Chapters 4--6, Planche II.
* C. Chevalley, *The Algebraic Theory of Spinors*, Chapter II.
-/

public section

open CliffordAlgebra QuadraticMap

namespace TauCeti

universe u v w

namespace SpinPolarizationData

attribute [local instance 100] LieRing.ofAssociativeRing

section PreQuadratic

variable {K : Type u} [CommRing K] {V : Type v} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} (P : SpinPolarizationData Q)
  {ι : Type w} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K P.W)
  (z : P.line) (hz : P.lineCoordinate z = 1)

/-- A coordinate-one remainder vector identifies the remainder with the scalar line. -/
private noncomputable def lineEquiv : P.line ≃ₗ[K] K :=
  LinearEquiv.ofBijective P.lineCoordinate
    ⟨P.lineCoordinate_injective, fun a => ⟨a • z, by simp [hz]⟩⟩

@[simp]
private theorem lineEquiv_apply (x : P.line) : P.lineEquiv z hz x = P.lineCoordinate x :=
  rfl

@[simp]
private theorem lineEquiv_symm_apply (a : K) : (P.lineEquiv z hz).symm a = a • z := by
  apply (P.lineEquiv z hz).injective
  simp [hz]

/-- Coordinates for an odd polarization, ordered with the one-dimensional remainder first. -/
private noncomputable def oddDecompositionEquiv :
    (K × (P.W × P.W')) ≃ₗ[K] V :=
  (((P.lineEquiv z hz).symm.prodCongr (LinearEquiv.refl K (P.W × P.W'))).trans
      (LinearEquiv.prodComm K P.line (P.W × P.W'))).trans P.decompositionEquiv

private theorem oddDecompositionEquiv_apply (x : K × (P.W × P.W')) :
    P.oddDecompositionEquiv z hz x =
      (x.2.1 : V) + x.2.2 + x.1 • (z : V) := by
  rcases x with ⟨a, x, y⟩
  simp [oddDecompositionEquiv]

/-- The standard odd hyperbolic basis of a polarization: the coordinate-one remainder vector,
then a basis of the first isotropic summand, then its polar-dual basis. -/
noncomputable def typeBBasis : Module.Basis (Unit ⊕ ι ⊕ ι) K V :=
  ((Module.Basis.singleton Unit K).prod (b.prod (P.dualBasis b))).map
    (P.oddDecompositionEquiv z hz)

@[simp]
theorem typeBBasis_inl (i : Unit) : P.typeBBasis b z hz (.inl i) = (z : V) := by
  simp [typeBBasis, P.oddDecompositionEquiv_apply]

@[simp]
theorem typeBBasis_inr_inl (i : ι) :
    P.typeBBasis b z hz (.inr (.inl i)) = (b i : V) := by
  simp [typeBBasis, P.oddDecompositionEquiv_apply]

@[simp]
theorem typeBBasis_inr_inr (i : ι) :
    P.typeBBasis b z hz (.inr (.inr i)) = (P.dualVector b i : V) := by
  simp [typeBBasis, P.oddDecompositionEquiv_apply]

/-- In the odd hyperbolic basis, the polar form has the standard split type-`B` Gram matrix. -/
theorem polarBilin_toMatrix_typeBBasis :
    LinearMap.BilinForm.toMatrix (P.typeBBasis b z hz) Q.polarBilin =
      LieAlgebra.Orthogonal.JB ι K := by
  ext (i | (i | i)) (j | (j | j))
  · simp [LinearMap.BilinForm.toMatrix_apply, LieAlgebra.Orthogonal.JB,
      QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, ← P.lineCoordinate_sq, hz]
  · simp [LinearMap.BilinForm.toMatrix_apply, LieAlgebra.Orthogonal.JB,
      P.line_orthogonal_W]
  · simp [LinearMap.BilinForm.toMatrix_apply, LieAlgebra.Orthogonal.JB,
      P.line_orthogonal_W']
  · rw [LinearMap.BilinForm.toMatrix_apply, typeBBasis_inr_inl, typeBBasis_inl,
      QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm]
    simp [LieAlgebra.Orthogonal.JB, P.line_orthogonal_W]
  · simp [LinearMap.BilinForm.toMatrix_apply, LieAlgebra.Orthogonal.JB,
      LieAlgebra.Orthogonal.JD, P.polar_W_eq_zero]
  · simp [LinearMap.BilinForm.toMatrix_apply, LieAlgebra.Orthogonal.JB,
      LieAlgebra.Orthogonal.JD, QuadraticMap.polarBilin_apply_apply, P.polar_dualVector,
      Matrix.one_apply]
  · rw [LinearMap.BilinForm.toMatrix_apply, typeBBasis_inr_inr, typeBBasis_inl,
      QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm]
    simp [LieAlgebra.Orthogonal.JB, P.line_orthogonal_W']
  · rw [LinearMap.BilinForm.toMatrix_apply, typeBBasis_inr_inr, typeBBasis_inr_inl,
      QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm, P.polar_dualVector]
    simp [LieAlgebra.Orthogonal.JB, LieAlgebra.Orthogonal.JD, Matrix.one_apply, eq_comm]
  · simp [LinearMap.BilinForm.toMatrix_apply, LieAlgebra.Orthogonal.JB,
      LieAlgebra.Orthogonal.JD, P.polar_W'_eq_zero]

private theorem mem_typeB_toMatrix_iff (f : Module.End K V) :
    LinearMap.toMatrix (P.typeBBasis b z hz) (P.typeBBasis b z hz) f ∈
        LieAlgebra.Orthogonal.typeB ι K ↔
      f ∈ skewAdjointLieSubalgebra Q.polarBilin := by
  have hB : Matrix.toLinearMap₂ (P.typeBBasis b z hz) (P.typeBBasis b z hz)
      (LieAlgebra.Orthogonal.JB ι K) = Q.polarBilin := by
    rw [← P.polarBilin_toMatrix_typeBBasis b z hz]
    exact Matrix.toLinearMap₂_toMatrix₂ _ _ Q.polarBilin
  rw [LieAlgebra.Orthogonal.typeB, mem_skewAdjointMatricesLieSubalgebra,
    mem_skewAdjointMatricesSubmodule]
  rw [show f ∈ skewAdjointLieSubalgebra Q.polarBilin ↔
      f ∈ Q.polarBilin.skewAdjointSubmodule by
    exact LieSubalgebra.mem_mk_iff' _ _, LinearMap.mem_skewAdjointSubmodule]
  rw [Matrix.IsSkewAdjoint, LinearMap.IsSkewAdjoint]
  symm
  simpa [hB] using
    (isAdjointPair_toLinearMap₂
      (b₁ := P.typeBBasis b z hz) (b₂ := P.typeBBasis b z hz)
      (J := LieAlgebra.Orthogonal.JB ι K) (J' := LieAlgebra.Orthogonal.JB ι K)
      (A := LinearMap.toMatrix (P.typeBBasis b z hz) (P.typeBBasis b z hz) f)
      (A' := -(LinearMap.toMatrix (P.typeBBasis b z hz) (P.typeBBasis b z hz) f)))

/-- The split type-`B` matrix model transported to skew-adjoint endomorphisms through the odd
hyperbolic basis. -/
private noncomputable def typeBSkewAdjointEquiv :
    LieAlgebra.Orthogonal.typeB ι K ≃ₗ⁅K⁆ skewAdjointLieSubalgebra Q.polarBilin :=
  LieEquiv.ofSubalgebras _ _
    (LinearMap.toMatrixAlgEquiv (P.typeBBasis b z hz)).symm.toLieEquiv <| by
      ext f
      simp only [Submodule.mem_map_equiv, LieSubalgebra.mem_map_submodule]
      -- `toMatrixAlgEquiv` has no application lemma identifying the inverse linear equivalence
      -- produced here with `LinearMap.toMatrix`, so expose that definitional equality explicitly.
      change LinearMap.toMatrix (P.typeBBasis b z hz) (P.typeBBasis b z hz) f ∈
          LieAlgebra.Orthogonal.typeB ι K ↔
        f ∈ skewAdjointLieSubalgebra Q.polarBilin
      exact P.mem_typeB_toMatrix_iff b z hz f

@[simp]
private theorem typeBSkewAdjointEquiv_apply (A : LieAlgebra.Orthogonal.typeB ι K) :
    (P.typeBSkewAdjointEquiv b z hz A : Module.End K V) =
      (LinearMap.toMatrixAlgEquiv (P.typeBBasis b z hz)).symm A := by
  rfl

end PreQuadratic

section Quadratic

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} (P : SpinPolarizationData Q)
  {ι : Type w} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K P.W)
  (z : P.line) (hz : P.lineCoordinate z = 1) [Invertible (2 : K)]

/-- An odd polarization with a coordinate-one remainder identifies the split type-`B` matrix
algebra with the quadratic elements of the Clifford algebra. -/
noncomputable def typeBQuadraticEquiv :
    LieAlgebra.Orthogonal.typeB ι K ≃ₗ⁅K⁆ quadraticLieSubalgebra Q := by
  let _ : Module.Finite K V := Module.Finite.of_basis (P.typeBBasis b z hz)
  exact (P.typeBSkewAdjointEquiv b z hz).trans
    (soEquivQuadratic Q (P.nondegenerate
      ((isUnit_of_invertible (2 : K)).isSMulRegular K)))

/-- The type-`B` comparison acts on Clifford generators through the corresponding matrix
endomorphism in the odd hyperbolic basis. -/
@[simp]
theorem typeBQuadraticEquiv_lie_ι (A : LieAlgebra.Orthogonal.typeB ι K) (x : V) :
    ⁅(P.typeBQuadraticEquiv b z hz A : CliffordAlgebra Q), CliffordAlgebra.ι Q x⁆ =
      CliffordAlgebra.ι Q
        ((LinearMap.toMatrixAlgEquiv (P.typeBBasis b z hz)).symm A x) := by
  let _ : Module.Finite K V := Module.Finite.of_basis (P.typeBBasis b z hz)
  rw [typeBQuadraticEquiv, LieEquiv.trans_apply, soEquivQuadratic_lie_ι]
  rw [P.typeBSkewAdjointEquiv_apply]

end Quadratic

end SpinPolarizationData

end TauCeti
