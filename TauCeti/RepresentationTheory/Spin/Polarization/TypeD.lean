/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeD.DiagonalCartan
public import TauCeti.LinearAlgebra.CliffordAlgebra.Quadratic.Realization
public import TauCeti.RepresentationTheory.Spin.Weight
public import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-!
# The type-D matrix model of a polarization

An even polarization identifies a quadratic space with the split space on two copies of the
isotropic basis. This file compares that basis with Mathlib's matrix model of the type-`D` Lie
algebra and then with the quadratic elements of the Clifford algebra.

The standard diagonal matrix indexed by `i` acts by `1` on the `i`-th isotropic basis vector and
by `-1` on its dual. Under the comparison it is therefore the diagonal Clifford bivector used to
compute the spin weights.

## References

* [Tau Ceti Roadmap, Spin Representations, Layer 5](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SpinRepresentations/README.md#layer-5-the-fundamental-representations-of-b%E2%82%97-and-d%E2%82%97)
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

/-- The linear coordinates of an even polarization, after discarding its zero remainder. -/
private noncomputable def evenDecompositionEquiv (hline : P.line = ⊥) :
    (P.W × P.W') ≃ₗ[K] V := by
  letI : Unique P.line :=
    { default := 0
      uniq := fun z => Subtype.ext (by simpa [hline] using z.property) }
  exact LinearEquiv.prodUnique.symm.trans P.decompositionEquiv

private theorem evenDecompositionEquiv_apply (hline : P.line = ⊥) (x : P.W × P.W') :
    P.evenDecompositionEquiv hline x = (x.1 : V) + x.2 := by
  -- `prodUnique.symm` inserts the unique coordinate of the zero remainder.
  change P.decompositionEquiv (x, default) = _
  rw [P.decompositionEquiv_apply]
  have hz : (default : P.line) = 0 := by
    apply Subtype.ext
    simpa [hline] using (default : P.line).property
  rw [hz]
  simp

/-- The hyperbolic basis of an even polarization: first `b`, then its polar-dual basis. -/
noncomputable def typeDBasis (hline : P.line = ⊥) : Module.Basis (ι ⊕ ι) K V :=
  (b.prod (P.dualBasis b)).map (P.evenDecompositionEquiv hline)

@[simp]
theorem typeDBasis_inl (hline : P.line = ⊥) (i : ι) :
    P.typeDBasis b hline (.inl i) = (b i : V) := by
  simp [typeDBasis, P.evenDecompositionEquiv_apply]

@[simp]
theorem typeDBasis_inr (hline : P.line = ⊥) (i : ι) :
    P.typeDBasis b hline (.inr i) = (P.dualVector b i : V) := by
  simp [typeDBasis, P.evenDecompositionEquiv_apply]

/-- In the hyperbolic basis, the polar form has the standard split type-`D` Gram matrix. -/
theorem polarBilin_toMatrix_typeDBasis (hline : P.line = ⊥) :
    LinearMap.BilinForm.toMatrix (P.typeDBasis b hline) Q.polarBilin =
      LieAlgebra.Orthogonal.JD ι K := by
  ext (i | i) (j | j)
  · simp [LinearMap.BilinForm.toMatrix_apply, LieAlgebra.Orthogonal.JD,
      P.polar_W_eq_zero]
  · simp [LinearMap.BilinForm.toMatrix_apply, LieAlgebra.Orthogonal.JD,
      QuadraticMap.polarBilin_apply_apply, P.polar_dualVector, Matrix.one_apply]
  · rw [LinearMap.BilinForm.toMatrix_apply, typeDBasis_inr, typeDBasis_inl,
      QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm, P.polar_dualVector]
    simp [LieAlgebra.Orthogonal.JD, Matrix.one_apply, eq_comm]
  · simp [LinearMap.BilinForm.toMatrix_apply, LieAlgebra.Orthogonal.JD,
      P.polar_W'_eq_zero]

private theorem mem_typeD_toMatrix_iff (hline : P.line = ⊥) (f : Module.End K V) :
    LinearMap.toMatrix (P.typeDBasis b hline) (P.typeDBasis b hline) f ∈
        LieAlgebra.Orthogonal.typeD ι K ↔
      f ∈ skewAdjointLieSubalgebra Q.polarBilin := by
  have hB : Matrix.toLinearMap₂ (P.typeDBasis b hline) (P.typeDBasis b hline)
      (LieAlgebra.Orthogonal.JD ι K) = Q.polarBilin := by
    rw [← P.polarBilin_toMatrix_typeDBasis b hline]
    exact Matrix.toLinearMap₂_toMatrix₂ _ _ Q.polarBilin
  -- Convert the matrix Gram equation to the basis-free bilinear form before comparing
  -- skew-adjointness.
  rw [LieAlgebra.Orthogonal.typeD, mem_skewAdjointMatricesLieSubalgebra,
    mem_skewAdjointMatricesSubmodule]
  -- Expose the two bundled skew-adjoint predicates after transporting the Gram matrix.
  change (LieAlgebra.Orthogonal.JD ι K).IsSkewAdjoint
      (LinearMap.toMatrix (P.typeDBasis b hline) (P.typeDBasis b hline) f) ↔
    f ∈ Q.polarBilin.skewAdjointSubmodule
  rw [LinearMap.mem_skewAdjointSubmodule]
  rw [Matrix.IsSkewAdjoint, LinearMap.IsSkewAdjoint]
  symm
  simpa [hB] using
    (isAdjointPair_toLinearMap₂
      (b₁ := P.typeDBasis b hline) (b₂ := P.typeDBasis b hline)
      (J := LieAlgebra.Orthogonal.JD ι K) (J' := LieAlgebra.Orthogonal.JD ι K)
      (A := LinearMap.toMatrix (P.typeDBasis b hline) (P.typeDBasis b hline) f)
      (A' := -(LinearMap.toMatrix (P.typeDBasis b hline) (P.typeDBasis b hline) f)))

/-- The split matrix model transported to skew-adjoint endomorphisms through the hyperbolic
basis. -/
private noncomputable def typeDSkewAdjointEquiv
    (b : Module.Basis ι K P.W) (hline : P.line = ⊥) :
    LieAlgebra.Orthogonal.typeD ι K ≃ₗ⁅K⁆ skewAdjointLieSubalgebra Q.polarBilin :=
  LieEquiv.ofSubalgebras _ _
    (LinearMap.toMatrixAlgEquiv (P.typeDBasis b hline)).symm.toLieEquiv <| by
      ext f
      simp only [Submodule.mem_map_equiv, LieSubalgebra.mem_map_submodule]
      -- Membership in the mapped subalgebra is the underlying matrix membership statement.
      change LinearMap.toMatrix (P.typeDBasis b hline) (P.typeDBasis b hline) f ∈
          LieAlgebra.Orthogonal.typeD ι K ↔
        f ∈ skewAdjointLieSubalgebra Q.polarBilin
      exact P.mem_typeD_toMatrix_iff b hline f

@[simp]
private theorem typeDSkewAdjointEquiv_apply (hline : P.line = ⊥)
    (A : LieAlgebra.Orthogonal.typeD ι K) :
    (P.typeDSkewAdjointEquiv b hline A : Module.End K V) =
      (LinearMap.toMatrixAlgEquiv (P.typeDBasis b hline)).symm A := by
  rfl

end PreQuadratic

section Quadratic

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} (P : SpinPolarizationData Q)
  {ι : Type w} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K P.W)
  [Invertible (2 : K)]

/-- An even polarization identifies the split type-`D` matrix algebra with the quadratic
elements of the Clifford algebra. -/
noncomputable def typeDQuadraticEquiv
    (b : Module.Basis ι K P.W) (hline : P.line = ⊥) :
    LieAlgebra.Orthogonal.typeD ι K ≃ₗ⁅K⁆ quadraticLieSubalgebra Q := by
  let _ : Module.Finite K V := Module.Finite.of_basis (P.typeDBasis b hline)
  exact (P.typeDSkewAdjointEquiv b hline).trans
    (soEquivQuadratic Q (P.nondegenerate_of_line_eq_bot hline))

/-- The type-`D` comparison acts on Clifford generators through the corresponding matrix
endomorphism in the hyperbolic basis. -/
@[simp]
theorem typeDQuadraticEquiv_lie_ι (hline : P.line = ⊥)
    (A : LieAlgebra.Orthogonal.typeD ι K) (x : V) :
    ⁅(P.typeDQuadraticEquiv b hline A : CliffordAlgebra Q), CliffordAlgebra.ι Q x⁆ =
      CliffordAlgebra.ι Q
        ((LinearMap.toMatrixAlgEquiv (P.typeDBasis b hline)).symm A x) := by
  let _ : Module.Finite K V := Module.Finite.of_basis (P.typeDBasis b hline)
  rw [typeDQuadraticEquiv, LieEquiv.trans_apply, soEquivQuadratic_lie_ι]
  rw [P.typeDSkewAdjointEquiv_apply]

/-- The standard one-coordinate diagonal matrix is the diagonal Clifford bivector of the
corresponding polarization coordinate. -/
@[simp] private theorem typeDQuadraticEquiv_typeDDiagonalMatrix_single
    (hline : P.line = ⊥) (i : ι) :
    P.typeDQuadraticEquiv b hline
        ⟨typeDDiagonalMatrix (Pi.single i 1),
          typeDDiagonalMatrix_mem_typeD (Pi.single i 1)⟩ =
      ⟨P.diagonalBivector b i, P.diagonalBivector_mem_quadraticLieSubalgebra b i⟩ := by
  let _ : Module.Finite K V := Module.Finite.of_basis (P.typeDBasis b hline)
  apply quadraticLieSubalgebra_ext Q (P.nondegenerate_of_line_eq_bot hline)
  intro x
  rw [P.typeDQuadraticEquiv_lie_ι b hline]
  -- The extensionality goal compares the underlying Clifford commutators.
  change _ = ⁅P.diagonalBivector b i, CliffordAlgebra.ι Q x⁆
  rw [P.diagonalBivector_def b, bivector_lie_ι]
  apply congrArg (CliffordAlgebra.ι Q)
  let g : Module.End K V :=
    (Q.polarBilin (P.dualVector b i)).smulRight (b i : V) -
      (Q.polarBilin (b i : V)).smulRight (P.dualVector b i : V)
  -- Name the endomorphism produced by the bivector action before comparing it on a basis.
  change _ = g x
  apply LinearMap.congr_fun
  apply (P.typeDBasis b hline).ext
  rintro (j | j)
  -- Each branch exposes the matrix action and the corresponding polar-form coordinate of `g`.
  · change Matrix.toLin (P.typeDBasis b hline) (P.typeDBasis b hline)
        (typeDDiagonalMatrix (Pi.single i 1))
        (P.typeDBasis b hline (.inl j)) = g (P.typeDBasis b hline (.inl j))
    rw [Matrix.toLin_self]
    simp only [typeDDiagonalMatrix_apply, ite_smul, zero_smul, Finset.sum_ite_eq',
      Finset.mem_univ, ↓reduceIte, typeDDiagonalValue_inl, typeDBasis_inl]
    -- Expand `g` on the first isotropic coordinate.
    change _ = QuadraticMap.polar Q (P.dualVector b i : V) (b j : V) • (b i : V) -
      QuadraticMap.polar Q (b i : V) (b j : V) • (P.dualVector b i : V)
    rw [P.polar_W_eq_zero, zero_smul, sub_zero]
    rw [QuadraticMap.polar_comm, P.polar_dualVector, Pi.single_apply]
    split <;> simp_all [eq_comm]
  -- The second coordinate has the opposite diagonal sign.
  · change Matrix.toLin (P.typeDBasis b hline) (P.typeDBasis b hline)
        (typeDDiagonalMatrix (Pi.single i 1))
        (P.typeDBasis b hline (.inr j)) = g (P.typeDBasis b hline (.inr j))
    rw [Matrix.toLin_self]
    simp only [typeDDiagonalMatrix_apply, ite_smul, zero_smul, Finset.sum_ite_eq',
      Finset.mem_univ, ↓reduceIte, typeDDiagonalValue_inr, typeDBasis_inr, neg_smul]
    -- Expand `g` on the polar-dual coordinate.
    change _ = QuadraticMap.polar Q (P.dualVector b i : V) (P.dualVector b j : V) •
        (b i : V) -
      QuadraticMap.polar Q (b i : V) (P.dualVector b j : V) • (P.dualVector b i : V)
    rw [P.polar_W'_eq_zero, zero_smul, zero_sub, P.polar_dualVector, neg_inj]
    rw [Pi.single_apply]
    split <;> simp_all [eq_comm]

/-- The standard diagonal Cartan basis maps to the diagonal Clifford bivectors of the
polarization. -/
theorem typeDQuadraticEquiv_typeDDiagonalCartanBasis (hline : P.line = ⊥) (i : ι) :
    P.typeDQuadraticEquiv b hline
        ((typeDDiagonalCartanBasis (K := K) (ι := ι) i : typeDDiagonalCartan K ι) :
          LieAlgebra.Orthogonal.typeD ι K) =
      ⟨P.diagonalBivector b i, P.diagonalBivector_mem_quadraticLieSubalgebra b i⟩ := by
  let _ : Module.Finite K V := Module.Finite.of_basis (P.typeDBasis b hline)
  rw [coe_typeDDiagonalCartanBasis_apply]
  exact P.typeDQuadraticEquiv_typeDDiagonalMatrix_single b hline i

/-- The inverse comparison sends a diagonal Clifford bivector back to the standard diagonal
generator. -/
@[simp]
theorem typeDQuadraticEquiv_symm_diagonalBivector (hline : P.line = ⊥) (i : ι) :
    (P.typeDQuadraticEquiv b hline).symm
        ⟨P.diagonalBivector b i, P.diagonalBivector_mem_quadraticLieSubalgebra b i⟩ =
      ((typeDDiagonalCartanBasis (K := K) (ι := ι) i : typeDDiagonalCartan K ι) :
        LieAlgebra.Orthogonal.typeD ι K) := by
  let _ : Module.Finite K V := Module.Finite.of_basis (P.typeDBasis b hline)
  rw [← P.typeDQuadraticEquiv_typeDDiagonalCartanBasis b hline]
  exact (P.typeDQuadraticEquiv b hline).symm_apply_apply _

end Quadratic

end SpinPolarizationData

namespace SpinPolarizationData

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} (P : SpinPolarizationData Q)
  {ι : Type w} [Fintype ι] [LinearOrder ι] (b : Module.Basis ι K P.W)
  [Invertible (2 : K)]

/-- Through the type-`D` comparison, the standard diagonal generator acts on the exterior basis
with the corresponding spin weight. -/
theorem spinAction_typeDQuadraticEquiv_basis (hline : P.line = ⊥) (i : ι) (s : Finset ι) :
    spinAction Q P
        (P.typeDQuadraticEquiv b hline
          ((typeDDiagonalCartanBasis (K := K) (ι := ι) i : typeDDiagonalCartan K ι) :
            LieAlgebra.Orthogonal.typeD ι K))
        (b.ExteriorAlgebra s) =
      spinWeight K s i • b.ExteriorAlgebra s := by
  let _ : Module.Finite K V := Module.Finite.of_basis (P.typeDBasis b hline)
  rw [P.typeDQuadraticEquiv_typeDDiagonalCartanBasis b hline]
  exact P.spinAction_diagonalBivector_basis b i s

end SpinPolarizationData

end TauCeti
