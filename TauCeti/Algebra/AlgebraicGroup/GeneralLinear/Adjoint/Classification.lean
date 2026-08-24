/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Adjoint.RootSpace

/-!
# Classification of the adjoint roots of the general linear group

For `GL_n` with its diagonal split torus, this file proves the converse to the matrix-unit weight
calculation: every nontrivial adjoint weight is uniquely `e_i - e_j` for an ordered pair `i ≠ j`,
and its weight space is the line spanned by `E_ij`.  In particular, every such root space has
dimension one over the base field.

The proof reads an arbitrary weight vector entrywise.  The universal diagonal adjoint action
multiplies its `(i, j)` entry by the group-algebra basis element for `e_i - e_j`; comparing this
with the defining action of its weight shows that every nonzero entry determines the weight.

## Main declarations

* `TauCeti.GeneralLinear.matrixUnitWeight_eq_matrixUnitWeight_iff`: off the diagonal, matrix-unit
  weights remember their ordered pairs.
* `TauCeti.GeneralLinear.matrixUnitWeight_eq_of_mem_adjointWeightSpace`: a nonzero entry of a
  weight vector determines its weight.
* `TauCeti.GeneralLinear.mem_nontrivialAdjointWeights_iff`: the nontrivial adjoint weights are
  exactly the characters `e_i - e_j` with `i ≠ j`.
* `TauCeti.GeneralLinear.adjointWeightSpace_matrixUnitWeight_eq_span`: the `e_i - e_j` weight space
  is the line spanned by `E_ij`.
* `TauCeti.GeneralLinear.finrank_adjointWeightSpace_matrixUnitWeight`: every root space has
  dimension one.

## References

* J. S. Milne, *Algebraic Groups* (2017), §21.1.
* J. E. Humphreys, *Linear Algebraic Groups* (1975), §26.3.

This completes the adjoint-root classification for the `GL_n` worked example in Layer 7, "Root
datum of `(G,T)`", of the ReductiveGroups roadmap.
-/

public section

open CategoryTheory TensorProduct WithConv

namespace TauCeti.GeneralLinear

universe u

noncomputable section

variable {k : Type u} [Field k] {n : ℕ}

/-- Off the diagonal, the character `e_i - e_j` determines the ordered pair `(i, j)`.  Character
lattices retain this distinction in every field characteristic, including characteristic two. -/
@[simp]
theorem matrixUnitWeight_eq_matrixUnitWeight_iff {i j : Fin n} (hij : i ≠ j) (a b : Fin n) :
    (matrixUnitWeight a b : Multiplicative (ULift.{u} (Fin n) →₀ ℤ)) =
      matrixUnitWeight i j ↔ a = i ∧ b = j := by
  constructor
  · intro h
    have hi := congrArg
      (fun alpha : Multiplicative (ULift.{u} (Fin n) →₀ ℤ) ↦
        Multiplicative.toAdd alpha (ULift.up i)) h
    have hai : a = i := by
      by_contra hai
      by_cases hbi : b = i
      · subst b
        simp [toAdd_matrixUnitWeight_apply, Ne.symm hai, hij] at hi
      · simp [toAdd_matrixUnitWeight_apply, Ne.symm hai, Ne.symm hbi, hij] at hi
    subst a
    have hj := congrArg
      (fun alpha : Multiplicative (ULift.{u} (Fin n) →₀ ℤ) ↦
        Multiplicative.toAdd alpha (ULift.up j)) h
    have hbj : b = j := by
      by_contra hbj
      simp [toAdd_matrixUnitWeight_apply] at hj
      exact hbj hj.symm
    exact ⟨rfl, hbj⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- A scalar from the coefficient field can be absorbed into the coefficient of a group-algebra
basis element. -/
private theorem single_one_mul_algebraMap (alpha : Multiplicative (ULift.{u} (Fin n) →₀ ℤ))
    (c : k) :
    MonoidAlgebra.single alpha 1 *
        algebraMap k (MonoidAlgebra k (Multiplicative (ULift.{u} (Fin n) →₀ ℤ))) c =
      MonoidAlgebra.single alpha c := by
  rw [mul_comm, ← Algebra.smul_def, MonoidAlgebra.smul_single]
  simp

/-- If the `(i, j)` entry of an adjoint weight vector is nonzero, then its weight is
`e_i - e_j`. -/
theorem matrixUnitWeight_eq_of_mem_adjointWeightSpace
    {alpha : Multiplicative (ULift.{u} (Fin n) →₀ ℤ)}
    {x : Module.Dual k (Bialgebra.CotangentSpace k (coordinateHopfAlgebra k n))}
    (hx : x ∈ Derivation.adjointWeightSpace
      (diagonalTorusCoordinateMap (R := k) (N := n)).hom alpha)
    {i j : Fin n} (hentry : (cotangentDualMatrixEquiv x) i j ≠ 0) :
    matrixUnitWeight i j = alpha := by
  let M := Multiplicative (ULift.{u} (Fin n) →₀ ℤ)
  let K := MonoidAlgebra k M
  have haction :=
    (Derivation.mem_adjointWeightSpace_iff_universalPointAction
      (diagonalTorusCoordinateMap (R := k) (N := n)).hom alpha x).mp hx
  have hentryAction := congrArg
    (fun y : K ⊗[k]
        Module.Dual k (Bialgebra.CotangentSpace k (coordinateHopfAlgebra k n)) ↦
      tangentMatrix n
        (Derivation.tangentScalarExtensionEquiv
          (R := k) (A := coordinateHopfAlgebra k n) (B := K) y) i j)
    haction
  rw [tangentMatrix_universalDiagonalAdjointAction_apply,
    tangentMatrix_tangentScalarExtensionEquiv_tmul, Matrix.smul_apply, Matrix.map_apply,
    smul_eq_mul, single_one_mul_algebraMap] at hentryAction
  exact MonoidAlgebra.single_left_injective hentry hentryAction

/-- The nontrivial adjoint weights of `GL_n` relative to its diagonal torus are exactly the
characters `e_i - e_j` for ordered pairs `i ≠ j`. -/
theorem mem_nontrivialAdjointWeights_iff
    (alpha : Multiplicative (ULift.{u} (Fin n) →₀ ℤ)) :
    alpha ∈ Derivation.nontrivialAdjointWeights
        (diagonalTorusCoordinateMap (R := k) (N := n)).hom ↔
      ∃ i j, i ≠ j ∧ alpha = matrixUnitWeight i j := by
  constructor
  · rw [Derivation.mem_nontrivialAdjointWeights]
    rintro ⟨halpha, hspace⟩
    obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).mp hspace
    have hmatrix0 : cotangentDualMatrixEquiv x ≠ 0 := by
      intro hmatrix
      apply hx0
      apply (cotangentDualMatrixEquiv (k := k) (n := n)).injective
      simpa using hmatrix
    obtain ⟨i, j, hentry⟩ : ∃ i j, (cotangentDualMatrixEquiv x) i j ≠ 0 := by
      by_contra hentries
      push Not at hentries
      apply hmatrix0
      ext i j
      exact hentries i j
    have hweight := matrixUnitWeight_eq_of_mem_adjointWeightSpace hx hentry
    refine ⟨i, j, ?_, hweight.symm⟩
    intro hij
    subst j
    exact halpha (hweight.symm.trans (matrixUnitWeight_self i))
  · rintro ⟨i, j, hij, rfl⟩
    exact matrixUnitWeight_mem_nontrivialAdjointWeights (k := k) hij

/-- The set of nontrivial adjoint weights of `GL_n` is the set of off-diagonal matrix-unit
characters. -/
theorem nontrivialAdjointWeights_eq_setOf_matrixUnitWeight :
    Derivation.nontrivialAdjointWeights
        (diagonalTorusCoordinateMap (R := k) (N := n)).hom =
      {alpha | ∃ i j, i ≠ j ∧ alpha = matrixUnitWeight i j} := by
  ext alpha
  exact mem_nontrivialAdjointWeights_iff alpha

/-- The adjoint weight space for an off-diagonal character `e_i - e_j` is exactly the line
spanned by the matrix-unit tangent vector `E_ij`. -/
theorem adjointWeightSpace_matrixUnitWeight_eq_span {i j : Fin n} (hij : i ≠ j) :
    Derivation.adjointWeightSpace
        (diagonalTorusCoordinateMap (R := k) (N := n)).hom (matrixUnitWeight i j) =
      k ∙ matrixUnitTangent (k := k) i j := by
  apply le_antisymm
  · intro x hx
    rw [Submodule.mem_span_singleton]
    refine ⟨(cotangentDualMatrixEquiv x) i j, ?_⟩
    apply (cotangentDualMatrixEquiv (k := k) (n := n)).injective
    ext a b
    rw [map_smul, cotangentDualMatrixEquiv_matrixUnitTangent, Matrix.smul_apply]
    simp only [Matrix.single_apply, smul_eq_mul]
    by_cases hab : i = a ∧ j = b
    · obtain ⟨rfl, rfl⟩ := hab
      simp
    · rw [ite_eq_right hab, mul_zero]
      apply Eq.symm
      by_contra hentry
      have hweight := matrixUnitWeight_eq_of_mem_adjointWeightSpace hx hentry
      have hpairs := (matrixUnitWeight_eq_matrixUnitWeight_iff hij a b).mp hweight
      exact hab ⟨hpairs.1.symm, hpairs.2.symm⟩
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact matrixUnitTangent_mem_adjointWeightSpace (k := k) i j

/-- Every nontrivial matrix-unit adjoint weight space of `GL_n` is one-dimensional. -/
theorem finrank_adjointWeightSpace_matrixUnitWeight {i j : Fin n} (hij : i ≠ j) :
    Module.finrank k
      (Derivation.adjointWeightSpace
        (diagonalTorusCoordinateMap (R := k) (N := n)).hom (matrixUnitWeight i j)) = 1 := by
  rw [adjointWeightSpace_matrixUnitWeight_eq_span hij]
  exact finrank_span_singleton (matrixUnitTangent_ne_zero (k := k) i j)

end

end TauCeti.GeneralLinear
