/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.FunctorOfPoints
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Basic

/-!
# The tangent Lie algebra of the general linear group

The tangent space at the identity of `GLₙ` is the full matrix algebra.  A tangent vector is a
counit-valued derivation of the coordinate Hopf algebra `O(GLₙ)`; its matrix is obtained by
evaluating the derivation on the generic coordinate entries.  We prove that this is a linear
equivalence and that it identifies the convolution Lie bracket with the matrix commutator.

The proof uses the functor-of-points description of `GLₙ`.  Over the dual numbers, the matrices
reducing to the identity are exactly `1 + εX`, with inverse `1 - εX`.  The existing equivalences
between derivations, tangent-kernel points, and invertible matrices therefore give both injectivity
and surjectivity without choosing a presentation of derivations on the determinant localization.

## Main declarations

* `TauCeti.GeneralLinear.tangentMatrix`: evaluate a tangent derivation on the generic entries.
* `TauCeti.GeneralLinear.tangentLinearEquivMatrix`: the tangent space of `GLₙ` is linearly
  equivalent to `n × n` matrices.
* `TauCeti.GeneralLinear.tangentLieEquivMatrix`: the same equivalence as an equivalence of Lie
  algebras, carrying the tangent bracket to the matrix commutator.

## References

* J. S. Milne, *Algebraic Groups* (2017), §14.
-/

public section

open scoped TensorProduct

namespace TauCeti

namespace GeneralLinear

open TrivSqZeroExt WithConv

attribute [local instance 100] LieRing.ofAssociativeRing

universe u w

noncomputable section

private noncomputable def dualMatrix {C : Type*} [CommRing C] {n : ℕ}
    (X : Matrix (Fin n) (Fin n) C) : Matrix (Fin n) (Fin n) (DualNumber C) :=
  fun i j ↦ inl ((1 : Matrix (Fin n) (Fin n) C) i j) + inr (X i j)

private theorem dualMatrix_mul_neg {C : Type*} [CommRing C] {n : ℕ}
    (X : Matrix (Fin n) (Fin n) C) : dualMatrix X * dualMatrix (-X) = 1 := by
  apply Matrix.ext
  intro i j
  -- Expose matrix multiplication so the two dual-number components can be computed separately.
  change (∑ x, dualMatrix X i x * dualMatrix (-X) x j) =
    (1 : Matrix (Fin n) (Fin n) (DualNumber C)) i j
  apply TrivSqZeroExt.ext
  · simp only [dualMatrix, fst_sum, fst_mul, fst_add, fst_inl, fst_inr, add_zero]
    classical simp [Matrix.one_apply]
    split_ifs <;> simp
  · simp only [dualMatrix, snd_sum, snd_mul, fst_add, fst_inl, fst_inr, snd_add,
      snd_inl, snd_inr, add_zero, zero_add]
    classical simp [Matrix.one_apply, Finset.sum_add_distrib]
    split_ifs <;> simp

private theorem dualMatrix_neg_mul {C : Type*} [CommRing C] {n : ℕ}
    (X : Matrix (Fin n) (Fin n) C) : dualMatrix (-X) * dualMatrix X = 1 := by
  simpa only [neg_neg] using dualMatrix_mul_neg (-X)

private noncomputable def dualMatrixGeneralLinear {C : Type*} [CommRing C] {n : ℕ}
    (X : Matrix (Fin n) (Fin n) C) : Matrix.GeneralLinearGroup (Fin n) (DualNumber C) where
  val := dualMatrix X
  inv := dualMatrix (-X)
  val_inv := dualMatrix_mul_neg X
  inv_val := dualMatrix_neg_mul X

@[simp]
private theorem dualMatrixGeneralLinear_apply {C : Type*} [CommRing C] {n : ℕ}
    (X : Matrix (Fin n) (Fin n) C) (i j : Fin n) :
    dualMatrixGeneralLinear X i j =
      inl ((1 : Matrix (Fin n) (Fin n) C) i j) + inr (X i j) :=
  rfl

variable {R : Type u} [CommRing R] {B : Type w} [CommRing B] [Algebra R B]
variable (n : ℕ)

local notation "H" => coordinateHopfAlgebra

/-- The matrix of a tangent vector to `GLₙ`, obtained by evaluating the derivation on the
generic coordinate entries. -/
noncomputable def tangentMatrix :
    Derivation R (H (R := R) n)
        (Bialgebra.CounitAlgebra R (H (R := R) n) B) →ₗ[B]
      Matrix (Fin n) (Fin n) B where
  toFun d i j := Bialgebra.CounitAlgebra.algEquivSelf R (H (R := R) n) B
    (d (coordinateHopfAlgebraAlgEquiv R n
      (coordinateRingMap R n (MvPolynomial.X (i, j)))))
  map_add' d e := by
    ext i j
    -- Expose the pointwise definition of `tangentMatrix` to use additivity of the derivation.
    change Bialgebra.CounitAlgebra.algEquivSelf R (H (R := R) n) B
        (d (coordinateHopfAlgebraAlgEquiv R n
            (coordinateRingMap R n (MvPolynomial.X (i, j)))) +
          e (coordinateHopfAlgebraAlgEquiv R n
            (coordinateRingMap R n (MvPolynomial.X (i, j))))) = _
    rw [map_add]
    rfl
  map_smul' b d := by
    ext i j
    exact algEquivSelf_derivation_smul_apply b d _

@[simp]
theorem tangentMatrix_apply (d : Derivation R (H (R := R) n)
    (Bialgebra.CounitAlgebra R (H (R := R) n) B)) (i j : Fin n) :
    tangentMatrix n d i j = Bialgebra.CounitAlgebra.algEquivSelf R (H (R := R) n) B
      (d (coordinateHopfAlgebraAlgEquiv R n
        (coordinateRingMap R n (MvPolynomial.X (i, j))))) :=
  by
    -- Expose the `toFun` field of the public linear map to state its computation rule.
    change Bialgebra.CounitAlgebra.algEquivSelf R (H (R := R) n) B
      (d (coordinateHopfAlgebraAlgEquiv R n
        (coordinateRingMap R n (MvPolynomial.X (i, j))))) = _
    rfl

private theorem tangentPoint_matrix_snd (d : Derivation R (H (R := R) n)
    (Bialgebra.CounitAlgebra R (H (R := R) n) B)) (i j : Fin n) :
    snd ((pointsMulEquiv (R := R) n
      (derivationMulEquivTangentKer R (H (R := R) n) B (.ofAdd d)).val) i j) =
      d (coordinateHopfAlgebraAlgEquiv R n
        (coordinateRingMap R n (MvPolynomial.X (i, j)))) := by
  rw [pointsMulEquiv_apply, pointToGeneralLinear_apply]
  exact derivationMulEquivTangentKer_apply_snd (.ofAdd d) _

private theorem tangentPoint_matrix_fst (d : Derivation R (H (R := R) n)
    (Bialgebra.CounitAlgebra R (H (R := R) n) B)) (i j : Fin n) :
    fst ((pointsMulEquiv (R := R) n
      (derivationMulEquivTangentKer R (H (R := R) n) B (.ofAdd d)).val) i j) =
      (1 : Matrix (Fin n) (Fin n)
        (Bialgebra.CounitAlgebra R (H (R := R) n) B)) i j := by
  let q := derivationMulEquivTangentKer R (H (R := R) n) B (.ofAdd d)
  have hqmem : q.val ∈ (dualNumberReduction R (H (R := R) n) B).ker := by
    rw [← tangentKer_def]
    exact q.prop
  have hq : dualNumberReduction R (H (R := R) n) B q.val = 1 :=
    MonoidHom.mem_ker.mp hqmem
  have h := congrArg (pointsMulEquiv (R := R)
    (A := Bialgebra.CounitAlgebra R (H (R := R) n) B) n) hq
  rw [dualNumberReduction_def, pointsMulEquiv_mapValue] at h
  have hij := congrArg (fun g : Matrix.GeneralLinearGroup (Fin n)
      (Bialgebra.CounitAlgebra R (H (R := R) n) B) ↦ g i j) h
  -- Expose how reduction and the point equivalence act on matrix entries before using `map_one`.
  change fst ((pointsMulEquiv (R := R) n q.val) i j) =
    (pointsMulEquiv (R := R) n (1 : WithConv (H (R := R) n →ₐ[R]
      Bialgebra.CounitAlgebra R (H (R := R) n) B))) i j at hij
  rw [map_one] at hij
  -- Identify the mapped identity with the identity matrix entry.
  change fst ((pointsMulEquiv (R := R) n q.val) i j) =
    (1 : Matrix.GeneralLinearGroup (Fin n)
      (Bialgebra.CounitAlgebra R (H (R := R) n) B)) i j
  exact hij

private theorem tangentMatrix_injective :
    Function.Injective (tangentMatrix (R := R) (B := B) n) := by
  intro d e hde
  have htag : Multiplicative.ofAdd d = Multiplicative.ofAdd e := by
    apply (derivationMulEquivTangentKer R (H (R := R) n) B).injective
    apply Subtype.ext
    apply (pointsMulEquiv (R := R) n).injective
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    apply TrivSqZeroExt.ext
    · rw [tangentPoint_matrix_fst, tangentPoint_matrix_fst]
    · rw [tangentPoint_matrix_snd, tangentPoint_matrix_snd]
      apply (Bialgebra.CounitAlgebra.algEquivSelf R (H (R := R) n) B).injective
      exact congr_fun (congr_fun hde i) j
  exact congrArg Multiplicative.toAdd htag

private theorem dualMatrixGeneralLinear_map_fst {C : Type*} [CommRing C] [Algebra R C]
    (X : Matrix (Fin n) (Fin n) C) :
    Matrix.GeneralLinearGroup.map (fstHom R C C).toRingHom
        (dualMatrixGeneralLinear X) = 1 := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  simp [dualMatrixGeneralLinear_apply]

private theorem tangentMatrix_surjective :
    Function.Surjective (tangentMatrix (R := R) (B := B) n) := by
  intro X
  let C := Bialgebra.CounitAlgebra R (H (R := R) n) B
  let X' : Matrix (Fin n) (Fin n) C := fun i j ↦
    (Bialgebra.CounitAlgebra.algEquivSelf R (H (R := R) n) B).symm (X i j)
  let g : Matrix.GeneralLinearGroup (Fin n) (DualNumber C) := dualMatrixGeneralLinear X'
  let q : WithConv (H (R := R) n →ₐ[R] DualNumber C) :=
    (pointsMulEquiv (R := R) n).symm g
  have hq : q ∈ tangentKer R (H (R := R) n) B := by
    rw [tangentKer_def, MonoidHom.mem_ker]
    rw [dualNumberReduction_def]
    apply (pointsMulEquiv (R := R) n).injective
    rw [pointsMulEquiv_mapValue]
    simp only [q, MulEquiv.apply_symm_apply, map_one]
    exact dualMatrixGeneralLinear_map_fst (R := R) n X'
  let d := ((derivationMulEquivTangentKer R (H (R := R) n) B).symm ⟨q, hq⟩).toAdd
  refine ⟨d, ?_⟩
  ext i j
  rw [tangentMatrix_apply]
  dsimp only [d]
  rw [derivationMulEquivTangentKer_symm_apply]
  rw [← pointToGeneralLinear_apply (R := R) n q i j]
  rw [← pointsMulEquiv_apply]
  -- Expose the second dual-number component represented by the tangent point.
  change Bialgebra.CounitAlgebra.algEquivSelf R (H (R := R) n) B
      (snd ((pointsMulEquiv (R := R) n q) i j)) = X i j
  -- Unfold the chosen point through the inverse of the point equivalence.
  rw [show pointsMulEquiv (R := R) n q = g from MulEquiv.apply_symm_apply _ g]
  rw [dualMatrixGeneralLinear_apply]
  simp only [snd_add, snd_inl, snd_inr, zero_add]
  exact (Bialgebra.CounitAlgebra.algEquivSelf R (H (R := R) n) B).apply_symm_apply _

/-- **The tangent space at the identity of `GLₙ` is the full matrix algebra.** The equivalence
sends a counit-valued derivation to its values on the generic matrix entries. -/
noncomputable def tangentLinearEquivMatrix :
    Derivation R (H (R := R) n)
        (Bialgebra.CounitAlgebra R (H (R := R) n) B) ≃ₗ[B]
      Matrix (Fin n) (Fin n) B :=
  LinearEquiv.ofBijective (tangentMatrix (R := R) (B := B) n)
    ⟨tangentMatrix_injective n, tangentMatrix_surjective n⟩

@[simp]
theorem tangentLinearEquivMatrix_apply (d : Derivation R (H (R := R) n)
    (Bialgebra.CounitAlgebra R (H (R := R) n) B)) :
    tangentLinearEquivMatrix n d = tangentMatrix n d :=
  by
    -- `LinearEquiv.ofBijective` retains the original map as its forward function.
    change tangentMatrix n d = _
    rfl

/-- The tangent-matrix equivalence identifies the convolution Lie bracket with the matrix
commutator. -/
@[simp]
theorem tangentMatrix_lie (d e : Derivation R (H (R := R) n)
    (Bialgebra.CounitAlgebra R (H (R := R) n) B)) :
    tangentMatrix n ⁅d, e⁆ = ⁅tangentMatrix n d, tangentMatrix n e⁆ := by
  ext i j
  rw [tangentMatrix_apply, Derivation.bracket_apply, coordinateHopfAlgebra_comul_X]
  simp [Matrix.mul_apply, tangentMatrix_apply, LieRing.of_associative_ring_bracket]
  rfl

/-- **The tangent Lie algebra of `GLₙ` is the matrix Lie algebra.** The underlying linear
equivalence evaluates tangent derivations on the generic coordinate entries, and the bracket on
matrices is the commutator. -/
noncomputable def tangentLieEquivMatrix :
    LieEquiv B
      (Derivation R (H (R := R) n)
        (Bialgebra.CounitAlgebra R (H (R := R) n) B))
      (Matrix (Fin n) (Fin n) B) where
  toFun := tangentMatrix n
  invFun := (tangentLinearEquivMatrix n).symm
  left_inv d := by
    rw [← tangentLinearEquivMatrix_apply]
    exact (tangentLinearEquivMatrix n).symm_apply_apply d
  right_inv X := by
    rw [← tangentLinearEquivMatrix_apply]
    exact (tangentLinearEquivMatrix n).apply_symm_apply X
  map_add' := map_add (tangentMatrix n)
  map_smul' b d := map_smul (tangentMatrix n) b d
  map_lie' := fun {d e} ↦ by
    exact tangentMatrix_lie n d e

@[simp]
theorem tangentLieEquivMatrix_apply (d : Derivation R (H (R := R) n)
    (Bialgebra.CounitAlgebra R (H (R := R) n) B)) :
    tangentLieEquivMatrix n d = tangentMatrix n d := by
  -- Expose the `toFun` field of the Lie equivalence once; its public computation rule is this
  -- theorem itself.
  change tangentMatrix n d = tangentMatrix n d
  rfl

end

end GeneralLinear

end TauCeti
