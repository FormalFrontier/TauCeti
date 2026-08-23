/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Determinant
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
* `TauCeti.GeneralLinear.trace_tangentMatrix`: the derivative of the determinant is matrix trace.
* `TauCeti.GeneralLinear.tangentLinearEquivMatrix`: the tangent space of `GLₙ` is linearly
  equivalent to `n × n` matrices.
* `TauCeti.GeneralLinear.tangentLieEquivMatrix`: the same equivalence as an equivalence of Lie
  algebras, carrying the tangent bracket to the matrix commutator.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§10, 14.
* The first-order determinant computation uses Mathlib's `Matrix.det_one_add_smul`.
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

/-- A dual-number matrix whose classical part is the identity has determinant with first-order
part equal to the trace of its infinitesimal part. -/
private theorem snd_det_eq_trace_of_fst_eq_one {C : Type*} [CommRing C] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) (DualNumber C))
    (hM : M.map fst = 1) :
    snd (Matrix.det M) = Matrix.trace (M.map snd) := by
  classical
  let X : Matrix (Fin n) (Fin n) C := M.map snd
  let X' : Matrix (Fin n) (Fin n) (DualNumber C) := X.map inl
  have hmatrix : M = 1 + (inr (1 : C) : DualNumber C) • X' := by
    apply Matrix.ext
    intro i j
    rw [← TrivSqZeroExt.inl_fst_add_inr_snd_eq (M i j)]
    have hMij := congr_fun (congr_fun hM i) j
    rw [Matrix.map_apply] at hMij
    rw [hMij]
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, X', X,
      Matrix.one_apply, apply_ite, inl_one, inl_zero, inr_mul_inl, op_smul_eq_smul, mul_one]
  calc
    snd (Matrix.det M) =
        snd (Matrix.det (1 + (inr (1 : C) : DualNumber C) • X')) := by rw [hmatrix]
    _ = Matrix.trace X := by
      rw [Matrix.det_one_add_smul]
      simp only [DualNumber.inr_eq_smul_eps, one_smul, DualNumber.eps_pow_two, mul_zero,
        add_zero, snd_add, snd_one, snd_mul, DualNumber.snd_eps, smul_eq_mul, mul_one,
        DualNumber.fst_eps, MulOpposite.op_zero, zero_smul, zero_add]
      simp only [Matrix.trace, Matrix.diag_apply]
      rw [fst_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp only [X', Matrix.map_apply, fst_inl]
    _ = Matrix.trace (M.map snd) := by simp only [X]

/-- **The differential of the determinant on `GLₙ` is matrix trace.** Evaluating a tangent
derivation on the generic determinant, then identifying its counit-valued coefficient with `B`,
equals the trace of its tangent matrix. -/
@[simp]
theorem trace_tangentMatrix (d : Derivation R (H (R := R) n)
    (Bialgebra.CounitAlgebra R (H (R := R) n) B)) :
    Matrix.trace (tangentMatrix n d) =
      d (determinantGroupLike R n : H (R := R) n) := by
  let q := derivationMulEquivTangentKer R (H (R := R) n) B (.ofAdd d)
  let M : Matrix (Fin n) (Fin n) (DualNumber (Bialgebra.CounitAlgebra R
      (H (R := R) n) B)) := (pointsMulEquiv (R := R) n q.val).val
  -- Compute the determinant of the dual-number point in the tangent kernel.
  have hdet : d (determinantGroupLike R n : H (R := R) n) =
      Matrix.trace (M.map snd) := by
    calc
      d (determinantGroupLike R n : H (R := R) n) =
          snd (q.val.ofConv (determinantGroupLike R n : H (R := R) n)) := by
        -- Unfold the local tangent point `q` before applying its public second-component rule.
        rw [show q = derivationMulEquivTangentKer R (H (R := R) n) B (.ofAdd d) from rfl]
        exact (derivationMulEquivTangentKer_apply_snd (.ofAdd d) _).symm
      _ = snd (Matrix.det M) := by
        rw [point_apply_determinantGroupLike, ← pointsMulEquiv_apply]
      _ = Matrix.trace (M.map snd) :=
        snd_det_eq_trace_of_fst_eq_one M (by
          apply Matrix.ext
          intro i j
          simp only [Matrix.map_apply, Matrix.one_apply, M, q]
          exact tangentPoint_matrix_fst n d i j)
  -- Transport the entrywise identity through the coefficient equivalence.
  rw [hdet]
  simp only [Matrix.trace, Matrix.diag_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [tangentMatrix_apply]
  simp only [Matrix.map_apply, M, q, tangentPoint_matrix_snd]
  exact Bialgebra.CounitAlgebra.algEquivSelf_apply R (H (R := R) n) B _

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
