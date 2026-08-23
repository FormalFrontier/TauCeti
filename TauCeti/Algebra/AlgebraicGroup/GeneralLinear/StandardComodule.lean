/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.FunctorOfPoints
public import TauCeti.Algebra.AlgebraicGroup.Representation.Faithful
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# The standard representation of the general linear group

The generic matrix defines a coaction of the coordinate Hopf algebra `O(GLₙ)` on the column
space `Rⁿ`: the `j`-th standard basis vector goes to the `j`-th column of the generic matrix.
This is the standard representation of `GLₙ`, and this file constructs it and establishes the
properties of it that the structure theory uses.

It is **faithful**: its coefficient matrix is the generic matrix, so its coordinate morphism
`O(GLₙ) ⟶ O(GLₙ)` is the identity, hence surjective, and the associated morphism of group
schemes is a closed immersion.

Over a field and for `n ≠ 0` it is **simple**: the only subcomodules of `kⁿ` are `0` and `kⁿ`.
Contracting the coaction of a vector of a subcomodule against the linear functional given by a
point of `GLₙ` valued in `k` shows that a subcomodule is stable under the action of every
invertible matrix, and `GL(n, k)` is transitive on nonzero vectors.

## Main declarations

* `TauCeti.GeneralLinear.standardComodule`: the standard comodule of `O(GLₙ)` on `Rⁿ`.
* `TauCeti.GeneralLinear.isFaithful_standardComodule`: the standard comodule is faithful.
* `TauCeti.GeneralLinear.piScalarRight_comp_endOfPoint`: a point acts on the standard comodule
  by the invertible matrix it names.
* `TauCeti.GeneralLinear.mulVec_mem`: a subcomodule of the standard comodule is stable under
  every invertible matrix.
* `TauCeti.GeneralLinear.instIsSimpleOrderSubcomodule`: over a field and in
  positive size, the standard comodule is simple.

## References

* J. S. Milne, *Algebraic Groups* (2017), §4.a and §5.
* J. C. Jantzen, *Representations of Algebraic Groups*, I.2.

Faithfulness and simplicity of the standard representation are the two representation-theoretic
inputs to the statement that `GLₙ` is reductive, which the ReductiveGroups roadmap asks for among
the worked examples accompanying Layer 6, "Reductive and semisimple groups". The remaining input
is that the invariants of a normal closed subgroup form a subrepresentation.

The construction of the comodule follows the template of
`TauCeti.Algebra.AlgebraicGroup.UpperUnitriangular.Unipotent`.
-/

public section

open Module WithConv
open scoped Matrix TensorProduct

namespace TauCeti.GeneralLinear

universe u

variable (R : Type u) [CommRing R] (n : ℕ)

/-- The standard coaction of `O(GLₙ)` on column vectors. On the `j`-th basis vector it is the
`j`-th column of the generic matrix. -/
noncomputable def standardCoact :
    (Fin n → R) →ₗ[R] (Fin n → R) ⊗[R] coordinateHopfAlgebra R n :=
  (Pi.basisFun R (Fin n)).constr R fun j ↦
    ∑ i, (Pi.single i (1 : R) : Fin n → R) ⊗ₜ[R]
      coordinateHopfAlgebraAlgEquiv R n (coordinateRingMap R n (MvPolynomial.X (i, j)))

/-- The standard coaction on a basis vector is the corresponding column of the generic
matrix. -/
@[simp]
theorem standardCoact_apply_basisFun (j : Fin n) :
    standardCoact R n (Pi.single j 1) =
      ∑ i, (Pi.single i (1 : R) : Fin n → R) ⊗ₜ[R]
        coordinateHopfAlgebraAlgEquiv R n (coordinateRingMap R n (MvPolynomial.X (i, j))) := by
  rw [standardCoact, ← Pi.basisFun_apply, Basis.constr_basis]

/-- The standard right comodule of the general linear coordinate Hopf algebra. -/
@[instance_reducible]
noncomputable def standardComodule :
    Comodule R (coordinateHopfAlgebra R n) (Fin n → R) where
  coact := standardCoact R n
  coassoc := by
    apply (Pi.basisFun R (Fin n)).ext
    intro j
    simp only [LinearMap.coe_comp, Function.comp_apply]
    rw [Pi.basisFun_apply, standardCoact_apply_basisFun]
    simp only [map_sum, LinearMap.rTensor_tmul, standardCoact_apply_basisFun,
      TensorProduct.sum_tmul, LinearEquiv.coe_coe, TensorProduct.assoc_tmul,
      LinearMap.lTensor_tmul, coordinateHopfAlgebra_comul_X, TensorProduct.tmul_sum]
    rw [Finset.sum_comm]
  lTensor_counit_comp_coact := by
    apply (Pi.basisFun R (Fin n)).ext
    intro j
    simp only [LinearMap.coe_comp, Function.comp_apply]
    rw [Pi.basisFun_apply, standardCoact_apply_basisFun]
    simp only [map_sum, LinearMap.lTensor_tmul, coordinateHopfAlgebra_counit_X]
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hij
      simp [hij]
    · simp

/-- The coaction of the standard comodule is `standardCoact`. -/
@[simp]
theorem standardComodule_coact :
    (standardComodule R n).coact = standardCoact R n :=
  (rfl)

attribute [local instance] standardComodule

/-- The coefficient matrix of the standard comodule is the generic matrix. -/
@[simp]
theorem coefficientMatrix_basisFun :
    Comodule.coefficientMatrix (C := coordinateHopfAlgebra R n)
        (Pi.basisFun R (Fin n)) = fun i j ↦
          coordinateHopfAlgebraAlgEquiv R n (coordinateRingMap R n (MvPolynomial.X (i, j))) := by
  ext i j
  rw [Comodule.coefficientMatrix_apply, Comodule.matrixCoefficient_def,
    standardComodule_coact, Pi.basisFun_apply, standardCoact_apply_basisFun]
  simp [Pi.single_apply]

/-- The coordinate morphism of the standard comodule is the identity of `O(GLₙ)`. -/
@[simp]
theorem coordinateBialgHom_basisFun :
    Comodule.coordinateBialgHom (H := coordinateHopfAlgebra R n)
        (Pi.basisFun R (Fin n)) = BialgHom.id R (coordinateHopfAlgebra R n) := by
  apply BialgHom.ext
  intro x
  have hAlg :
      (Comodule.coordinateBialgHom (H := coordinateHopfAlgebra R n)
          (Pi.basisFun R (Fin n))).toAlgHom =
        (BialgHom.id R (coordinateHopfAlgebra R n)).toAlgHom := by
    apply coordinateHopfAlgebra_algHom_ext
    intro i j
    calc
      _ = Comodule.coefficientMatrix (C := coordinateHopfAlgebra R n)
            (Pi.basisFun R (Fin n)) i j :=
        Comodule.coordinateBialgHom_X (Pi.basisFun R (Fin n)) i j
      _ = _ := by simp [coefficientMatrix_basisFun]
  exact DFunLike.congr_fun hAlg x

/-- **The standard comodule of `GLₙ` is faithful.** -/
theorem isFaithful_standardComodule :
    Comodule.IsFaithful (k := R) (H := coordinateHopfAlgebra R n) (V := Fin n → R) := by
  rw [Comodule.isFaithful_iff_isClosedImmersion_coordinateGroupSchemeHom
      (b := Pi.basisFun R (Fin n)),
    Comodule.isClosedImmersion_coordinateGroupSchemeHom_iff,
    coordinateBialgHom_basisFun]
  exact Function.surjective_id

/-- Contracting the standard coaction against a linear functional on `O(GLₙ)` multiplies by the
matrix of the functional's values on the generic entries. -/
theorem rid_lTensor_comp_standardCoact (f : coordinateHopfAlgebra R n →ₗ[R] R) :
    (TensorProduct.rid R (Fin n → R)).toLinearMap ∘ₗ
        LinearMap.lTensor (Fin n → R) f ∘ₗ standardCoact R n =
      Matrix.mulVecLin (Matrix.of fun i j ↦
        f (coordinateHopfAlgebraAlgEquiv R n
          (coordinateRingMap R n (MvPolynomial.X (i, j))))) := by
  apply (Pi.basisFun R (Fin n)).ext
  intro j
  simp only [LinearMap.coe_comp, Function.comp_apply, Pi.basisFun_apply,
    standardCoact_apply_basisFun, map_sum, LinearMap.lTensor_tmul,
    LinearEquiv.coe_coe, TensorProduct.rid_tmul]
  ext i
  simp [Matrix.mulVec, dotProduct, Pi.single_apply, Finset.sum_ite_eq']

/-- **A subcomodule of the standard comodule of `GLₙ` is stable under every invertible
matrix.** -/
theorem mulVec_mem (N : Subcomodule R (coordinateHopfAlgebra R n) (Fin n → R))
    (g : Matrix.GeneralLinearGroup (Fin n) R) {w : Fin n → R} (hw : w ∈ N) :
    (g : Matrix (Fin n) (Fin n) R) *ᵥ w ∈ N := by
  have h := N.rid_lTensor_coact_mem
    (generalLinearToPoint (R := R) n g).ofConv.toLinearMap hw
  rw [standardComodule_coact R n] at h
  have hf := DFunLike.congr_fun
    (rid_lTensor_comp_standardCoact R n (generalLinearToPoint (R := R) n g).ofConv.toLinearMap) w
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe] at hf
  have hmat : (Matrix.of fun i j ↦ (generalLinearToPoint (R := R) n g).ofConv.toLinearMap
        (coordinateHopfAlgebraAlgEquiv R n
          (coordinateRingMap R n (MvPolynomial.X (i, j))))) =
      (g : Matrix (Fin n) (Fin n) R) := by
    ext i j
    simp
  rw [hf, hmat, Matrix.mulVecLin_apply] at h
  exact h

section PointAction

variable {A : Type*} [CommRing A] [Algebra R A]

/-- Under the canonical scalar-extension identification `A ⊗[R] Rⁿ ≃ Aⁿ`, a point of `GLₙ` acts
on the standard comodule by multiplication with the invertible matrix it names. -/
theorem piScalarRight_comp_endOfPoint (g : WithConv (coordinateHopfAlgebra R n →ₐ[R] A)) :
    (TensorProduct.piScalarRight R A A (Fin n)).toLinearMap.comp
        (Comodule.endOfPoint (Fin n → R) g.ofConv) =
      (Matrix.GeneralLinearGroup.toLin (pointToGeneralLinear n g) :
          (Fin n → A) →ₗ[A] Fin n → A).comp
        (TensorProduct.piScalarRight R A A (Fin n)).toLinearMap := by
  apply ((Pi.basisFun R (Fin n)).baseChange A).ext
  intro j
  simp only [LinearMap.comp_apply, Module.Basis.baseChange_apply]
  rw [Comodule.endOfPoint_tmul, standardComodule_coact, Pi.basisFun_apply,
    standardCoact_apply_basisFun]
  simp only [map_sum, LinearMap.lTensor_tmul, AlgHom.toLinearMap_apply,
    TensorProduct.comm_tmul, one_smul, Matrix.GeneralLinearGroup.toLin_apply,
    Matrix.mulVecLin_apply]
  ext i
  simp only [Finset.sum_apply, Matrix.mulVec, dotProduct]
  simp [TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul,
    Pi.single_apply, pointToGeneralLinear_apply]

end PointAction

section Simple

variable (k : Type u) [Field k] (m : ℕ) [NeZero m]

omit [NeZero m] in
/-- Every nonzero vector of `kᵐ` is the image of every other one under an invertible matrix. -/
private theorem exists_generalLinearGroup_mulVec {v w : Fin m → k} (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ g : Matrix.GeneralLinearGroup (Fin m) k, (g : Matrix (Fin m) (Fin m) k) *ᵥ w = v := by
  let e : (k ∙ w) ≃ₗ[k] (k ∙ v) :=
    (LinearEquiv.toSpanNonzeroSingleton k (Fin m → k) w hw).symm.trans
      (LinearEquiv.toSpanNonzeroSingleton k (Fin m → k) v hv)
  obtain ⟨φ, hφ⟩ := Submodule.exists_linearEquiv_restrict_eq e
  have hφw : φ w = v := by
    have hone := hφ ⟨w, Submodule.mem_span_singleton_self w⟩
    have he : e ⟨w, Submodule.mem_span_singleton_self w⟩ =
        ⟨v, Submodule.mem_span_singleton_self v⟩ := by
      simp only [e, LinearEquiv.trans_apply]
      have hw_coord :
          (LinearEquiv.toSpanNonzeroSingleton k (Fin m → k) w hw).symm
              ⟨w, Submodule.mem_span_singleton_self w⟩ = 1 :=
        LinearEquiv.coord_self k (Fin m → k) w hw
      rw [hw_coord]
      exact LinearEquiv.toSpanNonzeroSingleton_one k (Fin m → k) v hv
    rw [he] at hone
    exact hone.symm
  refine ⟨⟨LinearMap.toMatrix' (φ : (Fin m → k) →ₗ[k] Fin m → k),
    LinearMap.toMatrix' (φ.symm : (Fin m → k) →ₗ[k] Fin m → k), ?_, ?_⟩, ?_⟩
  · rw [← LinearMap.toMatrix'_comp]
    simp
  · rw [← LinearMap.toMatrix'_comp]
    simp
  · rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
    exact hφw

/-- **The standard comodule of `GLₘ` over a field is simple** for `m ≠ 0`: its only subcomodules
are the zero comodule and the whole column space. -/
instance instIsSimpleOrderSubcomodule :
    IsSimpleOrder (Subcomodule k (coordinateHopfAlgebra k m) (Fin m → k)) where
  exists_pair_ne := by
    refine ⟨⊥, ⊤, fun h ↦ ?_⟩
    have hone : (Pi.single (0 : Fin m) (1 : k) : Fin m → k) ∈
        (⊥ : Subcomodule k (coordinateHopfAlgebra k m) (Fin m → k)) :=
      h ▸ Subcomodule.mem_top _
    rw [Subcomodule.mem_bot] at hone
    simpa using congrFun hone (0 : Fin m)
  eq_bot_or_eq_top N := by
    by_cases hN : ∀ w ∈ N, w = 0
    · left
      exact Subcomodule.ext fun w ↦ ⟨fun hw ↦ Subcomodule.mem_bot.mpr (hN w hw),
        fun hw ↦ Subcomodule.mem_bot.mp hw ▸ zero_mem N⟩
    · right
      simp only [not_forall] at hN
      obtain ⟨w, hwN, hw⟩ := hN
      refine Subcomodule.ext fun v ↦ ⟨fun _ ↦ Subcomodule.mem_top v, fun _ ↦ ?_⟩
      by_cases hv : v = 0
      · exact hv ▸ zero_mem N
      · obtain ⟨g, hg⟩ := exists_generalLinearGroup_mulVec k m hv hw
        exact hg ▸ mulVec_mem k m N g hwN

end Simple

end TauCeti.GeneralLinear
