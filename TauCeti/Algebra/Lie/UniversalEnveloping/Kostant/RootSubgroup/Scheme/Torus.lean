/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.Embedding
public import TauCeti.Algebra.AlgebraicGroup.Representation.Comodule.Basic
public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.Scheme
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Torus

import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.PointAction

/-!
# The Kostant split torus as a group-scheme morphism

A weight basis `b : Basis (Fin n) ℤ M` of a Kostant-stable lattice and its weight function
`wt : Fin n → κ → ℤ` give, over every commutative ring `A`, the diagonal action

```text
𝔾ₘ^κ(A) → GL(A ⊗[ℤ] M),
s ↦ diag(χ_(wt i)(s)).
```

This file proves that the value-ring actions constructed in
`Kostant/RootSubgroup/Torus.lean` are represented by a group-scheme morphism
`𝔾ₘ^κ → GLₙ` over `ℤ`. It first packages their naturality as a point representation,
recovers the corresponding monoid-algebra comodule, and applies the coordinate-morphism
construction for finite free comodules. The final point comparison shows that the represented
morphism acts by the original diagonal matrices.

This supplies the split-torus part of the pinning required by Layer 9 of the ReductiveGroups
roadmap. It does not assert that the torus is maximal in the generated Chevalley group scheme;
that identification belongs to the later pinning assembly.

## Main declarations

* `TauCeti.UniversalEnvelopingAlgebra.kostantTorusPointRepresentation`: the natural action of the
  split torus on the scalar extensions of the lattice.
* `TauCeti.UniversalEnvelopingAlgebra.kostantTorusComodule`: its coordinate-side comodule.
* `TauCeti.UniversalEnvelopingAlgebra.kostantTorusCoordinateMap`: the coordinate Hopf-algebra
  morphism `O(GLₙ) → O(𝔾ₘ^κ)`.
* `TauCeti.UniversalEnvelopingAlgebra.kostantTorusGroupSchemeMap`: the represented morphism
  `𝔾ₘ^κ → GLₙ`.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §§7.1--7.2.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

open AlgebraicGeometry CategoryTheory TensorProduct WithConv
open scoped CategoryTheory.MonObj

namespace TauCeti.UniversalEnvelopingAlgebra

-- Match tensor products to the `ℤ`-algebra structure used by scalar extension.
attribute [local instance high] Algebra.toModule
-- Public declarations only require finiteness; choose a `Fintype` internally for finite products.
attribute [local instance] Fintype.ofFinite

variable {κ : Type} [Finite κ]
variable (M : Type) [AddCommGroup M]
variable {n : ℕ} (b : Module.Basis (Fin n) ℤ M) (wt : Fin n → κ → ℤ)

/-- The diagonal torus action associated to a weighted basis after scalar extension. -/
noncomputable def weightedBasisTorusPoints (A : Type*) [CommRing A] [Algebra ℤ A] :
    (κ → Aˣ) →* LinearMap.GeneralLinearGroup A (A ⊗[ℤ] M) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv A (A ⊗[ℤ] M)).symm.toMonoidHom.comp
    (basisWeightTorus (b.baseChange A) wt)

@[simp]
private theorem weightedBasisTorusPoints_tmul_basis
    (A : Type*) [CommRing A] [Algebra ℤ A] (s : κ → Aˣ) (a : A) (i : Fin n) :
    (weightedBasisTorusPoints M b wt A s).val (a ⊗ₜ[ℤ] b i) =
      ((torusCharacter s (wt i) : A) * a) ⊗ₜ[ℤ] b i := by
  rw [weightedBasisTorusPoints]
  change basisWeightTorus (b.baseChange A) wt s (a ⊗ₜ[ℤ] b i) = _
  rw [show a ⊗ₜ[ℤ] b i = a • b.baseChange A i by
    rw [Module.Basis.baseChange_apply, smul_tmul', smul_eq_mul, mul_one],
    map_smul, basisWeightTorus_basis, smul_smul, mul_comm,
    Module.Basis.baseChange_apply, smul_tmul', smul_eq_mul, mul_one]

/-- On a Kostant lattice, the abstract weighted-basis action is the previously constructed
Kostant torus action. -/
theorem weightedBasisTorusPoints_eq_kostantTorusPoints
    {V : Type} [AddCommGroup V] (M : AddSubgroup V)
    {n : ℕ} (b : Module.Basis (Fin n) ℤ M) (wt : Fin n → κ → ℤ)
    (A : Type*) [CommRing A] [Algebra ℤ A] :
    weightedBasisTorusPoints M b wt A = kostantTorusPoints M b wt A := by
  apply MonoidHom.ext
  intro s
  apply Units.ext
  apply Module.Basis.ext (b.baseChange A)
  intro i
  rw [Module.Basis.baseChange_apply, weightedBasisTorusPoints_tmul_basis,
    kostantTorusPoints_tmul_basis]

private theorem map_weightedBasisTorusPoints
    {A B : Type*} [CommRing A] [CommRing B] [Algebra ℤ A] [Algebra ℤ B]
    (φ : A →ₐ[ℤ] B) (s : κ → Aˣ) (z : A ⊗[ℤ] M) :
    TensorProduct.map φ.toLinearMap LinearMap.id
        ((weightedBasisTorusPoints M b wt A s).val z) =
      (weightedBasisTorusPoints M b wt B fun j ↦ Units.map φ.toMonoidHom (s j)).val
        (TensorProduct.map φ.toLinearMap LinearMap.id z) := by
  let this : TensorProduct.CompatibleSMul ℤ ℤ A M :=
    ⟨fun z a m ↦ by
      change ((inferInstance : Module ℤ A).smul z a) ⊗ₜ[ℤ] m = a ⊗ₜ[ℤ] (z • m)
      rw [int_smul_eq_zsmul (inferInstance : Module ℤ A)]
      exact TensorProduct.CompatibleSMul.int.smul_tmul z a m⟩
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add y z hy hz => simp only [map_add, hy, hz]
  | tmul a m =>
      conv_lhs => rw [← b.linearCombination_repr m]
      conv_rhs => rw [← b.linearCombination_repr m]
      rw [Finsupp.linearCombination_apply, Finsupp.sum, TensorProduct.tmul_sum]
      simp only [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← this.smul_tmul, weightedBasisTorusPoints_tmul_basis,
        TensorProduct.map_tmul, TensorProduct.map_tmul]
      simp only [LinearMap.id_coe, id_eq]
      rw [weightedBasisTorusPoints_tmul_basis]
      simp only [AlgHom.toLinearMap_apply, map_mul]
      have hchar :
          φ (torusCharacter s (wt i) : A) =
            (torusCharacter (fun j ↦ Units.map φ.toMonoidHom (s j)) (wt i) : B) :=
        congrArg Units.val (map_torusCharacter φ.toRingHom s (wt i))
      rw [hchar]

private noncomputable def kostantTorusPointAction (A : CommAlgCat ℤ) :
    HopfAlgebra.points
        (R := ℤ) (H := MonoidAlgebra ℤ (Multiplicative (κ →₀ ℤ))) A ⟶
      GeneralLinear.scalarExtensionAutomorphisms (V := M) A :=
  GrpCat.ofHom <| (weightedBasisTorusPoints M b wt A).comp
    (SplitTorus.pointsMulEquiv (R := ℤ) (A := A) (σ := κ)).toMonoidHom

@[simp]
private theorem kostantTorusPointAction_val (A : CommAlgCat ℤ)
    (f : HopfAlgebra.points
      (R := ℤ) (H := MonoidAlgebra ℤ (Multiplicative (κ →₀ ℤ))) A) :
    (kostantTorusPointAction M b wt A f).val =
      (weightedBasisTorusPoints M b wt A (SplitTorus.pointsMulEquiv f)).val := by
  rfl

private theorem kostantTorusPointAction_naturality
    {A B : CommAlgCat ℤ} (φ : A ⟶ B)
    (f : HopfAlgebra.points
      (R := ℤ) (H := MonoidAlgebra ℤ (Multiplicative (κ →₀ ℤ))) A) :
    GeneralLinear.mapScalarExtensionAutomorphisms (V := M) φ
        (kostantTorusPointAction M b wt A f) =
      kostantTorusPointAction M b wt B
        (HopfAlgebra.mapPoints
          (H := MonoidAlgebra ℤ (Multiplicative (κ →₀ ℤ))) φ f) := by
  symm
  apply GeneralLinear.eq_mapScalarExtensionAutomorphisms_of_apply_scalarExtensionMap_eq
    (V := M) φ
  intro z
  rw [GeneralLinear.scalarExtensionMap_eq_map,
    kostantTorusPointAction_val, kostantTorusPointAction_val]
  have hs :
      SplitTorus.pointsMulEquiv
          (HopfAlgebra.mapPoints
            (H := MonoidAlgebra ℤ (Multiplicative (κ →₀ ℤ))) φ f) =
        fun j => Units.map φ.hom.toMonoidHom (SplitTorus.pointsMulEquiv f j) := by
    funext j
    exact SplitTorus.pointsMulEquiv_mapValue φ.hom f j
  rw [hs]
  exact (map_weightedBasisTorusPoints M b wt φ.hom
    (SplitTorus.pointsMulEquiv f) z).symm

/-- The natural point representation of the split torus on a finite free `ℤ`-module written in
a weight basis.

At a value ring `A`, a point is read as a family `s : κ → Aˣ`, and the action is the diagonal
automorphism whose `i`-th entry is the value at `s` of the weight `wt i`. -/
noncomputable def kostantTorusPointRepresentation :
    HopfAlgebra.PointRepresentation
      (R := ℤ) (H := MonoidAlgebra ℤ (Multiplicative (κ →₀ ℤ))) (V := M) where
  app A := kostantTorusPointAction M b wt A ≫
    eqToHom (GeneralLinear.scalarExtensionAutomorphismsFunctor_obj (V := M) A).symm
  naturality A B φ := by
    -- Expose the functor components and their equality transports in the naturality square.
    change
      HopfAlgebra.mapPoints
          (H := MonoidAlgebra ℤ (Multiplicative (κ →₀ ℤ))) φ ≫
          kostantTorusPointAction M b wt B ≫
          eqToHom
            (GeneralLinear.scalarExtensionAutomorphismsFunctor_obj (V := M) B).symm =
        kostantTorusPointAction M b wt A ≫
          eqToHom
            (GeneralLinear.scalarExtensionAutomorphismsFunctor_obj (V := M) A).symm ≫
          (GeneralLinear.scalarExtensionAutomorphismsFunctor (V := M)).map φ
    have hraw :
        HopfAlgebra.mapPoints
            (H := MonoidAlgebra ℤ (Multiplicative (κ →₀ ℤ))) φ ≫
            kostantTorusPointAction M b wt B =
          kostantTorusPointAction M b wt A ≫
            GeneralLinear.mapScalarExtensionAutomorphisms (V := M) φ := by
      apply GrpCat.ext
      intro f
      exact (kostantTorusPointAction_naturality M b wt φ f).symm
    rw [GeneralLinear.scalarExtensionAutomorphismsFunctor_map]
    rw [← Category.assoc, hraw]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

/-- At every categorical value ring, the represented point action is the weighted-basis diagonal
action after reading a split-torus point as its family of coordinates. -/
@[simp]
theorem kostantTorusPointRepresentation_action (A : CommAlgCat ℤ) :
    (kostantTorusPointRepresentation M b wt).action A =
      GrpCat.ofHom ((weightedBasisTorusPoints M b wt A).comp
        (SplitTorus.pointsMulEquiv (R := ℤ) (A := A) (σ := κ)).toMonoidHom) := by
  rw [HopfAlgebra.PointRepresentation.action_def]
  dsimp only [kostantTorusPointRepresentation]
  -- The source point functor is definitionally, but not reducibly, equal to `HopfAlgebra.points`.
  change
    (kostantTorusPointAction M b wt A ≫
        eqToHom (GeneralLinear.scalarExtensionAutomorphismsFunctor_obj (V := M) A).symm) ≫
      eqToHom (GeneralLinear.scalarExtensionAutomorphismsFunctor_obj (V := M) A) =
        GrpCat.ofHom ((weightedBasisTorusPoints M b wt A).comp
          (SplitTorus.pointsMulEquiv (R := ℤ) (A := A) (σ := κ)).toMonoidHom)
  rw [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
  rfl

/-- The coordinate-side comodule recovered from the natural weighted-basis split-torus action. -/
@[irreducible]
noncomputable def kostantTorusComodule :
    Comodule ℤ (MonoidAlgebra ℤ (Multiplicative (κ →₀ ℤ))) M :=
  HopfAlgebra.PointRepresentation.toComodule (kostantTorusPointRepresentation M b wt)

/-- The Kostant torus coaction is internally recovered from the universal point action. -/
theorem kostantTorusComodule_coact_apply (x : M) :
    (kostantTorusComodule M b wt).coact x =
      TensorProduct.comm ℤ (MonoidAlgebra ℤ (Multiplicative (κ →₀ ℤ))) M
        (TensorProduct.map ULift.algEquiv.toLinearMap LinearMap.id
          (((kostantTorusPointRepresentation M b wt).action
            (CommAlgCat.of ℤ
              (ULift.{max 0 0} (MonoidAlgebra ℤ (Multiplicative (κ →₀ ℤ)))))
            (toConv ULift.algEquiv.symm.toAlgHom)).val (1 ⊗ₜ[ℤ] x))) := by
  unfold kostantTorusComodule
  exact HopfAlgebra.PointRepresentation.toComodule_coact_apply _ x

private theorem torusCharacter_pointsMulEquiv
    {A : Type*} [CommRing A] [Algebra ℤ A]
    (f : WithConv (MonoidAlgebra ℤ (Multiplicative (κ →₀ ℤ)) →ₐ[ℤ] A))
    (mu : κ → ℤ) :
    (torusCharacter (SplitTorus.pointsMulEquiv f) mu : A) =
      f.ofConv (MonoidAlgebra.single
        (Multiplicative.ofAdd (Finsupp.equivFunOnFinite.symm mu)) 1) := by
  let χ := DiagonalizableGroup.charOfPoint f.ofConv
  have hs : SplitTorus.pointsMulEquiv f = freeAbelianCharEquiv χ := by
    funext i
    apply Units.ext
    rw [SplitTorus.pointsMulEquiv_apply_coe, freeAbelianCharEquiv_apply,
      DiagonalizableGroup.charOfPoint_apply_coe]
  have hunit : torusCharacter (freeAbelianCharEquiv χ) mu =
      χ (Multiplicative.ofAdd (Finsupp.equivFunOnFinite.symm mu)) := by
    let m := Finsupp.equivFunOnFinite.symm mu
    calc
      torusCharacter (freeAbelianCharEquiv χ) mu =
          torusCharacter (freeAbelianCharEquiv χ) (Finsupp.equivFunOnFinite m) := by
            rw [Finsupp.equivFunOnFinite.apply_symm_apply]
      _ = m.prod fun i z ↦ freeAbelianCharEquiv χ i ^ z :=
        torusCharacter_equivFunOnFinite _ _
      _ = (freeAbelianCharEquiv).symm (freeAbelianCharEquiv χ)
          (Multiplicative.ofAdd m) := by
            rw [freeAbelianCharEquiv_symm_apply_ofAdd]
      _ = χ (Multiplicative.ofAdd m) := by rw [MulEquiv.symm_apply_apply]
  rw [hs]
  exact (congrArg Units.val hunit).trans
    (DiagonalizableGroup.charOfPoint_apply_coe f.ofConv _)

/-- A weight-basis vector coacts by its weight monomial. -/
@[simp]
theorem kostantTorusComodule_coact_basis (i : Fin n) :
    (kostantTorusComodule M b wt).coact (b i) =
      b i ⊗ₜ[ℤ] MonoidAlgebra.single
        (Multiplicative.ofAdd (Finsupp.equivFunOnFinite.symm (wt i))) 1 := by
  unfold kostantTorusComodule
  rw [HopfAlgebra.PointRepresentation.toComodule_coact_apply,
    kostantTorusPointRepresentation_action]
  change
    TensorProduct.comm ℤ (MonoidAlgebra ℤ (Multiplicative (κ →₀ ℤ))) M
      (TensorProduct.map ULift.algEquiv.toLinearMap LinearMap.id
        ((weightedBasisTorusPoints M b wt
            (ULift (MonoidAlgebra ℤ (Multiplicative (κ →₀ ℤ))))
            (SplitTorus.pointsMulEquiv (toConv ULift.algEquiv.symm.toAlgHom))).val
          (1 ⊗ₜ[ℤ] b i))) = _
  rw [weightedBasisTorusPoints_tmul_basis]
  simp only [mul_one, TensorProduct.map_tmul, LinearMap.id_apply,
    TensorProduct.comm_tmul, AlgEquiv.toLinearMap_apply]
  rw [torusCharacter_pointsMulEquiv]
  simp

/-- The matrix-valued split-torus action in the base-changed weight basis. -/
noncomputable def kostantTorusMatrix (A : Type*) [CommRing A] :
    (κ → Aˣ) →* Matrix.GeneralLinearGroup (Fin n) A :=
  (Units.map (LinearMap.toMatrixAlgEquiv (b.baseChange A)).toMonoidHom).comp
    (weightedBasisTorusPoints M b wt A)

/-- The torus matrix is diagonal, with the weight character in its `i`-th diagonal entry. -/
@[simp]
theorem kostantTorusMatrix_apply (A : Type*) [CommRing A] (s : κ → Aˣ) (r i : Fin n) :
    kostantTorusMatrix M b wt A s r i =
      if r = i then (torusCharacter s (wt i) : A) else 0 := by
  rw [kostantTorusMatrix, MonoidHom.comp_apply, Units.coe_map]
  change LinearMap.toMatrix (b.baseChange A) (b.baseChange A)
    (weightedBasisTorusPoints M b wt A s).val r i = _
  rw [LinearMap.toMatrix_apply]
  change (b.baseChange A).repr
    ((weightedBasisTorusPoints M b wt A s).val (b.baseChange A i)) r = _
  rw [Module.Basis.baseChange_apply, weightedBasisTorusPoints_tmul_basis,
    Module.Basis.baseChange_repr_tmul, b.repr_self]
  by_cases h : r = i
  · subst r
    simp
  · simp [h]

/-- The `i`-th diagonal entry is the character attached to the `i`-th weight. -/
theorem kostantTorusMatrix_apply_self (A : Type*) [CommRing A] (s : κ → Aˣ) (i : Fin n) :
    kostantTorusMatrix M b wt A s i i = (torusCharacter s (wt i) : A) := by
  simp

/-- Every off-diagonal entry of the weighted-basis torus matrix vanishes. -/
theorem kostantTorusMatrix_apply_of_ne (A : Type*) [CommRing A] (s : κ → Aˣ)
    {r i : Fin n} (h : r ≠ i) :
    kostantTorusMatrix M b wt A s r i = 0 := by
  simp [h]

/-- The coordinate Hopf-algebra morphism of the split torus action in the weight basis `b`. -/
noncomputable def kostantTorusCoordinateMap :
    GeneralLinear.coordinateHopfAlgebra ℤ n ⟶
      (DiagonalizableGroup.coordinateRing ℤ (SplitTorus.characterGroup κ)).obj := by
  let : Comodule ℤ (MonoidAlgebra ℤ (Multiplicative (κ →₀ ℤ))) M :=
    kostantTorusComodule M b wt
  exact CommHopfAlgCat.ofHom (Comodule.coordinateBialgHom b)

/-- A generic matrix coordinate pulls back to the corresponding diagonal weight monomial. -/
@[simp]
theorem kostantTorusCoordinateMap_X (r i : Fin n) :
    (kostantTorusCoordinateMap M b wt).hom
        (GeneralLinear.coordinateHopfAlgebraAlgEquiv ℤ n
          (GeneralLinear.coordinateRingMap ℤ n (MvPolynomial.X (r, i)))) =
      if r = i then
        MonoidAlgebra.single
          (Multiplicative.ofAdd (Finsupp.equivFunOnFinite.symm (wt i))) 1
      else 0 := by
  let : Comodule ℤ (MonoidAlgebra ℤ (Multiplicative (κ →₀ ℤ))) M :=
    kostantTorusComodule M b wt
  rw [kostantTorusCoordinateMap]
  change Comodule.coordinateBialgHom b
      (GeneralLinear.coordinateHopfAlgebraAlgEquiv ℤ n
        (GeneralLinear.coordinateRingMap ℤ n (MvPolynomial.X (r, i)))) = _
  rw [Comodule.coordinateBialgHom_X, Comodule.coefficientMatrix_apply,
    Comodule.matrixCoefficient_def, kostantTorusComodule_coact_basis]
  by_cases h : r = i
  · subst r
    simp [Module.Basis.coord_apply]
  · simp [Module.Basis.coord_apply, h]

/-- A diagonal matrix coordinate pulls back to the corresponding weight monomial. -/
@[simp]
theorem kostantTorusCoordinateMap_X_self (i : Fin n) :
    (kostantTorusCoordinateMap M b wt).hom
        (GeneralLinear.coordinateHopfAlgebraAlgEquiv ℤ n
          (GeneralLinear.coordinateRingMap ℤ n (MvPolynomial.X (i, i)))) =
      MonoidAlgebra.single
        (Multiplicative.ofAdd (Finsupp.equivFunOnFinite.symm (wt i))) 1 := by
  simpa using kostantTorusCoordinateMap_X M b wt i i

/-- Every off-diagonal matrix coordinate pulls back to zero. -/
@[simp]
theorem kostantTorusCoordinateMap_X_of_ne {r i : Fin n} (h : r ≠ i) :
    (kostantTorusCoordinateMap M b wt).hom
        (GeneralLinear.coordinateHopfAlgebraAlgEquiv ℤ n
          (GeneralLinear.coordinateRingMap ℤ n (MvPolynomial.X (r, i)))) = 0 := by
  simpa [h] using kostantTorusCoordinateMap_X M b wt r i

/-- The split torus of a Kostant weight basis as a group-scheme morphism `𝔾ₘ^κ → GLₙ` over
`ℤ`. -/
noncomputable def kostantTorusGroupSchemeMap :
    SplitTorus.groupScheme ℤ κ ⟶ GeneralLinear.groupScheme ℤ n := by
  let : Comodule ℤ (MonoidAlgebra ℤ (Multiplicative (κ →₀ ℤ))) M :=
    kostantTorusComodule M b wt
  exact eqToHom (DiagonalizableGroup.groupScheme_def ℤ (SplitTorus.characterGroup κ)) ≫
    Comodule.coordinateGroupSchemeHom b

/-- The Kostant torus morphism is relative spectrum applied contravariantly to its coordinate
Hopf-algebra morphism. -/
theorem kostantTorusGroupSchemeMap_def :
    kostantTorusGroupSchemeMap M b wt =
      eqToHom (DiagonalizableGroup.groupScheme_def ℤ (SplitTorus.characterGroup κ)) ≫
        (AlgebraicGeometry.hopfSpec (CommRingCat.of ℤ)).map
          (kostantTorusCoordinateMap M b wt).op ≫
        eqToHom (GeneralLinear.groupScheme_def ℤ n).symm := by
  let : Comodule ℤ (MonoidAlgebra ℤ (Multiplicative (κ →₀ ℤ))) M :=
    kostantTorusComodule M b wt
  rw [kostantTorusGroupSchemeMap, Comodule.coordinateGroupSchemeHom_def]
  rfl

section Points

variable (A : Type) [CommRing A]

/-- On algebra-valued points, precomposition with the torus coordinate morphism gives the
diagonal matrix defined by the original weight-basis action. -/
@[simp]
theorem pointsMulEquiv_kostantTorusCoordinateMap
    (f : WithConv (MonoidAlgebra ℤ (Multiplicative (κ →₀ ℤ)) →ₐ[ℤ] A)) :
    GeneralLinear.pointToGeneralLinear n
        (toConv (f.ofConv.comp (kostantTorusCoordinateMap M b wt).hom)) =
      kostantTorusMatrix M b wt A (SplitTorus.pointsMulEquiv f) := by
  apply Matrix.GeneralLinearGroup.ext
  intro r i
  rw [GeneralLinear.pointToGeneralLinear_apply, ofConv_toConv, AlgHom.comp_apply]
  -- Expose the coordinate-map application hidden by bundled algebra-map coercions.
  change f.ofConv
      ((kostantTorusCoordinateMap M b wt).hom
        (GeneralLinear.coordinateHopfAlgebraAlgEquiv ℤ n
          (GeneralLinear.coordinateRingMap ℤ n (MvPolynomial.X (r, i))))) = _
  rw [kostantTorusCoordinateMap_X, kostantTorusMatrix_apply]
  by_cases h : r = i
  · subst r
    simp only [↓reduceIte]
    exact (torusCharacter_pointsMulEquiv f (wt i)).symm
  · simp [h]

private theorem groupSchemePointsMulEquiv_comp_kostantTorusGroupSchemeMap
    (f : WithConv (MonoidAlgebra ℤ (Multiplicative (κ →₀ ℤ)) →ₐ[ℤ] A)) :
    CommHopfAlgCat.mapMulEquivOfPresentation
        (DiagonalizableGroup.coordinateRing ℤ (SplitTorus.characterGroup κ)).obj A
        (DiagonalizableGroup.groupScheme_def ℤ (SplitTorus.characterGroup κ)) f ≫
        (kostantTorusGroupSchemeMap M b wt).hom.hom =
      GeneralLinear.groupSchemePointMulEquiv n A
        ((CommHopfAlgCat.mapPointsFunctor (kostantTorusCoordinateMap M b wt)).app
          (CommAlgCat.of ℤ A) f) := by
  rw [kostantTorusGroupSchemeMap_def]
  exact CommHopfAlgCat.pointMulEquivOfPresentation_mapDomain
    (R := ℤ) A (GeneralLinear.groupScheme_def ℤ n)
      (DiagonalizableGroup.groupScheme_def ℤ (SplitTorus.characterGroup κ))
      (GeneralLinear.groupSchemePointMulEquiv n A)
      (CommHopfAlgCat.mapMulEquivOfPresentation
        (DiagonalizableGroup.coordinateRing ℤ (SplitTorus.characterGroup κ)).obj A
        (DiagonalizableGroup.groupScheme_def ℤ (SplitTorus.characterGroup κ)))
      (GeneralLinear.groupSchemePointMulEquiv_apply_left n A)
      (CommHopfAlgCat.mapMulEquivOfPresentation_apply_left
        (DiagonalizableGroup.coordinateRing ℤ (SplitTorus.characterGroup κ)).obj A
        (DiagonalizableGroup.groupScheme_def ℤ (SplitTorus.characterGroup κ))
        (DiagonalizableGroup.groupScheme_X_left ℤ (SplitTorus.characterGroup κ)))
      (kostantTorusCoordinateMap M b wt) f

private theorem diagonalizableGroupSchemePointsMulEquiv_mapMulEquivOfPresentation
    (f : WithConv (MonoidAlgebra ℤ (Multiplicative (κ →₀ ℤ)) →ₐ[ℤ] A)) :
    DiagonalizableGroup.groupSchemePointsMulEquiv
        (R := ℤ) (A := A) (SplitTorus.characterGroup κ)
        (CommHopfAlgCat.mapMulEquivOfPresentation
          (DiagonalizableGroup.coordinateRing ℤ (SplitTorus.characterGroup κ)).obj A
          (DiagonalizableGroup.groupScheme_def ℤ (SplitTorus.characterGroup κ)) f) = f := by
  let p := CommHopfAlgCat.mapMulEquivOfPresentation
    (DiagonalizableGroup.coordinateRing ℤ (SplitTorus.characterGroup κ)).obj A
    (DiagonalizableGroup.groupScheme_def ℤ (SplitTorus.characterGroup κ)) f
  have hp := DiagonalizableGroup.groupSchemePointsMulEquiv_apply_left_comp
    (R := ℤ) (A := A) (SplitTorus.characterGroup κ) p
  dsimp only [p] at hp
  rw [CommHopfAlgCat.mapMulEquivOfPresentation_apply_left
    (DiagonalizableGroup.coordinateRing ℤ (SplitTorus.characterGroup κ)).obj A
    (DiagonalizableGroup.groupScheme_def ℤ (SplitTorus.characterGroup κ))
    (DiagonalizableGroup.groupScheme_X_left ℤ (SplitTorus.characterGroup κ))] at hp
  apply AlgebraicGeometry.Spec.mapMulEquiv.injective
  apply Over.OverMorphism.ext
  rw [← hp]
  -- Expose the underlying scheme maps hidden by the `Over` morphism coercions.
  change (Spec.map (CommRingCat.ofHom f.ofConv.toRingHom) ≫
      eqToHom (DiagonalizableGroup.groupScheme_X_left ℤ
        (SplitTorus.characterGroup κ)).symm) ≫
      eqToHom (DiagonalizableGroup.groupScheme_X_left ℤ
        (SplitTorus.characterGroup κ)) =
    Spec.map (CommRingCat.ofHom f.ofConv.toRingHom)
  rw [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]

private theorem splitTorus_schemePointsMulEquiv_mapMulEquivOfPresentation
    (f : WithConv (MonoidAlgebra ℤ (Multiplicative (κ →₀ ℤ)) →ₐ[ℤ] A)) :
    SplitTorus.schemePointsMulEquiv (R := ℤ) (A := A)
        (CommHopfAlgCat.mapMulEquivOfPresentation
          (DiagonalizableGroup.coordinateRing ℤ (SplitTorus.characterGroup κ)).obj A
          (DiagonalizableGroup.groupScheme_def ℤ (SplitTorus.characterGroup κ)) f) =
      SplitTorus.pointsMulEquiv f := by
  funext i
  apply Units.ext
  rw [SplitTorus.schemePointsMulEquiv_apply_coe, SplitTorus.pointsMulEquiv_apply_coe,
    diagonalizableGroupSchemePointsMulEquiv_mapMulEquivOfPresentation]
  rfl

/-- On scheme-valued points, the represented Kostant torus is the original diagonal action in
the weight basis `b`. -/
@[simp]
theorem schemePointsMulEquiv_kostantTorusGroupSchemeMap
    (p : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of ℤ)) ⟶
      (SplitTorus.groupScheme ℤ κ).X) :
    GeneralLinear.schemePointsMulEquiv n A
        (p ≫ (kostantTorusGroupSchemeMap M b wt).hom.hom) =
      kostantTorusMatrix M b wt A
        (SplitTorus.schemePointsMulEquiv (R := ℤ) (A := A) p) := by
  let e := CommHopfAlgCat.mapMulEquivOfPresentation
    (DiagonalizableGroup.coordinateRing ℤ (SplitTorus.characterGroup κ)).obj A
    (DiagonalizableGroup.groupScheme_def ℤ (SplitTorus.characterGroup κ))
  obtain ⟨f, rfl⟩ := e.surjective p
  erw [groupSchemePointsMulEquiv_comp_kostantTorusGroupSchemeMap,
    GeneralLinear.schemePointsMulEquiv_groupSchemePointMulEquiv,
    CommHopfAlgCat.mapPointsFunctor_app_apply,
    GeneralLinear.pointsMulEquiv_apply,
    pointsMulEquiv_kostantTorusCoordinateMap,
    splitTorus_schemePointsMulEquiv_mapMulEquivOfPresentation]

end Points

end TauCeti.UniversalEnvelopingAlgebra
