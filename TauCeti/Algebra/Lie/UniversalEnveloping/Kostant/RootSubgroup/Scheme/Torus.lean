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

variable {κ : Type} [Finite κ]
noncomputable local instance : Fintype κ := Fintype.ofFinite κ
variable {V : Type} [AddCommGroup V]
variable (M : AddSubgroup V)
variable {n : ℕ} (b : Module.Basis (Fin n) ℤ M) (wt : Fin n → κ → ℤ)

private noncomputable def kostantTorusPointAction (A : CommAlgCat ℤ) :
    HopfAlgebra.points
        (R := ℤ) (H := MonoidAlgebra ℤ (Multiplicative (κ →₀ ℤ))) A ⟶
      GeneralLinear.scalarExtensionAutomorphisms (V := M) A :=
  GrpCat.ofHom <| (kostantTorusPoints M b wt A).comp
    (SplitTorus.pointsMulEquiv (R := ℤ) (A := A) (σ := κ)).toMonoidHom

@[simp]
private theorem kostantTorusPointAction_val (A : CommAlgCat ℤ)
    (f : HopfAlgebra.points
      (R := ℤ) (H := MonoidAlgebra ℤ (Multiplicative (κ →₀ ℤ))) A) :
    (kostantTorusPointAction M b wt A f).val =
      (kostantTorusPoints M b wt A (SplitTorus.pointsMulEquiv f)).val := by
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
  have hmap (x : A ⊗[ℤ] M) :
      GeneralLinear.scalarExtensionMap (V := M) φ x =
        TensorProduct.map φ.hom.toLinearMap LinearMap.id x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a m => simp
    | add x y hx hy => simp [hx, hy]
  rw [hmap z, hmap, kostantTorusPointAction_val, kostantTorusPointAction_val]
  have hs :
      SplitTorus.pointsMulEquiv
          (HopfAlgebra.mapPoints
            (H := MonoidAlgebra ℤ (Multiplicative (κ →₀ ℤ))) φ f) =
        fun j => Units.map φ.hom.toMonoidHom (SplitTorus.pointsMulEquiv f j) := by
    funext j
    exact SplitTorus.pointsMulEquiv_mapValue φ.hom f j
  rw [hs]
  exact (map_kostantTorusPoints_algHom M b wt φ.hom
    (SplitTorus.pointsMulEquiv f) z).symm

/-- The natural point representation of the split torus on a Kostant-stable lattice written in a
weight basis.

At a value ring `A`, a point is read as a family `s : κ → Aˣ`, and the action is the diagonal
automorphism whose `i`-th entry is the value at `s` of the weight `wt i`. -/
noncomputable def kostantTorusPointRepresentation :
    HopfAlgebra.PointRepresentation
      (R := ℤ) (H := MonoidAlgebra ℤ (Multiplicative (κ →₀ ℤ))) (V := M) where
  app A := kostantTorusPointAction M b wt A ≫
    eqToHom (GeneralLinear.scalarExtensionAutomorphismsFunctor_obj (V := M) A).symm
  naturality A B φ := by
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

/-- At every categorical value ring, the represented point action is the previously constructed
diagonal torus action after reading a split-torus point as its family of coordinates. -/
@[simp]
theorem kostantTorusPointRepresentation_action (A : CommAlgCat ℤ) :
    (kostantTorusPointRepresentation M b wt).action A =
      GrpCat.ofHom ((kostantTorusPoints M b wt A).comp
        (SplitTorus.pointsMulEquiv (R := ℤ) (A := A) (σ := κ)).toMonoidHom) := by
  rw [HopfAlgebra.PointRepresentation.action_def, kostantTorusPointRepresentation]
  change
    (kostantTorusPointAction M b wt A ≫
        eqToHom (GeneralLinear.scalarExtensionAutomorphismsFunctor_obj (V := M) A).symm) ≫
      eqToHom (GeneralLinear.scalarExtensionAutomorphismsFunctor_obj (V := M) A) =
        GrpCat.ofHom ((kostantTorusPoints M b wt A).comp
          (SplitTorus.pointsMulEquiv (R := ℤ) (A := A) (σ := κ)).toMonoidHom)
  rw [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
  rfl

/-- The coordinate-side comodule recovered from the natural split-torus action on the lattice. -/
@[irreducible]
noncomputable def kostantTorusComodule :
    Comodule ℤ (MonoidAlgebra ℤ (Multiplicative (κ →₀ ℤ))) M :=
  HopfAlgebra.PointRepresentation.toComodule (kostantTorusPointRepresentation M b wt)

/-- The matrix-valued split-torus action in the base-changed weight basis. -/
noncomputable def kostantTorusMatrix (A : Type*) [CommRing A] :
    (κ → Aˣ) →* Matrix.GeneralLinearGroup (Fin n) A :=
  (Units.map (LinearMap.toMatrixAlgEquiv (b.baseChange A)).toMonoidHom).comp
    (kostantTorusPoints M b wt A)

/-- An entry of the torus matrix is the corresponding weight-basis coordinate of the diagonal
action. -/
@[simp]
theorem kostantTorusMatrix_apply (A : Type*) [CommRing A] (s : κ → Aˣ) (r i : Fin n) :
    kostantTorusMatrix M b wt A s r i =
      (b.baseChange A).repr
        ((kostantTorusPoints M b wt A s).val (b.baseChange A i)) r := by
  rw [kostantTorusMatrix, MonoidHom.comp_apply, Units.coe_map]
  exact LinearMap.toMatrixAlgEquiv_apply (b.baseChange A)
    (kostantTorusPoints M b wt A s).val r i

/-- The coordinate Hopf-algebra morphism of the split torus action in the weight basis `b`. -/
noncomputable def kostantTorusCoordinateMap :
    GeneralLinear.coordinateHopfAlgebra ℤ n ⟶
      (DiagonalizableGroup.coordinateRing ℤ (SplitTorus.characterGroup κ)).obj := by
  let : Comodule ℤ (MonoidAlgebra ℤ (Multiplicative (κ →₀ ℤ))) M :=
    kostantTorusComodule M b wt
  exact CommHopfAlgCat.ofHom (Comodule.coordinateBialgHom b)

/-- A generic matrix coordinate pulls back to the corresponding coefficient of the split-torus
comodule. -/
@[simp]
theorem kostantTorusCoordinateMap_X (r i : Fin n) :
    (kostantTorusCoordinateMap M b wt).hom
        (GeneralLinear.coordinateHopfAlgebraAlgEquiv ℤ n
          (GeneralLinear.coordinateRingMap ℤ n (MvPolynomial.X (r, i)))) =
      letI : Comodule ℤ (MonoidAlgebra ℤ (Multiplicative (κ →₀ ℤ))) M :=
        kostantTorusComodule M b wt
      Comodule.coefficientMatrix
        (C := MonoidAlgebra ℤ (Multiplicative (κ →₀ ℤ))) b r i := by
  let : Comodule ℤ (MonoidAlgebra ℤ (Multiplicative (κ →₀ ℤ))) M :=
    kostantTorusComodule M b wt
  exact Comodule.coordinateBialgHom_X b r i

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
  let : Comodule ℤ (MonoidAlgebra ℤ (Multiplicative (κ →₀ ℤ))) M :=
    kostantTorusComodule M b wt
  have hrecover :
      HopfAlgebra.PointRepresentation.ofComodule (kostantTorusComodule M b wt) =
        kostantTorusPointRepresentation M b wt := by
    unfold kostantTorusComodule
    exact HopfAlgebra.PointRepresentation.ofComodule_toComodule _
  have haction := HopfAlgebra.PointRepresentation.ofComodule_action_val_eq_endOfPoint
    (kostantTorusComodule M b wt) (CommAlgCat.of ℤ A) f
  rw [hrecover, kostantTorusPointRepresentation_action] at haction
  change
    (kostantTorusPoints M b wt A (SplitTorus.pointsMulEquiv f)).val =
      Comodule.endOfPoint M f.ofConv at haction
  apply Matrix.GeneralLinearGroup.ext
  intro r i
  rw [GeneralLinear.pointToGeneralLinear_apply, ofConv_toConv, AlgHom.comp_apply]
  change f.ofConv
      ((kostantTorusCoordinateMap M b wt).hom
        (GeneralLinear.coordinateHopfAlgebraAlgEquiv ℤ n
          (GeneralLinear.coordinateRingMap ℤ n (MvPolynomial.X (r, i))))) = _
  rw [kostantTorusCoordinateMap_X, kostantTorusMatrix_apply]
  have hmatrix := Comodule.toMatrix_endOfPoint
    (C := MonoidAlgebra ℤ (Multiplicative (κ →₀ ℤ))) b f.ofConv
  calc
    f.ofConv (Comodule.coefficientMatrix
        (C := MonoidAlgebra ℤ (Multiplicative (κ →₀ ℤ))) b r i) =
        LinearMap.toMatrix (b.baseChange A) (b.baseChange A)
          (Comodule.endOfPoint M f.ofConv) r i := by
            rw [hmatrix, Matrix.map_apply]
    _ = LinearMap.toMatrix (b.baseChange A) (b.baseChange A)
          (kostantTorusPoints M b wt A (SplitTorus.pointsMulEquiv f)).val r i := by
            rw [← haction]
    _ = (b.baseChange A).repr
          ((kostantTorusPoints M b wt A (SplitTorus.pointsMulEquiv f)).val
            (b.baseChange A i)) r := by
            exact LinearMap.toMatrix_apply _ _ _ _ _

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
