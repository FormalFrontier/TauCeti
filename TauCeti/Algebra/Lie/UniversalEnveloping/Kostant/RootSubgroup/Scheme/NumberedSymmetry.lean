/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.Yoneda
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.FunctorOfPoints
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Weight.Torus
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.NumberedSymmetry
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.Basic

/-!
# The ambient coordinate automorphism of a numbered Kostant symmetry

A symmetry of numbered Kostant data is a self-map `σ` of the index set together with a rational
automorphism `θ` of the representation which preserves the integral lattice `M` and carries the
action of `eᵢ` to the action of `e_{σ i}`. Conjugating by the scalar extension of `θ` is then an
automorphism of the general linear group of `A ⊗[ℤ] M`, natural in the value ring `A`.

This file turns that natural automorphism into an automorphism of the coordinate Hopf algebra of
`GLₙ` itself, and records the two compositional identities a closed subgroup scheme of `GLₙ` needs
in order to inherit it:

```text
γ ≫ xᵢ = x_{σ i},        γ ≫ (weight torus of wt) = weight torus of (wt ∘ π⁻¹).
```

The first says that conjugation permutes the represented Kostant root subgroups without touching
their additive parameters. The second says that when `θ` permutes the chosen lattice basis by `π`,
conjugation carries the represented weight torus of a weight family to the weight torus of the
relabelled family. Preserving a subgroup scheme cut out by both families additionally requires
weight equivariance identifying that family with the original one, through a permutation of the
torus index and `GeneralLinear.weightTorusCoordinateMap_reindex`.

Neither identity is available from the construction of the coordinate automorphism, which goes
through the functor of points: full faithfulness of the functor of points on commutative Hopf
algebras recovers the coordinate morphism from the natural conjugation, and each identity is then
proved by evaluating both sides at the generic point of the relevant codomain.

Nothing here assumes that `σ` comes from a Dynkin-diagram symmetry, that `θ` is unique, or that the
weights are the weights of an admissible lattice: all of that is supplied by the caller.

## Main declarations

* `TauCeti.UniversalEnvelopingAlgebra.kostantNumberedSymmetryMatrix`: the matrix of the
  base-changed lattice symmetry in the chosen basis.
* `TauCeti.UniversalEnvelopingAlgebra.kostantNumberedSymmetryCoordinateIso`: the resulting
  automorphism of the coordinate Hopf algebra of `GLₙ`.

## Main results

* `pointsMulEquiv_mapPointsFunctor_kostantNumberedSymmetryCoordinateIso`: on algebra-valued points
  the coordinate automorphism is conjugation by the base-changed matrix.
* `pointsMulEquiv_toConv_comp_kostantNumberedSymmetryCoordinateIso`: the same statement for a value
  ring in an arbitrary universe, obtained by transporting the generic point of the coordinate Hopf
  algebra along the naturality of the matrix.
* `kostantNumberedSymmetryCoordinateIso_hom_comp_rootSubgroupCoordinateMap`: the pinning equation
  `γ ≫ xᵢ = x_{σ i}` on coordinate algebras.
* `kostantNumberedSymmetryCoordinateIso_hom_comp_weightTorusCoordinateMap`: a basis-permuting
  symmetry carries the represented weight torus to the relabelled weight torus.

All of these live in the `TauCeti.UniversalEnvelopingAlgebra` namespace.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §12.2.
* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §1.15.
* J. E. Humphreys, *Linear Algebraic Groups*, §27.

This advances the pinnings and pinned-isomorphism targets of Layer 9 of
`TauCetiRoadmap/ReductiveGroups/README.md`; the automorphisms it produces are required by milestone
L1 of `TauCetiRoadmap/CFSGStatement/README.md`.
-/

public section

open AlgebraicGeometry CategoryTheory TensorProduct WithConv

namespace TauCeti.UniversalEnvelopingAlgebra

universe u v v' w z

attribute [local instance high] Algebra.toModule

variable {L : Type u} [LieRing L] [LieAlgebra ℚ L]
variable {I : Type w} {κ : Type z}
variable {V : Type} [AddCommGroup V] [Module ℚ V]

variable (e : I → L) (h : κ → L)
variable (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V)
variable (M : AddSubgroup V)
variable (hM : ∀ u ∈ kostantForm e h, ∀ m ∈ M, ρ u m ∈ M)
variable (hnil : ∀ i, IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
variable {n : ℕ} (b : Module.Basis (Fin n) ℤ M)
variable (σ : I → I) (θ : V ≃ₗ[ℚ] V) (hθM : ∀ v, θ v ∈ M ↔ v ∈ M)
variable (hθe : ∀ i, ∀ v : V,
  θ (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i)) v) =
    ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e (σ i))) (θ v))

/-- The matrix of the base-changed lattice symmetry in the chosen basis. -/
noncomputable def kostantNumberedSymmetryMatrix (A : Type v) [CommRing A] :
    Matrix.GeneralLinearGroup (Fin n) A :=
  Units.map (LinearMap.toMatrixAlgEquiv (b.baseChange A)).toMulEquiv
    (AddEquiv.baseChangeInvariantRestrictUnit (R := A) θ.toAddEquiv M hθM)

/-- The matrix of the numbered symmetry commutes with extension of the value ring. -/
theorem map_kostantNumberedSymmetryMatrix {A : Type v} {B : Type v'} [CommRing A] [CommRing B]
    (φ : A →+* B) :
    Matrix.GeneralLinearGroup.map φ (kostantNumberedSymmetryMatrix M b θ hθM A) =
      kostantNumberedSymmetryMatrix M b θ hθM B := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rw [Matrix.GeneralLinearGroup.map_apply]
  have hintertwine (z : A ⊗[ℤ] M) :
      TensorProduct.map φ.toIntAlgHom.toLinearMap LinearMap.id
          ((AddEquiv.baseChangeInvariantRestrictUnit
            (R := A) θ.toAddEquiv M hθM).val z) =
        (AddEquiv.baseChangeInvariantRestrictUnit
            (R := B) θ.toAddEquiv M hθM).val
          (TensorProduct.map φ.toIntAlgHom.toLinearMap LinearMap.id z) := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a m =>
        simp only [TensorProduct.map_tmul, AlgHom.toLinearMap_apply, LinearMap.id_apply,
          AddEquiv.val_baseChangeInvariantRestrictUnit_tmul]
  have hmatrix := Module.Basis.map_toMatrixAlgEquiv_baseChange b φ.toIntAlgHom
    (AddEquiv.baseChangeInvariantRestrictUnit (R := A) θ.toAddEquiv M hθM).val
    (AddEquiv.baseChangeInvariantRestrictUnit (R := B) θ.toAddEquiv M hθM).val
    hintertwine
  rw [kostantNumberedSymmetryMatrix, kostantNumberedSymmetryMatrix,
    Units.coe_map, Units.coe_map]
  -- `Units.map` and `GeneralLinearGroup.map` expose their underlying matrices only by
  -- reduction; there is no conversion lemma from this entrywise goal to `hmatrix`.
  change φ ((LinearMap.toMatrixAlgEquiv (b.baseChange A))
      (AddEquiv.baseChangeInvariantRestrictUnit (R := A) θ.toAddEquiv M hθM).val i j) =
    (LinearMap.toMatrixAlgEquiv (b.baseChange B))
      (AddEquiv.baseChangeInvariantRestrictUnit (R := B) θ.toAddEquiv M hθM).val i j
  exact congrFun (congrFun hmatrix i) j

/-- Conjugation by the numbered symmetry on the points of the general-linear coordinate
Hopf algebra. -/
private noncomputable def generalLinearPointsNumberedSymmetryMulEquiv (A : CommAlgCat.{0} ℤ) :
    HopfAlgebra.points
        (R := ℤ) (H := GeneralLinear.coordinateHopfAlgebra ℤ n) A ≃*
      HopfAlgebra.points
        (R := ℤ) (H := GeneralLinear.coordinateHopfAlgebra ℤ n) A :=
  ((GeneralLinear.pointsMulEquiv (R := ℤ) (A := A) n).trans
    (MulAut.conj (kostantNumberedSymmetryMatrix M b θ hθM A))).trans
      (GeneralLinear.pointsMulEquiv (R := ℤ) (A := A) n).symm

private theorem pointsMulEquiv_generalLinearPointsNumberedSymmetryMulEquiv
    (A : CommAlgCat.{0} ℤ)
    (f : HopfAlgebra.points
      (R := ℤ) (H := GeneralLinear.coordinateHopfAlgebra ℤ n) A) :
    GeneralLinear.pointsMulEquiv n
        (generalLinearPointsNumberedSymmetryMulEquiv M b θ hθM A f) =
      kostantNumberedSymmetryMatrix M b θ hθM A *
          GeneralLinear.pointsMulEquiv n f *
        (kostantNumberedSymmetryMatrix M b θ hθM A)⁻¹ := by
  rw [generalLinearPointsNumberedSymmetryMulEquiv]
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply]
  exact (GeneralLinear.pointsMulEquiv (R := ℤ) (A := A) n).apply_symm_apply _

/-- The pointwise symmetry, transported to the object presentation used by the points functor. -/
private noncomputable def generalLinearPointsNumberedSymmetryIsoApp (A : CommAlgCat.{0} ℤ) :
    (HopfAlgebra.pointsFunctor
        (R := ℤ) (H := GeneralLinear.coordinateHopfAlgebra ℤ n)).obj A ≅
      (HopfAlgebra.pointsFunctor
        (R := ℤ) (H := GeneralLinear.coordinateHopfAlgebra ℤ n)).obj A :=
  eqToIso (HopfAlgebra.pointsFunctor_obj
      (R := ℤ) (H := GeneralLinear.coordinateHopfAlgebra ℤ n) A) ≪≫
    (generalLinearPointsNumberedSymmetryMulEquiv M b θ hθM A).toGrpIso ≪≫
      eqToIso (HopfAlgebra.pointsFunctor_obj
        (R := ℤ) (H := GeneralLinear.coordinateHopfAlgebra ℤ n) A).symm

/-- The numbered symmetry transported to the functor of points of the general-linear
coordinate Hopf algebra. -/
private noncomputable def generalLinearPointsNumberedSymmetryNatIso :
    HopfAlgebra.pointsFunctor
        (R := ℤ) (H := GeneralLinear.coordinateHopfAlgebra ℤ n) ≅
      HopfAlgebra.pointsFunctor
        (R := ℤ) (H := GeneralLinear.coordinateHopfAlgebra ℤ n) :=
  NatIso.ofComponents
    (fun A ↦ generalLinearPointsNumberedSymmetryIsoApp M b θ hθM A)
    (fun {A B} φ ↦ by
      apply (cancel_epi (eqToHom (HopfAlgebra.pointsFunctor_obj
        (R := ℤ) (H := GeneralLinear.coordinateHopfAlgebra ℤ n) A).symm)).1
      apply (cancel_mono (eqToHom (HopfAlgebra.pointsFunctor_obj
        (R := ℤ) (H := GeneralLinear.coordinateHopfAlgebra ℤ n) B))).1
      rw [generalLinearPointsNumberedSymmetryIsoApp,
        generalLinearPointsNumberedSymmetryIsoApp]
      simp only [Iso.trans_hom, eqToIso.hom, Category.assoc, eqToHom_trans_assoc,
        eqToHom_refl, Category.id_comp, eqToHom_trans, Category.comp_id]
      simp only [← Category.assoc]
      rw [HopfAlgebra.pointsFunctor_map_eqToHom]
      slice_rhs 2 3 => rw [HopfAlgebra.pointsFunctor_map_eqToHom]
      slice_rhs 3 4 => simp
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
        Category.comp_id]
      apply GrpCat.hom_ext
      apply MonoidHom.ext
      intro f
      rw [GrpCat.comp_apply, GrpCat.comp_apply]
      -- Cancelling the object transports leaves the underlying `MulEquiv`; its application
      -- is definitionally the displayed pointwise operation, but has no named rewrite lemma.
      change generalLinearPointsNumberedSymmetryMulEquiv M b θ hθM B
          (HopfAlgebra.mapPoints φ f) =
        HopfAlgebra.mapPoints φ
          (generalLinearPointsNumberedSymmetryMulEquiv M b θ hθM A f)
      apply (GeneralLinear.pointsMulEquiv (R := ℤ) (A := B) n).injective
      simp only [HopfAlgebra.mapPoints]
      rw [pointsMulEquiv_generalLinearPointsNumberedSymmetryMulEquiv]
      -- `mapPoints` is implemented by `AlgHom.mapValue`; exposing that implementation is
      -- necessary before the public `pointsMulEquiv_mapValue` theorem can rewrite the goal.
      change kostantNumberedSymmetryMatrix M b θ hθM B *
            GeneralLinear.pointsMulEquiv n (AlgHom.mapValue φ.hom f) *
          (kostantNumberedSymmetryMatrix M b θ hθM B)⁻¹ =
        GeneralLinear.pointsMulEquiv n
          (AlgHom.mapValue φ.hom
            (generalLinearPointsNumberedSymmetryMulEquiv M b θ hθM A f))
      rw [GeneralLinear.pointsMulEquiv_mapValue,
        GeneralLinear.pointsMulEquiv_mapValue,
        pointsMulEquiv_generalLinearPointsNumberedSymmetryMulEquiv]
      rw [map_mul, map_mul, map_inv, map_kostantNumberedSymmetryMatrix M b θ hθM])

/-- The coordinate Hopf-algebra automorphism recovered from conjugation on points. -/
noncomputable def kostantNumberedSymmetryCoordinateIso :
    GeneralLinear.coordinateHopfAlgebra ℤ n ≅
      GeneralLinear.coordinateHopfAlgebra ℤ n :=
  ((CommHopfAlgCat.pointsFunctor (R := ℤ)).preimageIso
    (generalLinearPointsNumberedSymmetryNatIso M b θ hθM)).unop

/-- On algebra-valued points, the recovered coordinate automorphism is conjugation by the
base-changed numbered-symmetry matrix. -/
theorem pointsMulEquiv_mapPointsFunctor_kostantNumberedSymmetryCoordinateIso
    (A : CommAlgCat.{0} ℤ)
    (f : HopfAlgebra.points
      (R := ℤ) (H := GeneralLinear.coordinateHopfAlgebra ℤ n) A) :
    GeneralLinear.pointsMulEquiv n
        ((CommHopfAlgCat.mapPointsFunctor
          (kostantNumberedSymmetryCoordinateIso M b θ hθM).hom).app A f) =
      kostantNumberedSymmetryMatrix M b θ hθM A *
          GeneralLinear.pointsMulEquiv n f *
        (kostantNumberedSymmetryMatrix M b θ hθM A)⁻¹ := by
  have hmap := (CommHopfAlgCat.pointsFunctor (R := ℤ)).map_preimage
    (generalLinearPointsNumberedSymmetryNatIso M b θ hθM).hom
  have happ := congrArg (fun α => α.app A f) hmap
  have hcoordinate :
      (kostantNumberedSymmetryCoordinateIso M b θ hθM).hom.op =
        (CommHopfAlgCat.pointsFunctor (R := ℤ)).preimage
          (generalLinearPointsNumberedSymmetryNatIso M b θ hθM).hom := rfl
  -- Fix the concrete presentation of the point before moving between the two functor APIs;
  -- their agreement below is mediated by `pointsFunctor.map_preimage`, not a rewrite lemma.
  change GeneralLinear.pointsMulEquiv n
      ((CommHopfAlgCat.mapPointsFunctor
        (kostantNumberedSymmetryCoordinateIso M b θ hθM).hom).app A f) = _
  -- `mapPointsFunctor` is definitionally the opposite-coordinate morphism under
  -- `pointsFunctor`; expose that representation so `hcoordinate` can rewrite its argument.
  change GeneralLinear.pointsMulEquiv n
      (((CommHopfAlgCat.pointsFunctor (R := ℤ)).map
        (kostantNumberedSymmetryCoordinateIso M b θ hθM).hom.op).app A f) = _
  rw [hcoordinate]
  rw [happ]
  -- `NatIso.ofComponents` stores this component through equality transports; after `happ`
  -- those transports reduce to the underlying pointwise `MulEquiv`, with no named theorem.
  change GeneralLinear.pointsMulEquiv n
      (generalLinearPointsNumberedSymmetryMulEquiv M b θ hθM A f) = _
  exact pointsMulEquiv_generalLinearPointsNumberedSymmetryMulEquiv M b θ hθM A f

/-- Explicit precomposition form of the action of the recovered coordinate automorphism. -/
private theorem pointsMulEquiv_comp_kostantNumberedSymmetryCoordinateIso
    (A : CommAlgCat.{0} ℤ)
    (f : HopfAlgebra.points
      (R := ℤ) (H := GeneralLinear.coordinateHopfAlgebra ℤ n) A) :
    GeneralLinear.pointsMulEquiv n
        (toConv (f.ofConv.comp
          ((kostantNumberedSymmetryCoordinateIso M b θ hθM).hom.hom :
            GeneralLinear.coordinateHopfAlgebra ℤ n →ₐ[ℤ]
              GeneralLinear.coordinateHopfAlgebra ℤ n))) =
      kostantNumberedSymmetryMatrix M b θ hθM A *
          GeneralLinear.pointsMulEquiv n f *
        (kostantNumberedSymmetryMatrix M b θ hθM A)⁻¹ := by
  rw [← CommHopfAlgCat.mapPointsFunctor_app_apply]
  exact pointsMulEquiv_mapPointsFunctor_kostantNumberedSymmetryCoordinateIso
    M b θ hθM A f

/-- **On the algebra-valued points of `GLₙ` over a value ring in any universe, the recovered
coordinate automorphism is conjugation by the base-changed numbered-symmetry matrix.** The
comparison through the functor of points is available only for a value algebra of the category that
functor is taken over. Both sides here are natural in the value ring, so reading that comparison at
the generic point of the coordinate Hopf algebra and pushing it forward along an arbitrary point
removes the restriction. -/
theorem pointsMulEquiv_toConv_comp_kostantNumberedSymmetryCoordinateIso (A : Type v) [CommRing A]
    (f : WithConv (GeneralLinear.coordinateHopfAlgebra ℤ n →ₐ[ℤ] A)) :
    GeneralLinear.pointsMulEquiv n
        (toConv (f.ofConv.comp
          ((kostantNumberedSymmetryCoordinateIso M b θ hθM).hom.hom :
            GeneralLinear.coordinateHopfAlgebra ℤ n →ₐ[ℤ]
              GeneralLinear.coordinateHopfAlgebra ℤ n))) =
      kostantNumberedSymmetryMatrix M b θ hθM A *
          GeneralLinear.pointsMulEquiv n f *
        (kostantNumberedSymmetryMatrix M b θ hθM A)⁻¹ := by
  have hgeneric := pointsMulEquiv_comp_kostantNumberedSymmetryCoordinateIso M b θ hθM
    (CommAlgCat.of ℤ (GeneralLinear.coordinateHopfAlgebra ℤ n))
    (toConv (AlgHom.id ℤ (GeneralLinear.coordinateHopfAlgebra ℤ n)))
  rw [ofConv_toConv, AlgHom.id_comp] at hgeneric
  have hnat (g : WithConv (GeneralLinear.coordinateHopfAlgebra ℤ n →ₐ[ℤ]
      GeneralLinear.coordinateHopfAlgebra ℤ n)) :
      GeneralLinear.pointsMulEquiv n
          (AlgHom.mapValue (H := GeneralLinear.coordinateHopfAlgebra ℤ n) f.ofConv g) =
        Matrix.GeneralLinearGroup.map f.ofConv.toRingHom (GeneralLinear.pointsMulEquiv n g) :=
    GeneralLinear.pointsMulEquiv_mapValue n f.ofConv g
  have hgen : AlgHom.mapValue (H := GeneralLinear.coordinateHopfAlgebra ℤ n) f.ofConv
      (toConv (AlgHom.id ℤ (GeneralLinear.coordinateHopfAlgebra ℤ n))) = f := by
    rw [AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_id, toConv_ofConv]
  have hsym : AlgHom.mapValue (H := GeneralLinear.coordinateHopfAlgebra ℤ n) f.ofConv
      (toConv ((kostantNumberedSymmetryCoordinateIso M b θ hθM).hom.hom :
        GeneralLinear.coordinateHopfAlgebra ℤ n →ₐ[ℤ]
          GeneralLinear.coordinateHopfAlgebra ℤ n)) =
      toConv (f.ofConv.comp
        ((kostantNumberedSymmetryCoordinateIso M b θ hθM).hom.hom :
          GeneralLinear.coordinateHopfAlgebra ℤ n →ₐ[ℤ]
            GeneralLinear.coordinateHopfAlgebra ℤ n)) := by
    rw [AlgHom.mapValue_apply, ofConv_toConv]
  rw [← hsym, hnat, hgeneric, map_mul, map_mul, map_inv,
    map_kostantNumberedSymmetryMatrix M b θ hθM, ← hnat, hgen]

include hθe in
/-- Matrix-coordinate form of the pinning equation. -/
theorem kostantNumberedSymmetryMatrix_conj_kostantRootSubgroupMatrix
    (A : Type v) [CommRing A] (i : I)
    (q : WithConv (SymmetricAlgebra ℤ ℤ →ₐ[ℤ] A)) :
    kostantNumberedSymmetryMatrix M b θ hθM A *
          kostantRootSubgroupMatrix e h ρ M hM i (hnil i) b q *
        (kostantNumberedSymmetryMatrix M b θ hθM A)⁻¹ =
      kostantRootSubgroupMatrix e h ρ M hM (σ i) (hnil (σ i)) b q := by
  let t := AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := CommAlgCat.of ℤ A) q
  have hconj := baseChangeInvariantRestrictUnit_conj_kostantRootSubgroupParam
    e h ρ M hM hnil σ θ hθM hθe (CommAlgCat.of ℤ A) i t
  have hmatrix := congrArg
    (Units.map (LinearMap.toMatrixAlgEquiv
      (b.baseChange (CommAlgCat.of ℤ A))).toMonoidHom) hconj
  rw [map_mul, map_mul, map_inv] at hmatrix
  have htheta : Units.map (LinearMap.toMatrixAlgEquiv
        (b.baseChange (CommAlgCat.of ℤ A))).toMonoidHom
        (AddEquiv.baseChangeInvariantRestrictUnit
          (R := CommAlgCat.of ℤ A) θ.toAddEquiv M hθM) =
      kostantNumberedSymmetryMatrix M b θ hθM A := rfl
  have hroot (j : I) : Units.map (LinearMap.toMatrixAlgEquiv
        (b.baseChange (CommAlgCat.of ℤ A))).toMonoidHom
        (kostantRootSubgroupParam e h ρ M hM j (hnil j)
          (CommAlgCat.of ℤ A) t) =
      kostantRootSubgroupMatrix e h ρ M hM j (hnil j) b q := by
    rw [kostantRootSubgroupMatrix_def, MonoidHom.comp_apply,
      kostantRootSubgroupParam_apply]
    congr 1
    dsimp only [t]
    exact congrArg (kostantRootSubgroupPoints e h ρ M hM j (hnil j))
      ((AdditiveGroup.gaPointsMulEquiv
        (R := ℤ) (A := CommAlgCat.of ℤ A)).symm_apply_apply q)
  rw [htheta, hroot i, hroot (σ i)] at hmatrix
  exact hmatrix

include hθe in
/-- The ambient coordinate automorphism permutes the Kostant root-subgroup coordinate maps. -/
theorem kostantNumberedSymmetryCoordinateIso_hom_comp_rootSubgroupCoordinateMap
    (i : I) :
    (kostantNumberedSymmetryCoordinateIso M b θ hθM).hom ≫
        kostantRootSubgroupCoordinateMap e h ρ M hM i (hnil i) b =
      kostantRootSubgroupCoordinateMap e h ρ M hM (σ i) (hnil (σ i)) b := by
  let c := (kostantNumberedSymmetryCoordinateIso M b θ hθM).hom
  let r := kostantRootSubgroupCoordinateMap e h ρ M hM i (hnil i) b
  let s := kostantRootSubgroupCoordinateMap e h ρ M hM (σ i) (hnil (σ i)) b
  apply _root_.CommHopfAlgCat.hom_ext
  ext x
  let q : WithConv (AdditiveGroup.coordinateHopfAlgebra ℤ →ₐ[ℤ]
      AdditiveGroup.coordinateHopfAlgebra ℤ) :=
    toConv (AlgHom.id ℤ (AdditiveGroup.coordinateHopfAlgebra ℤ))
  let f : HopfAlgebra.points
      (R := ℤ) (H := GeneralLinear.coordinateHopfAlgebra ℤ n)
        (CommAlgCat.of ℤ (AdditiveGroup.coordinateHopfAlgebra ℤ)) :=
    toConv (q.ofConv.comp r.hom.toAlgHom)
  let g : HopfAlgebra.points
      (R := ℤ) (H := GeneralLinear.coordinateHopfAlgebra ℤ n)
        (CommAlgCat.of ℤ (AdditiveGroup.coordinateHopfAlgebra ℤ)) :=
    toConv (q.ofConv.comp s.hom.toAlgHom)
  have hroot_i : GeneralLinear.pointToGeneralLinear n f =
      kostantRootSubgroupMatrix e h ρ M hM i (hnil i) b q := by
    exact pointsMulEquiv_kostantRootSubgroupCoordinateMap
      e h ρ M hM i (hnil i) b
        (A := AdditiveGroup.coordinateHopfAlgebra ℤ) q
  have hroot_σ : GeneralLinear.pointToGeneralLinear n g =
      kostantRootSubgroupMatrix e h ρ M hM (σ i) (hnil (σ i)) b q := by
    exact pointsMulEquiv_kostantRootSubgroupCoordinateMap
      e h ρ M hM (σ i) (hnil (σ i)) b
        (A := AdditiveGroup.coordinateHopfAlgebra ℤ) q
  have hmatrix := kostantNumberedSymmetryMatrix_conj_kostantRootSubgroupMatrix
    e h ρ M hM hnil b σ θ hθM hθe
      (AdditiveGroup.coordinateHopfAlgebra ℤ) i q
  have hp : toConv (f.ofConv.comp c.hom.toAlgHom) = g := by
    apply (GeneralLinear.pointsMulEquiv
      (R := ℤ) (A := CommAlgCat.of ℤ (AdditiveGroup.coordinateHopfAlgebra ℤ)) n).injective
    rw [pointsMulEquiv_comp_kostantNumberedSymmetryCoordinateIso,
      GeneralLinear.pointsMulEquiv_apply, GeneralLinear.pointsMulEquiv_apply]
    have hleft := congrArg
      (fun z => kostantNumberedSymmetryMatrix M b θ hθM
          (AdditiveGroup.coordinateHopfAlgebra ℤ) * z *
        (kostantNumberedSymmetryMatrix M b θ hθM
          (AdditiveGroup.coordinateHopfAlgebra ℤ))⁻¹) hroot_i
    exact hleft.trans (hmatrix.trans hroot_σ.symm)
  have hx := congrArg (fun p => p.ofConv x) hp
  simp only [f, g, q, AlgHom.id_apply, AlgHom.comp_apply] at hx
  rw [_root_.CommHopfAlgCat.comp_apply]
  exact hx

/-- The entries of the numbered-symmetry matrix are the coordinates of the images of the basis
vectors. -/
theorem coe_kostantNumberedSymmetryMatrix_apply (A : Type v) [CommRing A] (i j : Fin n) :
    (kostantNumberedSymmetryMatrix M b θ hθM A : Matrix (Fin n) (Fin n) A) i j =
      (b.baseChange A).repr
        ((AddEquiv.baseChangeInvariantRestrictUnit (R := A) θ.toAddEquiv M hθM).val
          ((b.baseChange A) j)) i := by
  rw [kostantNumberedSymmetryMatrix, Units.coe_map]
  exact LinearMap.toMatrixAlgEquiv_apply (b.baseChange A) _ i j

/-- **A symmetry permuting the chosen lattice basis has a permutation matrix.** This is the
hypothesis under which conjugation normalizes the diagonal torus of `GLₙ`, and it holds for the
coordinate permutation a Dynkin-diagram symmetry induces on Geck's lattice. -/
theorem coe_kostantNumberedSymmetryMatrix_of_perm (basisPerm : Equiv.Perm (Fin n))
    (hbasis : ∀ i, θ ((b i : M) : V) = ((b (basisPerm i) : M) : V))
    (A : Type v) [CommRing A] :
    (kostantNumberedSymmetryMatrix M b θ hθM A : Matrix (Fin n) (Fin n) A) =
      (basisPerm⁻¹).permMatrix A := by
  ext i j
  rw [coe_kostantNumberedSymmetryMatrix_apply, Module.Basis.baseChange_apply]
  have hval : (AddEquiv.baseChangeInvariantRestrictUnit
      (R := A) θ.toAddEquiv M hθM).val ((1 : A) ⊗ₜ[ℤ] b j) = (1 : A) ⊗ₜ[ℤ] b (basisPerm j) := by
    rw [AddEquiv.val_baseChangeInvariantRestrictUnit_tmul]
    congr 1
    refine Subtype.ext ?_
    rw [AddEquiv.coe_invariantRestrict_apply]
    exact hbasis j
  rw [hval, Module.Basis.baseChange_repr_tmul, b.repr_self, Finsupp.single_apply]
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.eq_symm_apply, eq_comm]

/-- **Conjugating a diagonal matrix by a basis-permuting symmetry relabels its entries by the
inverse permutation.** In particular the diagonal torus of `GLₙ` is normalized. -/
theorem kostantNumberedSymmetryMatrix_conj_diagGL (basisPerm : Equiv.Perm (Fin n))
    (hbasis : ∀ i, θ ((b i : M) : V) = ((b (basisPerm i) : M) : V))
    (A : Type v) [CommRing A] (d : Fin n → Aˣ) :
    kostantNumberedSymmetryMatrix M b θ hθM A * diagGL d *
        (kostantNumberedSymmetryMatrix M b θ hθM A)⁻¹ =
      diagGL (fun i => d (basisPerm⁻¹ i)) := by
  rw [mul_diagGL_of_coe_eq_permMatrix
      (kostantNumberedSymmetryMatrix M b θ hθM A) basisPerm⁻¹
      (coe_kostantNumberedSymmetryMatrix_of_perm M b θ hθM basisPerm hbasis A) d,
    mul_assoc, mul_inv_cancel, mul_one]
  rfl

/-- **A basis-permuting numbered symmetry carries the represented weight torus of a weight family
to the weight torus of the relabelled family.** Stability of a closed subgroup scheme cut out by
the root subgroups and a weight torus additionally requires identifying this relabelled family
with the original one, via weight equivariance and
`GeneralLinear.weightTorusCoordinateMap_reindex`. -/
theorem kostantNumberedSymmetryCoordinateIso_hom_comp_weightTorusCoordinateMap
    {ι : Type} [Finite ι] (wt : Fin n → ι → ℤ) (basisPerm : Equiv.Perm (Fin n))
    (hbasis : ∀ i, θ ((b i : M) : V) = ((b (basisPerm i) : M) : V)) :
    (kostantNumberedSymmetryCoordinateIso M b θ hθM).hom ≫
        GeneralLinear.weightTorusCoordinateMap (R := ℤ) wt =
      GeneralLinear.weightTorusCoordinateMap (R := ℤ) (fun i => wt (basisPerm⁻¹ i)) := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  let c := (kostantNumberedSymmetryCoordinateIso M b θ hθM).hom
  let r := GeneralLinear.weightTorusCoordinateMap (R := ℤ) wt
  let s := GeneralLinear.weightTorusCoordinateMap (R := ℤ) (fun i => wt (basisPerm⁻¹ i))
  apply _root_.CommHopfAlgCat.hom_ext
  refine DFunLike.ext _ _ fun x => ?_
  let T := MonoidAlgebra ℤ (SplitTorus.characterGroup ι)
  let q : WithConv (T →ₐ[ℤ] T) := toConv (AlgHom.id ℤ T)
  let f : HopfAlgebra.points
      (R := ℤ) (H := GeneralLinear.coordinateHopfAlgebra ℤ n) (CommAlgCat.of ℤ T) :=
    toConv (q.ofConv.comp r.hom.toAlgHom)
  let g : HopfAlgebra.points
      (R := ℤ) (H := GeneralLinear.coordinateHopfAlgebra ℤ n) (CommAlgCat.of ℤ T) :=
    toConv (q.ofConv.comp s.hom.toAlgHom)
  have htorus_r : GeneralLinear.pointsMulEquiv n f =
      diagGL fun i => torusCharacter (SplitTorus.pointsMulEquiv q) (wt i) := by
    calc
      _ = GeneralLinear.pointsMulEquiv n
          ((CommHopfAlgCat.mapPointsFunctor r).app (CommAlgCat.of ℤ T) q) := by
        rw [CommHopfAlgCat.mapPointsFunctor_app_apply]
      _ = _ := GeneralLinear.pointsMulEquiv_mapPointsFunctor_weightTorusCoordinateMap
        wt (CommAlgCat.of ℤ T) q
  have htorus_s : GeneralLinear.pointsMulEquiv n g =
      diagGL fun i =>
        torusCharacter (SplitTorus.pointsMulEquiv q) (wt (basisPerm⁻¹ i)) := by
    calc
      _ = GeneralLinear.pointsMulEquiv n
          ((CommHopfAlgCat.mapPointsFunctor s).app (CommAlgCat.of ℤ T) q) := by
        rw [CommHopfAlgCat.mapPointsFunctor_app_apply]
      _ = _ := GeneralLinear.pointsMulEquiv_mapPointsFunctor_weightTorusCoordinateMap
        (fun i => wt (basisPerm⁻¹ i)) (CommAlgCat.of ℤ T) q
  have hp : toConv (f.ofConv.comp c.hom.toAlgHom) = g := by
    apply (GeneralLinear.pointsMulEquiv (R := ℤ) (A := CommAlgCat.of ℤ T) n).injective
    rw [pointsMulEquiv_comp_kostantNumberedSymmetryCoordinateIso, htorus_r, htorus_s,
      kostantNumberedSymmetryMatrix_conj_diagGL M b θ hθM basisPerm hbasis]
  have hx := congrArg (fun p => p.ofConv x) hp
  simp only [f, g, q, AlgHom.id_apply, AlgHom.comp_apply] at hx
  rw [_root_.CommHopfAlgCat.comp_apply]
  exact hx

end TauCeti.UniversalEnvelopingAlgebra
