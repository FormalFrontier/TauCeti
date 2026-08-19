/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.AdditiveGroup.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Coordinate.BaseChange
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.BaseChange

/-!
# The base-changed toral Kostant closure inside the general linear group

The toral Kostant closure over `ℤ` is the closed subgroup scheme of `GLₙ` generated jointly by
represented root subgroups and a represented split torus. Base change first presents it inside
the scalar extension `A ⊗[ℤ] O(GLₙ/ℤ)`. This file transports that presentation across the
canonical Hopf-algebra isomorphism

```text
A ⊗[ℤ] O(GLₙ/ℤ) ≅ O(GLₙ/A),
```

so the carrier is cut out directly inside `GLₙ` over `A`. The root-subgroup parameter algebra and
the split-torus coordinate algebra are transported at the same time. Consequently the factored
maps have source `O(𝔾ₐ/A)` and `O(T/A)`, rather than scalar extensions of the corresponding
coordinate algebras over `ℤ`.

The transported ideal need not be the largest Hopf ideal killed by the root subgroups and torus
after base change: new equations may appear over a non-flat base. The proved comparison therefore
has the honest direction only. The closed subgroup generated over `A` by the transported root and
torus maps lies in the base change of the integral toral carrier; equality is not asserted.

## Main declarations

* `TauCeti.UniversalEnvelopingAlgebra.kostantToralGeneralLinearBaseChangeIdeal`: the transported
  defining ideal in `O(GLₙ/A)`.
* `kostantToralGeneralLinearBaseChangeIso`: its quotient is the base change of the integral toral
  coordinate ring.
* `kostantRootSubgroupGeneralLinearToralBaseChangeCoordinateMap`: the factorization of a
  base-changed root subgroup through the transported toral carrier.
* `kostantWeightTorusGeneralLinearBaseChangeCoordinateMap` and
  `kostantWeightTorusGeneralLinearToralBaseChangeCoordinateMap`: the represented split torus over
  `A` and its factorization through the transported carrier.
* `kostantToralGeneralLinearBaseChangeIdeal_le_commonKernelHopfIdeal`: the generated-over-`A`
  carrier is a closed subgroup of the transported integral carrier.

## References

This is the base-change compatibility of the explicit Chevalley--Demazure construction; see
R. W. Carter, *Simple Groups of Lie Type*, §4.4, and B. Conrad, *Reductive Group Schemes*, §1.
It advances Layer 9 of `TauCetiRoadmap/ReductiveGroups/README.md`. The resulting carrier over the
prime field and its algebraic closure is consumed by milestone L0 of the CFSGStatement roadmap.
-/

public section

open CategoryTheory

namespace TauCeti.UniversalEnvelopingAlgebra

universe u w

-- Match tensor products to the `ℤ`-algebra structure used by scalar extension.
attribute [local instance high] Algebra.toModule

variable {L : Type u} [LieRing L] [LieAlgebra ℚ L]
variable {I : Type w} {κ : Type} [Finite κ]
variable {V : Type} [AddCommGroup V] [Module ℚ V]

variable (e : I → L) (h : κ → L)
variable (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V)
variable (M : AddSubgroup V)
variable (hM : ∀ u ∈ kostantForm e h, ∀ m ∈ M, ρ u m ∈ M)
variable (hnil : ∀ i, IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
variable {n : ℕ} (b : Module.Basis (Fin n) ℤ M)
variable (wt : Fin n → κ → ℤ)
variable (A : Type*) [CommRing A]

/-- The categorical base-change isomorphism for the additive coordinate Hopf algebra, privately
bundling the existing bialgebra equivalence used by the toral factorization. -/
private noncomputable def additiveCoordinateBaseChangeIso :
    CommHopfAlgCat.baseChange (K := A) (AdditiveGroup.coordinateHopfAlgebra ℤ) ≅
      AdditiveGroup.coordinateHopfAlgebra A :=
  (CommHopfAlgCat.ofIsoSelf
      (CommHopfAlgCat.baseChange (K := A) (AdditiveGroup.coordinateHopfAlgebra ℤ))).symm ≪≫
    CommHopfAlgCat.isoMk (AdditiveGroup.gaScalarTensorBialgEquiv (k := ℤ) (K := A)) ≪≫
      CommHopfAlgCat.ofIsoSelf (AdditiveGroup.coordinateHopfAlgebra A)

/-- The categorical base-change isomorphism for the represented split-torus coordinate Hopf
algebra. Its underlying map is the scalar-extension equivalence for a group algebra. -/
private noncomputable def splitTorusCoordinateBaseChangeIso :
    CommHopfAlgCat.baseChange (K := A)
        (DiagonalizableGroup.coordinateRing ℤ (SplitTorus.characterGroup κ)).obj ≅
      (DiagonalizableGroup.coordinateRing A (SplitTorus.characterGroup κ)).obj :=
  (CommHopfAlgCat.ofIsoSelf
      (CommHopfAlgCat.baseChange (K := A)
        (DiagonalizableGroup.coordinateRing ℤ (SplitTorus.characterGroup κ)).obj)).symm ≪≫
    CommHopfAlgCat.isoMk
      (TauCeti.MonoidAlgebra.scalarTensorBialgEquiv ℤ A
        (G := SplitTorus.characterGroup κ)) ≪≫
      CommHopfAlgCat.ofIsoSelf
        (DiagonalizableGroup.coordinateRing A (SplitTorus.characterGroup κ)).obj

/-- The Hopf ideal of `O(GLₙ/A)` presenting the base change of the toral Kostant closure: the
inverse image of the base-changed defining ideal under the general-linear coordinate
base-change isomorphism. -/
noncomputable def kostantToralGeneralLinearBaseChangeIdeal :
    HopfIdeal A (GeneralLinear.coordinateHopfAlgebra A n) :=
  (kostantToralBaseChangeIdeal e h ρ M hM hnil b wt A).comap
    (GeneralLinear.coordinateHopfAlgebraBaseChangeIso ℤ A n).symm.hom.hom
    (ConcreteCategory.bijective_of_isIso
      (GeneralLinear.coordinateHopfAlgebraBaseChangeIso ℤ A n).symm.hom).2

/-- Membership in the defining ideal over `A` is membership of the transported element in the
base-changed integral defining ideal. -/
@[simp]
theorem mem_kostantToralGeneralLinearBaseChangeIdeal_iff
    {x : GeneralLinear.coordinateHopfAlgebra A n} :
    x ∈ kostantToralGeneralLinearBaseChangeIdeal e h ρ M hM hnil b wt A ↔
      (GeneralLinear.coordinateHopfAlgebraBaseChangeIso ℤ A n).inv.hom x ∈
        kostantToralBaseChangeIdeal e h ρ M hM hnil b wt A :=
  HopfIdeal.mem_comap

/-- Transporting a pure tensor of a scalar and an integral defining equation produces an equation
in the defining ideal over `A`. -/
theorem map_tmul_mem_kostantToralGeneralLinearBaseChangeIdeal_of_mem (s : A)
    {y : GeneralLinear.coordinateHopfAlgebra ℤ n}
    (hy : y ∈ kostantToralDefiningIdeal e h ρ M hM hnil b wt) :
    (GeneralLinear.coordinateHopfAlgebraBaseChangeIso ℤ A n).hom.hom (s ⊗ₜ[ℤ] y) ∈
      kostantToralGeneralLinearBaseChangeIdeal e h ρ M hM hnil b wt A := by
  rw [mem_kostantToralGeneralLinearBaseChangeIdeal_iff,
    CommHopfAlgCat.inv_hom_apply, kostantToralBaseChangeIdeal_def]
  exact CommHopfAlgCat.tmul_mem_baseChangeHopfIdeal s hy

/-- Transporting the presentation from the scalar extension of `O(GLₙ/ℤ)` to `O(GLₙ/A)` gives
isomorphic quotient Hopf algebras. -/
private noncomputable def kostantToralGeneralLinearBaseChangePresentationIso :
    CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra A n)
        (kostantToralGeneralLinearBaseChangeIdeal e h ρ M hM hnil b wt A) ≅
      CommHopfAlgCat.quotient
        (CommHopfAlgCat.baseChange (K := A) (GeneralLinear.coordinateHopfAlgebra ℤ n))
        (kostantToralBaseChangeIdeal e h ρ M hM hnil b wt A) :=
  CommHopfAlgCat.quotientIsoOfIso
    (GeneralLinear.coordinateHopfAlgebraBaseChangeIso ℤ A n).symm
    (kostantToralBaseChangeIdeal e h ρ M hM hnil b wt A)

@[simp]
private theorem mkQuotient_comp_kostantToralGeneralLinearBaseChangePresentationIso_hom :
    CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra A n)
          (kostantToralGeneralLinearBaseChangeIdeal e h ρ M hM hnil b wt A) ≫
        (kostantToralGeneralLinearBaseChangePresentationIso
          e h ρ M hM hnil b wt A).hom =
      (GeneralLinear.coordinateHopfAlgebraBaseChangeIso ℤ A n).inv ≫
        CommHopfAlgCat.mkQuotient
          (CommHopfAlgCat.baseChange (K := A) (GeneralLinear.coordinateHopfAlgebra ℤ n))
          (kostantToralBaseChangeIdeal e h ρ M hM hnil b wt A) :=
  CommHopfAlgCat.mkQuotient_comp_quotientIsoOfIso_hom
    (GeneralLinear.coordinateHopfAlgebraBaseChangeIso ℤ A n).symm
    (kostantToralBaseChangeIdeal e h ρ M hM hnil b wt A)

/-- The toral carrier presented inside `GLₙ` over `A` is the base change of the toral carrier
over `ℤ`. -/
noncomputable def kostantToralGeneralLinearBaseChangeIso :
    CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra A n)
        (kostantToralGeneralLinearBaseChangeIdeal e h ρ M hM hnil b wt A) ≅
      CommHopfAlgCat.baseChange (K := A)
        (CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra ℤ n)
          (kostantToralDefiningIdeal e h ρ M hM hnil b wt)) :=
  kostantToralGeneralLinearBaseChangePresentationIso e h ρ M hM hnil b wt A ≪≫
    kostantToralBaseChangeIso e h ρ M hM hnil b wt A

/-- The base-change identification of the toral carrier is compatible with the quotient maps. -/
@[simp]
theorem mkQuotient_comp_kostantToralGeneralLinearBaseChangeIso_hom :
    CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra A n)
          (kostantToralGeneralLinearBaseChangeIdeal e h ρ M hM hnil b wt A) ≫
        (kostantToralGeneralLinearBaseChangeIso e h ρ M hM hnil b wt A).hom =
      (GeneralLinear.coordinateHopfAlgebraBaseChangeIso ℤ A n).inv ≫
        CommHopfAlgCat.baseChangeMap
          (CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra ℤ n)
            (kostantToralDefiningIdeal e h ρ M hM hnil b wt)) := by
  rw [kostantToralGeneralLinearBaseChangeIso, Iso.trans_hom, ← Category.assoc,
    mkQuotient_comp_kostantToralGeneralLinearBaseChangePresentationIso_hom, Category.assoc,
    mkQuotient_comp_kostantToralBaseChangeIso_hom]

/-- The `i`th represented root subgroup over `A`, factored through the transported toral
carrier. -/
noncomputable def kostantRootSubgroupGeneralLinearToralBaseChangeCoordinateMap (i : I) :
    CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra A n)
        (kostantToralGeneralLinearBaseChangeIdeal e h ρ M hM hnil b wt A) ⟶
      AdditiveGroup.coordinateHopfAlgebra A :=
  (kostantToralGeneralLinearBaseChangePresentationIso e h ρ M hM hnil b wt A).hom ≫
    kostantRootSubgroupToralBaseChangeCoordinateMap e h ρ M hM hnil b wt A i ≫
    (additiveCoordinateBaseChangeIso A).hom

/-- The factored root-subgroup map recovers the represented root subgroup over `A`. -/
@[simp]
theorem mkQuotient_comp_kostantRootSubgroupGeneralLinearToralBaseChangeCoordinateMap (i : I) :
    let E : CommHopfAlgCat.baseChange (K := A) (AdditiveGroup.coordinateHopfAlgebra ℤ) ≅
        AdditiveGroup.coordinateHopfAlgebra A :=
      (CommHopfAlgCat.ofIsoSelf
          (CommHopfAlgCat.baseChange (K := A) (AdditiveGroup.coordinateHopfAlgebra ℤ))).symm ≪≫
        CommHopfAlgCat.isoMk (AdditiveGroup.gaScalarTensorBialgEquiv (k := ℤ) (K := A)) ≪≫
          CommHopfAlgCat.ofIsoSelf (AdditiveGroup.coordinateHopfAlgebra A)
    CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra A n)
          (kostantToralGeneralLinearBaseChangeIdeal e h ρ M hM hnil b wt A) ≫
        kostantRootSubgroupGeneralLinearToralBaseChangeCoordinateMap
          e h ρ M hM hnil b wt A i =
      (GeneralLinear.coordinateHopfAlgebraBaseChangeIso ℤ A n).inv ≫
        CommHopfAlgCat.baseChangeMap
          (kostantRootSubgroupCoordinateMap e h ρ M hM i (hnil i) b) ≫
        E.hom := by
  dsimp only
  rw [kostantRootSubgroupGeneralLinearToralBaseChangeCoordinateMap, ← Category.assoc,
    mkQuotient_comp_kostantToralGeneralLinearBaseChangePresentationIso_hom, Category.assoc,
    ← Category.assoc (CommHopfAlgCat.mkQuotient _ _),
    mkQuotient_comp_kostantRootSubgroupToralBaseChangeCoordinateMap,
    additiveCoordinateBaseChangeIso]

/-- The represented weight torus after base change, as a morphism from `O(GLₙ/A)` to the
coordinate Hopf algebra of the split torus over `A`. -/
noncomputable def kostantWeightTorusGeneralLinearBaseChangeCoordinateMap :
    GeneralLinear.coordinateHopfAlgebra A n ⟶
      (DiagonalizableGroup.coordinateRing A (SplitTorus.characterGroup κ)).obj :=
  (GeneralLinear.coordinateHopfAlgebraBaseChangeIso ℤ A n).inv ≫
    CommHopfAlgCat.baseChangeMap (GeneralLinear.weightTorusCoordinateMap wt) ≫
    (splitTorusCoordinateBaseChangeIso (κ := κ) A).hom

/-- The represented weight torus over `A`, factored through the transported toral carrier. -/
noncomputable def kostantWeightTorusGeneralLinearToralBaseChangeCoordinateMap :
    CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra A n)
        (kostantToralGeneralLinearBaseChangeIdeal e h ρ M hM hnil b wt A) ⟶
      (DiagonalizableGroup.coordinateRing A (SplitTorus.characterGroup κ)).obj :=
  (kostantToralGeneralLinearBaseChangePresentationIso e h ρ M hM hnil b wt A).hom ≫
    kostantWeightTorusToralBaseChangeCoordinateMap e h ρ M hM hnil b wt A ≫
    (splitTorusCoordinateBaseChangeIso (κ := κ) A).hom

/-- The factored weight-torus map recovers the represented split torus over `A`. -/
@[simp]
theorem mkQuotient_comp_kostantWeightTorusGeneralLinearToralBaseChangeCoordinateMap :
    CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra A n)
          (kostantToralGeneralLinearBaseChangeIdeal e h ρ M hM hnil b wt A) ≫
        kostantWeightTorusGeneralLinearToralBaseChangeCoordinateMap e h ρ M hM hnil b wt A =
      kostantWeightTorusGeneralLinearBaseChangeCoordinateMap (κ := κ) wt A := by
  rw [kostantWeightTorusGeneralLinearToralBaseChangeCoordinateMap, ← Category.assoc,
    mkQuotient_comp_kostantToralGeneralLinearBaseChangePresentationIso_hom, Category.assoc,
    ← Category.assoc (CommHopfAlgCat.mkQuotient _ _),
    mkQuotient_comp_kostantWeightTorusToralBaseChangeCoordinateMap,
    kostantWeightTorusGeneralLinearBaseChangeCoordinateMap]

/-- Every transported root-subgroup map kills the defining ideal over `A`. -/
theorem kostantToralGeneralLinearBaseChangeIdeal_toIdeal_le_root_ker (i : I) :
    let E : CommHopfAlgCat.baseChange (K := A) (AdditiveGroup.coordinateHopfAlgebra ℤ) ≅
        AdditiveGroup.coordinateHopfAlgebra A :=
      (CommHopfAlgCat.ofIsoSelf
          (CommHopfAlgCat.baseChange (K := A) (AdditiveGroup.coordinateHopfAlgebra ℤ))).symm ≪≫
        CommHopfAlgCat.isoMk (AdditiveGroup.gaScalarTensorBialgEquiv (k := ℤ) (K := A)) ≪≫
          CommHopfAlgCat.ofIsoSelf (AdditiveGroup.coordinateHopfAlgebra A)
    (kostantToralGeneralLinearBaseChangeIdeal e h ρ M hM hnil b wt A).toIdeal ≤
      RingHom.ker
        (((GeneralLinear.coordinateHopfAlgebraBaseChangeIso ℤ A n).inv ≫
            CommHopfAlgCat.baseChangeMap
              (kostantRootSubgroupCoordinateMap e h ρ M hM i (hnil i) b) ≫
            E.hom).hom.toAlgHom.toRingHom) := by
  dsimp only
  rw [← CommHopfAlgCat.mkQuotient_ker (GeneralLinear.coordinateHopfAlgebra A n)
    (kostantToralGeneralLinearBaseChangeIdeal e h ρ M hM hnil b wt A)]
  intro x hx
  rw [RingHom.mem_ker] at hx ⊢
  have hcomp := congrArg (fun f => f.hom x)
    (mkQuotient_comp_kostantRootSubgroupGeneralLinearToralBaseChangeCoordinateMap
      e h ρ M hM hnil b wt A i)
  change (((GeneralLinear.coordinateHopfAlgebraBaseChangeIso ℤ A n).inv ≫
      CommHopfAlgCat.baseChangeMap
        (kostantRootSubgroupCoordinateMap e h ρ M hM i (hnil i) b) ≫
      (additiveCoordinateBaseChangeIso A).hom).hom x) = 0
  rw [additiveCoordinateBaseChangeIso]
  rw [← hcomp]
  change (kostantRootSubgroupGeneralLinearToralBaseChangeCoordinateMap
    e h ρ M hM hnil b wt A i).hom
      ((CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra A n)
        (kostantToralGeneralLinearBaseChangeIdeal e h ρ M hM hnil b wt A)).hom x) = 0
  have hx' : (CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra A n)
      (kostantToralGeneralLinearBaseChangeIdeal e h ρ M hM hnil b wt A)).hom x = 0 := by
    simpa only [BialgHom.coe_toAlgHom, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] using hx
  rw [hx', map_zero]

/-- The transported weight-torus map kills the defining ideal over `A`. -/
theorem kostantToralGeneralLinearBaseChangeIdeal_toIdeal_le_torus_ker :
    (kostantToralGeneralLinearBaseChangeIdeal e h ρ M hM hnil b wt A).toIdeal ≤
      RingHom.ker
        (kostantWeightTorusGeneralLinearBaseChangeCoordinateMap
          (κ := κ) wt A).hom.toAlgHom.toRingHom := by
  rw [← CommHopfAlgCat.mkQuotient_ker (GeneralLinear.coordinateHopfAlgebra A n)
    (kostantToralGeneralLinearBaseChangeIdeal e h ρ M hM hnil b wt A)]
  intro x hx
  rw [RingHom.mem_ker] at hx ⊢
  have hcomp := congrArg (fun f => f.hom x)
    (mkQuotient_comp_kostantWeightTorusGeneralLinearToralBaseChangeCoordinateMap
      e h ρ M hM hnil b wt A)
  change (kostantWeightTorusGeneralLinearBaseChangeCoordinateMap
    (κ := κ) wt A).hom x = 0
  rw [← hcomp]
  change (kostantWeightTorusGeneralLinearToralBaseChangeCoordinateMap
    e h ρ M hM hnil b wt A).hom
      ((CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra A n)
        (kostantToralGeneralLinearBaseChangeIdeal e h ρ M hM hnil b wt A)).hom x) = 0
  have hx' : (CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra A n)
      (kostantToralGeneralLinearBaseChangeIdeal e h ρ M hM hnil b wt A)).hom x = 0 := by
    simpa only [BialgHom.coe_toAlgHom, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] using hx
  rw [hx', map_zero]

/-- The closed subgroup of `GLₙ/A` generated by the transported root subgroups and split torus
lies in the transported base change of the integral toral carrier.

The reverse inclusion is deliberately not claimed: a Hopf ideal killed by all generators after
base change need not descend to an integral Hopf ideal. -/
theorem kostantToralGeneralLinearBaseChangeIdeal_le_commonKernelHopfIdeal :
    let E : CommHopfAlgCat.baseChange (K := A) (AdditiveGroup.coordinateHopfAlgebra ℤ) ≅
        AdditiveGroup.coordinateHopfAlgebra A :=
      (CommHopfAlgCat.ofIsoSelf
          (CommHopfAlgCat.baseChange (K := A) (AdditiveGroup.coordinateHopfAlgebra ℤ))).symm ≪≫
        CommHopfAlgCat.isoMk (AdditiveGroup.gaScalarTensorBialgEquiv (k := ℤ) (K := A)) ≪≫
          CommHopfAlgCat.ofIsoSelf (AdditiveGroup.coordinateHopfAlgebra A)
    let K : Sum I Unit → CommHopfAlgCat A
      | .inl _ => AdditiveGroup.coordinateHopfAlgebra A
      | .inr _ => (DiagonalizableGroup.coordinateRing A (SplitTorus.characterGroup κ)).obj
    kostantToralGeneralLinearBaseChangeIdeal e h ρ M hM hnil b wt A ≤
      CommHopfAlgCat.commonKernelHopfIdeal (K := K)
        (fun j => match j with
          | Sum.inl i =>
              (GeneralLinear.coordinateHopfAlgebraBaseChangeIso ℤ A n).inv ≫
                CommHopfAlgCat.baseChangeMap
                  (kostantRootSubgroupCoordinateMap e h ρ M hM i (hnil i) b) ≫
                E.hom
          | Sum.inr _ => kostantWeightTorusGeneralLinearBaseChangeCoordinateMap
              (κ := κ) wt A) := by
  dsimp only
  rw [CommHopfAlgCat.le_commonKernelHopfIdeal_iff]
  rintro (i | _)
  · exact kostantToralGeneralLinearBaseChangeIdeal_toIdeal_le_root_ker
      e h ρ M hM hnil b wt A i
  · exact kostantToralGeneralLinearBaseChangeIdeal_toIdeal_le_torus_ker
      e h ρ M hM hnil b wt A

end TauCeti.UniversalEnvelopingAlgebra
