/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Basic

/-!
# Naturality of Hopf-ideal quotient points

For a Hopf ideal `I` in a commutative Hopf algebra `H`, the quotient Hopf algebra
`H ⧸ I` represents the closed subgroup whose `A`-points are the ambient `H`-points killing
`I`. This file records that this description is natural in the value algebra `A`.

The quotient-points inclusion commutes with post-composition along a morphism
`A ⟶ B` of commutative `R`-algebras. Consequently the subgroup of ambient points cut out by
`I` is preserved by the functor-of-points map, and the value-algebra map restricts to a
homomorphism between these subgroups.

This is a small Layer 3 prerequisite for the ReductiveGroups roadmap target "Hopf ideals ↔
closed subgroup schemes": the closed-subgroup functor represented by `H ⧸ I` must be a
subfunctor of the ambient points functor, not just a subgroup at each individual algebra.
-/

public section

open CategoryTheory WithConv

namespace TauCeti

universe u v w w'

namespace CommHopfAlgCat

variable {R : Type u} [CommRing R]

/-- The quotient-points inclusion is natural in the value algebra. -/
@[simp]
lemma mapPoints_quotientPointsHom (H : _root_.CommHopfAlgCat.{v} R)
    (I : HopfIdeal R H) {A B : CommAlgCat.{w} R}
    (χ : A ⟶ B) (f : HopfAlgebra.points (R := R) (H := quotient H I) A) :
    HopfAlgebra.mapPoints (H := H) χ (quotientPointsHom H I A f) =
      quotientPointsHom H I B (HopfAlgebra.mapPoints (H := quotient H I) χ f) := by
  exact mapPointsFunctor_naturality_apply (R := R) (mkQuotient H I) χ f

/-- The quotient-points inclusion commutes with post-composition, including when the source and
target value algebras lie in different universes. -/
lemma mapValue_quotientPointsHom (H : _root_.CommHopfAlgCat.{v} R)
    (I : HopfIdeal R H) {A : Type w} {B : Type w'}
    [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (χ : A →ₐ[R] B)
    (f : HopfAlgebra.points (R := R) (H := quotient H I) (CommAlgCat.of R A)) :
    AlgHom.mapValue χ (quotientPointsHom H I (CommAlgCat.of R A) f) =
      quotientPointsHom H I (CommAlgCat.of R B) (AlgHom.mapValue χ f) := by
  rw [quotientPointsHom_apply, quotientPointsHom_apply, AlgHom.mapValue_apply,
    AlgHom.mapValue_apply, AlgHom.comp_assoc]

/-- Post-composition by an algebra homomorphism preserves the ambient-point subgroup cut out by a
Hopf ideal, including when the source and target value algebras lie in different universes. -/
lemma mapValue_mem_quotientPointsSubgroup (H : _root_.CommHopfAlgCat.{v} R)
    (I : HopfIdeal R H) {A : Type w} {B : Type w'}
    [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (χ : A →ₐ[R] B)
    {g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R A)}
    (hg : g ∈ quotientPointsSubgroup H I (CommAlgCat.of R A)) :
    AlgHom.mapValue χ g ∈ quotientPointsSubgroup H I (CommAlgCat.of R B) := by
  rw [mem_quotientPointsSubgroup_iff] at hg ⊢
  intro h hh
  rw [AlgHom.mapValue_apply]
  rw [WithConv.ofConv_toConv, AlgHom.comp_apply]
  rw [hg h hh, map_zero]

/-- Post-composition preserves the ambient-point subgroup cut out by a Hopf ideal. -/
lemma mapPoints_mem_quotientPointsSubgroup (H : _root_.CommHopfAlgCat.{v} R)
    (I : HopfIdeal R H) {A B : CommAlgCat.{w} R}
    (χ : A ⟶ B) {g : HopfAlgebra.points (R := R) (H := H) A}
    (hg : g ∈ quotientPointsSubgroup H I A) :
    HopfAlgebra.mapPoints (H := H) χ g ∈ quotientPointsSubgroup H I B := by
  exact mapValue_mem_quotientPointsSubgroup H I χ.hom hg

/-- The functor-of-points map restricted to the subgroups cut out by a Hopf ideal. -/
@[expose] noncomputable def mapQuotientPointsSubgroup (H : _root_.CommHopfAlgCat.{v} R)
    (I : HopfIdeal R H) {A B : CommAlgCat.{w} R}
    (χ : A ⟶ B) :
    quotientPointsSubgroup H I A →* quotientPointsSubgroup H I B :=
  (((HopfAlgebra.mapPoints (H := H) χ).hom.domRestrict (quotientPointsSubgroup H I A)).codRestrict
    (quotientPointsSubgroup H I B)
    fun g => mapPoints_mem_quotientPointsSubgroup H I χ g.property)

/-- The value-algebra functor of the point subgroups cut out by a Hopf ideal. -/
@[expose] noncomputable def quotientPointsSubgroupFunctor
    (H : _root_.CommHopfAlgCat.{v} R) (I : HopfIdeal R H) :
    CommAlgCat.{w} R ⥤ GrpCat.{max v w} where
  obj A := GrpCat.of (quotientPointsSubgroup H I A)
  map {A B} χ := GrpCat.ofHom (mapQuotientPointsSubgroup H I χ)
  map_id A := by
    ext g h
    rfl
  map_comp {A B C} χ ψ := by
    ext g h
    rfl

/-- The object part of the subgroup functor is the cut-out point subgroup. -/
@[simp]
lemma quotientPointsSubgroupFunctor_obj (H : _root_.CommHopfAlgCat.{v} R)
    (I : HopfIdeal R H) (A : CommAlgCat.{w} R) :
    (quotientPointsSubgroupFunctor (R := R) H I).obj A =
      GrpCat.of (quotientPointsSubgroup H I A) :=
  rfl

/-- The map part of the subgroup functor is the restricted value-algebra map. -/
@[simp]
lemma quotientPointsSubgroupFunctor_map (H : _root_.CommHopfAlgCat.{v} R)
    (I : HopfIdeal R H) {A B : CommAlgCat.{w} R} (χ : A ⟶ B) :
    (quotientPointsSubgroupFunctor (R := R) H I).map χ =
      GrpCat.ofHom (mapQuotientPointsSubgroup H I χ) :=
  rfl

/-- The subgroup functor includes naturally into the ambient functor of points. -/
@[expose] noncomputable def quotientPointsSubgroupIncl (H : _root_.CommHopfAlgCat.{v} R)
    (I : HopfIdeal R H) :
    quotientPointsSubgroupFunctor (R := R) H I ⟶
      HopfAlgebra.pointsFunctor (R := R) (H := H) where
  app A := GrpCat.ofHom (quotientPointsSubgroup H I A).subtype
  naturality {A B} χ := by
    ext g
    rfl

/-- The component of the subgroup inclusion is the subgroup subtype map. -/
@[simp]
lemma quotientPointsSubgroupIncl_app (H : _root_.CommHopfAlgCat.{v} R)
    (I : HopfIdeal R H) (A : CommAlgCat.{w} R) :
    (quotientPointsSubgroupIncl H I).app A =
      GrpCat.ofHom (quotientPointsSubgroup H I A).subtype :=
  rfl

/-- The restricted map on cut-out subgroups is induced by the ambient functor-of-points map. -/
@[simp]
lemma mapQuotientPointsSubgroup_apply (H : _root_.CommHopfAlgCat.{v} R)
    (I : HopfIdeal R H) {A B : CommAlgCat.{w} R}
    (χ : A ⟶ B) (g : quotientPointsSubgroup H I A) :
    mapQuotientPointsSubgroup H I χ g =
      ⟨HopfAlgebra.mapPoints (H := H) χ g,
        mapPoints_mem_quotientPointsSubgroup H I χ g.property⟩ :=
  rfl

/-- Coercing the restricted subgroup map gives the ambient functor-of-points map. -/
@[simp]
lemma coe_mapQuotientPointsSubgroup_apply (H : _root_.CommHopfAlgCat.{v} R)
    (I : HopfIdeal R H) {A B : CommAlgCat.{w} R}
    (χ : A ⟶ B) (g : quotientPointsSubgroup H I A) :
    (mapQuotientPointsSubgroup H I χ g :
      HopfAlgebra.points (R := R) (H := H) B) =
      HopfAlgebra.mapPoints (H := H) χ g :=
  rfl

/-- Pointwise form of the restricted subgroup map. -/
@[simp]
lemma mapQuotientPointsSubgroup_apply_apply (H : _root_.CommHopfAlgCat.{v} R)
    (I : HopfIdeal R H) {A B : CommAlgCat.{w} R}
    (χ : A ⟶ B) (g : quotientPointsSubgroup H I A) (h : H) :
    ((mapQuotientPointsSubgroup H I χ g :
      HopfAlgebra.points (R := R) (H := H) B).ofConv) h =
      χ.hom (g.val.ofConv h) :=
  rfl

/-- The restricted subgroup maps preserve identity morphisms of value algebras. -/
@[simp]
lemma mapQuotientPointsSubgroup_id (H : _root_.CommHopfAlgCat.{v} R)
    (I : HopfIdeal R H) (A : CommAlgCat.{w} R) :
    mapQuotientPointsSubgroup H I (𝟙 A) =
      MonoidHom.id (quotientPointsSubgroup H I A) := by
  exact congrArg GrpCat.Hom.hom ((quotientPointsSubgroupFunctor (R := R) H I).map_id A)

/-- The restricted subgroup maps preserve composition of value-algebra morphisms. -/
lemma mapQuotientPointsSubgroup_comp (H : _root_.CommHopfAlgCat.{v} R)
    (I : HopfIdeal R H) {A B C : CommAlgCat.{w} R} (χ : A ⟶ B) (ψ : B ⟶ C) :
    mapQuotientPointsSubgroup H I (χ ≫ ψ) =
      (mapQuotientPointsSubgroup H I ψ).comp
        (mapQuotientPointsSubgroup H I χ) := by
  exact congrArg GrpCat.Hom.hom ((quotientPointsSubgroupFunctor (R := R) H I).map_comp χ ψ)

/-- The inverse to the injective quotient-points homomorphism, with codomain restricted to its
cut-out subgroup. -/
private noncomputable def liftQuotientPointHom (H : _root_.CommHopfAlgCat.{v} R)
    (I : HopfIdeal R H) (A : CommAlgCat.{w} R) :
    quotientPointsSubgroup H I A →* HopfAlgebra.points (R := R) (H := quotient H I) A :=
  ((MonoidHom.ofInjective (f := (quotientPointsHom H I A).hom)
    (quotientPointsHom_injective H I A)).symm).toMonoidHom

private lemma liftQuotientPointHom_apply (H : _root_.CommHopfAlgCat.{v} R)
    (I : HopfIdeal R H) (A : CommAlgCat.{w} R) (g : quotientPointsSubgroup H I A) :
    liftQuotientPointHom H I A g =
      liftQuotientPoint H I A g ((mem_quotientPointsSubgroup_iff H I A g).mp g.property) := by
  apply quotientPointsHom_injective H I A
  have hg : g.1 ∈ (quotientPointsHom H I A).hom.range := by
    have hgp := g.property
    -- `g.property` is stated through the `Subtype` predicate of the subgroup coercion; `change`
    -- puts it back in the `∈ quotientPointsSubgroup …` form the membership lemmas expect.
    change g.1 ∈ quotientPointsSubgroup H I A at hgp
    exact hgp
  -- `liftQuotientPointHom` is the `toMonoidHom` of the inverse equivalence returned by
  -- `MonoidHom.ofInjective`; this coercion exposes the underlying inverse application so the
  -- standard `apply_ofInjective_symm` lemma can rewrite it.
  change (quotientPointsHom H I A).hom
      (((MonoidHom.ofInjective (f := (quotientPointsHom H I A).hom)
        (quotientPointsHom_injective H I A)).symm) ⟨g.1, hg⟩) =
    (quotientPointsHom H I A).hom
      (liftQuotientPoint H I A g
        ((mem_quotientPointsSubgroup_iff H I A g).mp g.property))
  rw [MonoidHom.apply_ofInjective_symm, quotientPointsHom_liftQuotientPoint]

/-- The component isomorphism between quotient points and the cut-out subgroup. -/
@[expose] noncomputable def quotientPointsSubgroupIso (H : _root_.CommHopfAlgCat.{v} R)
    (I : HopfIdeal R H) (A : CommAlgCat.{w} R) :
    GrpCat.of (HopfAlgebra.points (R := R) (H := quotient H I) A) ≅
      GrpCat.of (quotientPointsSubgroup H I A) :=
  (MonoidHom.ofInjective (f := (quotientPointsHom H I A).hom)
    (quotientPointsHom_injective H I A)).toGrpIso

/-- The component isomorphism sends a quotient point to its included ambient point. -/
@[simp]
lemma quotientPointsSubgroupIso_hom_apply (H : _root_.CommHopfAlgCat.{v} R)
    (I : HopfIdeal R H) (A : CommAlgCat.{w} R)
    (f : HopfAlgebra.points (R := R) (H := quotient H I) A) :
    (quotientPointsSubgroupIso H I A).hom f =
      (⟨quotientPointsHom H I A f, quotientPointsHom_mem_quotientPointsSubgroup H I A f⟩ :
        quotientPointsSubgroup H I A) :=
  Subtype.ext rfl

/-- The inverse component is the quotient point factoring the included ambient point. -/
@[simp]
lemma quotientPointsSubgroupIso_inv_apply (H : _root_.CommHopfAlgCat.{v} R)
    (I : HopfIdeal R H) (A : CommAlgCat.{w} R)
    (g : quotientPointsSubgroup H I A) :
    (quotientPointsSubgroupIso H I A).inv g =
      liftQuotientPoint H I A g ((mem_quotientPointsSubgroup_iff H I A g).mp g.property) := by
  exact liftQuotientPointHom_apply H I A g

private lemma quotientPointsSubgroupFunctor_map_quotientPointsHom_aux
    (H : _root_.CommHopfAlgCat.{v} R) (I : HopfIdeal R H) {A B : CommAlgCat.{w} R}
    (χ : A ⟶ B) (f : HopfAlgebra.points (R := R) (H := quotient H I) A) :
    mapQuotientPointsSubgroup H I χ
        ⟨quotientPointsHom H I A f, quotientPointsHom_mem_quotientPointsSubgroup H I A f⟩ =
      ⟨quotientPointsHom H I B (HopfAlgebra.mapPoints (H := quotient H I) χ f),
        quotientPointsHom_mem_quotientPointsSubgroup H I B _⟩ := by
  apply Subtype.ext
  rw [coe_mapQuotientPointsSubgroup_apply, mapPoints_quotientPointsHom]

/-- The quotient Hopf algebra represents the subgroup functor cut out by the Hopf ideal. -/
noncomputable def quotientPointsSubgroupNatIso (H : _root_.CommHopfAlgCat.{v} R)
    (I : HopfIdeal R H) :
    HopfAlgebra.pointsFunctor (R := R) (H := quotient H I) ≅
      quotientPointsSubgroupFunctor (R := R) H I :=
  NatIso.ofComponents
    (quotientPointsSubgroupIso H I)
    (by
      intro A B χ
      ext f
      exact (quotientPointsSubgroupFunctor_map_quotientPointsHom_aux H I χ f).symm)

/-- The natural isomorphism's forward component is the quotient-subgroup component isomorphism. -/
@[simp]
lemma quotientPointsSubgroupNatIso_hom_app_apply (H : _root_.CommHopfAlgCat.{v} R)
    (I : HopfIdeal R H) (A : CommAlgCat.{w} R)
    (f : HopfAlgebra.points (R := R) (H := quotient H I) A) :
    CategoryTheory.ConcreteCategory.hom
        (X := HopfAlgebra.pointsFunctor (R := R) (H := quotient H I).obj A)
        (Y := GrpCat.of (quotientPointsSubgroup H I A))
        ((quotientPointsSubgroupNatIso H I).hom.app A) f =
      (⟨quotientPointsHom H I A f, quotientPointsHom_mem_quotientPointsSubgroup H I A f⟩ :
        quotientPointsSubgroup H I A) := by
  exact quotientPointsSubgroupIso_hom_apply H I A f

/-- The natural isomorphism's inverse component is the quotient lift of a subgroup point. -/
@[simp]
lemma quotientPointsSubgroupNatIso_inv_app_apply (H : _root_.CommHopfAlgCat.{v} R)
    (I : HopfIdeal R H) (A : CommAlgCat.{w} R)
    (g : quotientPointsSubgroup H I A) :
    CategoryTheory.ConcreteCategory.hom
        (X := GrpCat.of (quotientPointsSubgroup H I A))
        (Y := HopfAlgebra.pointsFunctor (R := R) (H := quotient H I).obj A)
        ((quotientPointsSubgroupNatIso H I).inv.app A) g =
      liftQuotientPoint H I A g ((mem_quotientPointsSubgroup_iff H I A g).mp g.property) := by
  exact quotientPointsSubgroupIso_inv_apply H I A g

section SubgroupRepresentability

variable (H : _root_.CommHopfAlgCat.{v} R) (I : HopfIdeal R H)
variable (S : (A : CommAlgCat.{w} R) →
  Subgroup (HopfAlgebra.points (R := R) (H := H) A))
variable (mapS : {A B : CommAlgCat.{w} R} → (A ⟶ B) → S A →* S B)
variable (mapS_id : ∀ (A : CommAlgCat.{w} R) (g : S A), mapS (𝟙 A) g = g)
variable (mapS_comp : ∀ {A B C : CommAlgCat.{w} R} (φ : A ⟶ B) (ψ : B ⟶ C)
  (g : S A), mapS (φ ≫ ψ) g = mapS ψ (mapS φ g))
variable (hS : ∀ (A : CommAlgCat.{w} R)
  (g : HopfAlgebra.points (R := R) (H := H) A),
  g ∈ quotientPointsSubgroup H I A ↔ g ∈ S A)
variable (hmapS : ∀ {A B : CommAlgCat.{w} R} (φ : A ⟶ B) (g : S A),
  (mapS φ g : HopfAlgebra.points (R := R) (H := H) B) =
    HopfAlgebra.mapPoints (H := H) φ g)

/-- Pointwise identification of a Hopf-ideal cut-out with a subgroup family having the same
membership predicate. -/
private noncomputable def quotientPointsSubgroupMulEquiv (A : CommAlgCat.{w} R) :
    quotientPointsSubgroup H I A ≃* S A :=
  MulEquiv.subgroupCongr <| Subgroup.ext fun g ↦ hS A g

include hmapS in
private theorem quotientPointsSubgroupMulEquiv_natural
    {A B : CommAlgCat.{w} R} (φ : A ⟶ B) (g : quotientPointsSubgroup H I A) :
    quotientPointsSubgroupMulEquiv H I S hS B
        (mapQuotientPointsSubgroup H I φ g) =
      mapS φ (quotientPointsSubgroupMulEquiv H I S hS A g) := by
  apply Subtype.ext
  calc
    _ = (mapQuotientPointsSubgroup H I φ g :
        HopfAlgebra.points (R := R) (H := H) B) :=
      MulEquiv.subgroupCongr_apply _ _
    _ = HopfAlgebra.mapPoints (H := H) φ g :=
      coe_mapQuotientPointsSubgroup_apply H I φ g
    _ = HopfAlgebra.mapPoints (H := H) φ
        (quotientPointsSubgroupMulEquiv H I S hS A g) := by
      exact congrArg (HopfAlgebra.mapPoints (H := H) φ)
        (MulEquiv.subgroupCongr_apply _ g).symm
    _ = (mapS φ (quotientPointsSubgroupMulEquiv H I S hS A g) :
        HopfAlgebra.points (R := R) (H := H) B) :=
      (hmapS φ _).symm

include hS hmapS
/-- The Hopf-ideal cut-out subgroup functor is naturally isomorphic to any stable subgroup
family with the same pointwise membership condition. -/
noncomputable def quotientPointsSubgroupFunctorIso :
    quotientPointsSubgroupFunctor (R := R) H I ≅
      HopfAlgebra.subgroupFunctor S mapS mapS_id mapS_comp :=
  NatIso.ofComponents
    (fun A ↦ (quotientPointsSubgroupMulEquiv H I S hS A).toGrpIso)
    (by
      intro A B φ
      apply GrpCat.hom_ext
      apply MonoidHom.ext
      intro g
      exact quotientPointsSubgroupMulEquiv_natural H I S mapS hS hmapS φ g)

/-- A Hopf quotient represents any value-algebra-stable family of ambient point subgroups
whose membership condition agrees with vanishing on the Hopf ideal. -/
noncomputable def quotientPointsSubgroupRepresentingIso :
    HopfAlgebra.pointsFunctor (R := R) (H := quotient H I) ≅
      HopfAlgebra.subgroupFunctor S mapS mapS_id mapS_comp :=
  (quotientPointsSubgroupNatIso H I).trans
    (quotientPointsSubgroupFunctorIso H I S mapS mapS_id mapS_comp hS hmapS)

/-- The represented subgroup point underlying a quotient point is induced by the quotient
coordinate map. -/
@[simp]
theorem coe_quotientPointsSubgroupRepresentingIso_hom_app_apply
    (A : CommAlgCat.{w} R)
    (f : HopfAlgebra.points (R := R) (H := quotient H I) A) :
    ((CategoryTheory.ConcreteCategory.hom
      (X := HopfAlgebra.pointsFunctor (R := R) (H := quotient H I) |>.obj A)
      (Y := GrpCat.of (S A))
      ((quotientPointsSubgroupRepresentingIso
        H I S mapS mapS_id mapS_comp hS hmapS).hom.app A) f : S A) :
          HopfAlgebra.points (R := R) (H := H) A) =
      quotientPointsHom H I A f := by
  have hcomponent := quotientPointsSubgroupNatIso_hom_app_apply H I A f
  unfold quotientPointsSubgroupRepresentingIso
  exact congrArg
    (fun g ↦ ((quotientPointsSubgroupMulEquiv H I S hS A g : S A) :
      HopfAlgebra.points (R := R) (H := H) A))
    hcomponent

/-- Applying the quotient inclusion to the inverse representing isomorphism recovers the
ambient subgroup point. -/
@[simp]
theorem quotientPointsHom_quotientPointsSubgroupRepresentingIso_inv_app_apply
    (A : CommAlgCat.{w} R) (g : S A) :
    quotientPointsHom H I A
        (CategoryTheory.ConcreteCategory.hom
          (X := GrpCat.of (S A))
          (Y := HopfAlgebra.pointsFunctor (R := R) (H := quotient H I) |>.obj A)
          ((quotientPointsSubgroupRepresentingIso
            H I S mapS mapS_id mapS_comp hS hmapS).inv.app A) g) =
      g.1 := by
  let f :=
    CategoryTheory.ConcreteCategory.hom
      (X := GrpCat.of (S A))
      (Y := HopfAlgebra.pointsFunctor (R := R) (H := quotient H I) |>.obj A)
      ((quotientPointsSubgroupRepresentingIso
        H I S mapS mapS_id mapS_comp hS hmapS).inv.app A) g
  calc
    quotientPointsHom H I A f =
        ((CategoryTheory.ConcreteCategory.hom
          (X := HopfAlgebra.pointsFunctor (R := R) (H := quotient H I) |>.obj A)
          (Y := GrpCat.of (S A))
          ((quotientPointsSubgroupRepresentingIso
            H I S mapS mapS_id mapS_comp hS hmapS).hom.app A) f : S A) :
              HopfAlgebra.points (R := R) (H := H) A) :=
      (coe_quotientPointsSubgroupRepresentingIso_hom_app_apply
        H I S mapS mapS_id mapS_comp hS hmapS A f).symm
    _ = g.1 := by
      have hinv := CategoryTheory.Iso.inv_hom_id_apply
        ((quotientPointsSubgroupRepresentingIso
          H I S mapS mapS_id mapS_comp hS hmapS).app A)
        g
      exact congrArg Subtype.val hinv

end SubgroupRepresentability

/-- The image of a quotient point under the subgroup functor is its mapped quotient point,
viewed inside the cut-out subgroup. -/
lemma quotientPointsSubgroupFunctor_map_quotientPointsHom
    (H : _root_.CommHopfAlgCat.{v} R) (I : HopfIdeal R H) {A B : CommAlgCat.{w} R}
    (χ : A ⟶ B) (f : HopfAlgebra.points (R := R) (H := quotient H I) A) :
    mapQuotientPointsSubgroup H I χ
        ⟨quotientPointsHom H I A f, quotientPointsHom_mem_quotientPointsSubgroup H I A f⟩ =
      ⟨quotientPointsHom H I B (HopfAlgebra.mapPoints (H := quotient H I) χ f),
        quotientPointsHom_mem_quotientPointsSubgroup H I B _⟩ := by
  exact quotientPointsSubgroupFunctor_map_quotientPointsHom_aux H I χ f

/-- Factoring an ambient point through the quotient is natural in the value algebra. -/
lemma mapPoints_liftQuotientPoint (H : _root_.CommHopfAlgCat.{v} R)
    (I : HopfIdeal R H) {A B : CommAlgCat.{w} R}
    (χ : A ⟶ B) (g : HopfAlgebra.points (R := R) (H := H) A)
    (hg : ∀ h : H, h ∈ I → g.ofConv h = 0) :
    HopfAlgebra.mapPoints (H := quotient H I) χ
        (liftQuotientPoint H I A g hg) =
      liftQuotientPoint H I B (HopfAlgebra.mapPoints (H := H) χ g)
        (by
          intro h hh
          exact (mem_quotientPointsSubgroup_iff H I B _).mp
            (mapPoints_mem_quotientPointsSubgroup H I χ
              ((mem_quotientPointsSubgroup_iff H I A g).mpr hg)) h hh) := by
  apply quotientPointsHom_injective H I B
  rw [← mapPoints_quotientPointsHom H I χ, quotientPointsHom_liftQuotientPoint,
    quotientPointsHom_liftQuotientPoint]

end CommHopfAlgCat

end TauCeti
