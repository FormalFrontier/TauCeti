/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import TauCeti.Algebra.AlgebraicGroup.Fppf.Quotient.Projection

/-!
# The fppf quotient projection as a torsor

Let `H` be a commutative Hopf algebra over a commutative ring `R`, and let `I` be a normal Hopf
ideal. The quotient Hopf algebra `H / I` represents the closed normal subgroup `V(I)` of the
affine group represented by `H`. This file proves the kernel-pair formulation of the statement
that

```text
G ⟶ G / V(I)
```

is a `V(I)`-torsor: the square

```text
G × V(I)  --(g,n) ↦ g-->    G
    |                         |
 (g,n) ↦ gn               | quotient
    |                         |
    v                         v
    G          --quotient-->  G / V(I)
```

is a pullback. It is first proved for the pointwise quotient presheaf. Applying fppf
sheafification and its canonical finite-product comparison gives the corresponding pullback square
on the product of the fppf sheaves.

No representability of `G / V(I)` is asserted.

## Main declarations

* `TauCeti.CommHopfAlgCat.isPullback_pointwiseQuotientTorsor`: the pointwise quotient has the
  expected torsor kernel pair.
* `TauCeti.CommHopfAlgCat.isPullback_fppfQuotientTorsor`: the same square after fppf
  sheafification.

## References

* J. S. Milne, *Algebraic Groups* (2017), Section 5.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Section 14.

This is the torsor and kernel-pair step of Layer 3, "Normality and quotients", of the
ReductiveGroups roadmap.
-/

public section

open CategoryTheory ConcreteCategory Opposite
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.Obj

namespace TauCeti.CommHopfAlgCat

universe u

variable {R : Type u} [CommRing R]

private theorem isPullback_pointwiseQuotientMk
    (H : _root_.CommHopfAlgCat.{u} R) (I : HopfIdeal R H) (hI : I.IsNormal)
    (A : CommAlgCat.{u} R) :
    IsPullback
      (↾fun p : HopfAlgebra.points (R := R) (H := H) A ×
        HopfAlgebra.points (R := R) (H := quotient H I) A => p.1)
      (↾fun p : HopfAlgebra.points (R := R) (H := H) A ×
        HopfAlgebra.points (R := R) (H := quotient H I) A =>
          p.1 * quotientPointsHom H I A p.2)
      (↾fun g => pointwiseQuotientMk H I hI A g)
      (↾fun g => pointwiseQuotientMk H I hI A g) := by
  let _ : (quotientPointsSubgroup H I A).Normal :=
    quotientPointsSubgroup_normal H I hI A
  rw [CategoryTheory.Limits.Types.isPullback_iff]
  refine ⟨?_, ?_, ?_⟩
  · ext p
    -- `Types.isPullback_iff` exposes bundled concrete maps. There is no rewrite lemma from
    -- those wrappers to their functions, so reduce that wrapper before using the quotient API.
    change pointwiseQuotientMk H I hI A p.1 =
      pointwiseQuotientMk H I hI A (p.1 * quotientPointsHom H I A p.2)
    have hn : pointwiseQuotientMk H I hI A (quotientPointsHom H I A p.2) = 1 :=
      (pointwiseQuotientMk_eq_one_iff H I hI A _).2
        (quotientPointsHom_mem_quotientPointsSubgroup H I A p.2)
    rw [map_mul, hn, mul_one]
  · rintro ⟨g, n⟩ ⟨g', n'⟩ ⟨hg, hgn⟩
    -- As above, reduce the bundled concrete maps to the functions whose injectivity we use.
    change g = g' at hg
    -- Reduce the second bundled map separately to expose the pointwise group action.
    change g * quotientPointsHom H I A n =
      g' * quotientPointsHom H I A n' at hgn
    subst g'
    apply Prod.ext
    · rfl
    apply quotientPointsHom_injective H I A
    exact mul_left_cancel hgn
  · intro g g' hgg'
    -- Reduce the bundled quotient map; its stable public formula is `pointwiseQuotientMk_apply`.
    change pointwiseQuotientMk H I hI A g = pointwiseQuotientMk H I hI A g' at hgg'
    have hmem : g⁻¹ * g' ∈ quotientPointsSubgroup H I A := by
      rw [pointwiseQuotientMk_apply, pointwiseQuotientMk_apply] at hgg'
      exact QuotientGroup.eq.mp hgg'
    obtain ⟨n, hn⟩ := hmem
    refine ⟨⟨g, n⟩, rfl, ?_⟩
    -- Reduce the bundled action map so that the subgroup-membership witness `hn` applies.
    change g * quotientPointsHom H I A n = g'
    rw [hn]
    simp

private theorem isPullback_pointwiseQuotientProjection
    (H : _root_.CommHopfAlgCat.{u} R) (I : HopfIdeal R H) (hI : I.IsNormal)
    (A : CommAlgCat.{u} R) :
    let q : HopfAlgebra.points (R := R) (H := H) A ⟶
        (pointwiseQuotientFunctor H I hI).obj A :=
      (pointwiseQuotientProjection H I hI).app A
    IsPullback
      (↾fun p : HopfAlgebra.points (R := R) (H := H) A ×
        HopfAlgebra.points (R := R) (H := quotient H I) A => p.1)
      (↾fun p : HopfAlgebra.points (R := R) (H := H) A ×
        HopfAlgebra.points (R := R) (H := quotient H I) A =>
          p.1 * quotientPointsHom H I A p.2)
      (↾fun g => q g) (↾fun g => q g) := by
  apply (isPullback_pointwiseQuotientMk H I hI A).of_iso
    (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (eqToIso (congrArg (fun G : GrpCat.{u} => (G : Type u))
      (pointwiseQuotientFunctor_obj H I hI A)).symm)
  · rfl
  · rfl
  · simp only [Iso.refl_hom, Category.id_comp]
    -- `of_iso` exposes the underlying type-valued maps, while the public comparison lemma
    -- `pointwiseQuotientProjection_app` is stated for the bundled `GrpCat` morphism.
    change (forget GrpCat.{u}).map (pointwiseQuotientMk H I hI A) ≫
        eqToHom (congrArg (fun G : GrpCat.{u} => (G : Type u))
          (pointwiseQuotientFunctor_obj H I hI A)).symm =
      (forget GrpCat.{u}).map ((pointwiseQuotientProjection H I hI).app A)
    rw [pointwiseQuotientProjection_app, ← eqToHom_map]
    exact ((forget GrpCat.{u}).map_comp _ _).symm
  · simp only [Iso.refl_hom, Category.id_comp]
    -- This is the same underlying-map reduction for the square's second quotient leg.
    change (forget GrpCat.{u}).map (pointwiseQuotientMk H I hI A) ≫
        eqToHom (congrArg (fun G : GrpCat.{u} => (G : Type u))
          (pointwiseQuotientFunctor_obj H I hI A)).symm =
      (forget GrpCat.{u}).map ((pointwiseQuotientProjection H I hI).app A)
    rw [pointwiseQuotientProjection_app, ← eqToHom_map]
    exact ((forget GrpCat.{u}).map_comp _ _).symm

private theorem isPullback_pointwiseQuotientProjection_ulift
    (H : _root_.CommHopfAlgCat.{u} R) (I : HopfIdeal R H) (hI : I.IsNormal)
    (A : CommAlgCat.{u} R) :
    IsPullback
      (↾fun p : ULift.{u + 1, u} (HopfAlgebra.points (R := R) (H := H) A) ×
        ULift.{u + 1, u} (HopfAlgebra.points (R := R) (H := quotient H I) A) => p.1)
      (↾fun p : ULift.{u + 1, u} (HopfAlgebra.points (R := R) (H := H) A) ×
        ULift.{u + 1, u} (HopfAlgebra.points (R := R) (H := quotient H I) A) =>
          (ULift.up (p.1.down * quotientPointsHom H I A p.2.down) :
            ULift.{u + 1, u} _))
      (↾fun g => (ULift.up ((pointwiseQuotientProjection H I hI).app A g.down) :
        ULift.{u + 1, u} _))
      (↾fun g => (ULift.up ((pointwiseQuotientProjection H I hI).app A g.down) :
        ULift.{u + 1, u} _)) := by
  apply ((isPullback_pointwiseQuotientProjection H I hI A).map
    CategoryTheory.uliftFunctor.{u + 1, u}).of_iso
      (CartesianMonoidalCategory.prodComparisonIso
        CategoryTheory.uliftFunctor.{u + 1, u} _ _)
      (Iso.refl _) (Iso.refl _) (Iso.refl _)
  all_goals rfl

/-- The inclusion of subgroup points into ambient points, used to define the torsor action. -/
private noncomputable def quotientSubgroupPointsPresheafGrpInclusion
    (H : _root_.CommHopfAlgCat.{u} R) (I : HopfIdeal R H) :
    pointsPresheafGrp (quotient H I) ⟶ pointsPresheafGrp H :=
  groupFunctorGrpMap <| Functor.whiskerRight
    (Functor.whiskerLeft (opOpEquivalence (CommAlgCat.{u} R)).functor
      (mapPointsFunctor (mkQuotient H I)))
    GrpCat.uliftFunctor.{u + 1, u}

/-- The action map in the pointwise torsor square, `(g, n) ↦ gn`. -/
noncomputable def pointwiseQuotientTorsorAction
    (H : _root_.CommHopfAlgCat.{u} R) (I : HopfIdeal R H) :
    (pointsPresheafGrp H).X ⊗ (pointsPresheafGrp (quotient H I)).X ⟶
      (pointsPresheafGrp H).X :=
  CartesianMonoidalCategory.fst _ _ *
    (CartesianMonoidalCategory.snd _ _ ≫
      (quotientSubgroupPointsPresheafGrpInclusion H I).hom.hom)

private theorem pointwiseQuotientTorsorAction_app
    (H : _root_.CommHopfAlgCat.{u} R) (I : HopfIdeal R H)
    (A : ((CommAlgCat.{u} R)ᵒᵖ)ᵒᵖ) :
    (pointwiseQuotientTorsorAction H I).app A =
      (↾fun p : ULift (HopfAlgebra.points (R := R) (H := H) A.unop.unop) ×
        ULift (HopfAlgebra.points (R := R) (H := quotient H I) A.unop.unop) =>
          ULift.up (p.1.down * quotientPointsHom H I A.unop.unop p.2.down)) := by
  -- Reduce the cartesian lift, group-object multiplication, whiskering, and `ULift` wrappers;
  -- these constructions expose no single application lemma for the resulting composite.
  rfl

/-- The pointwise quotient projection has the expected torsor kernel pair: two ambient points
have the same quotient class exactly when they differ by a unique point of the closed subgroup
represented by `H / I`. -/
theorem isPullback_pointwiseQuotientTorsor
    (H : _root_.CommHopfAlgCat.{u} R) (I : HopfIdeal R H) (hI : I.IsNormal) :
    IsPullback
      (CartesianMonoidalCategory.fst _ _)
      (pointwiseQuotientTorsorAction H I)
      (pointwiseQuotientPresheafGrpProjection H I hI).hom.hom
      (pointwiseQuotientPresheafGrpProjection H I hI).hom.hom := by
  let q : (pointsPresheafGrp H).X ⟶
      pointwiseQuotientPresheaf H I hI ⋙ GrpCat.uliftFunctor.{u + 1, u} ⋙
        forget GrpCat.{u + 1} :=
    eqToHom (pointsPresheafGrp_X_eq H) ≫
      Functor.whiskerRight
        (Functor.whiskerRight (pointwiseQuotientPresheafProjection H I hI)
          GrpCat.uliftFunctor.{u + 1, u}) (forget GrpCat.{u + 1})
  have hq : IsPullback
      (CartesianMonoidalCategory.fst _ _)
      (pointwiseQuotientTorsorAction H I) q q := by
    apply IsPullback.of_forall_isPullback_app
    intro A
    rw [Functor.Monoidal.fst_app, pointwiseQuotientTorsorAction_app]
    let qA := (Functor.whiskerRight
        (Functor.whiskerRight (pointwiseQuotientPresheafProjection H I hI)
          GrpCat.uliftFunctor.{u + 1, u}) (forget GrpCat.{u + 1})).app A
    have hqA : qA =
        (↾fun g : ULift (HopfAlgebra.points (R := R) (H := H) A.unop.unop) =>
          ULift.up ((pointwiseQuotientProjection H I hI).app A.unop.unop g.down)) := by
      ext g
      exact pointwiseQuotientPresheafProjection_ulift_app_apply H I hI A g
    -- Reduce the local abbreviation `q` at `A` before rewriting it with `hqA`.
    change IsPullback _ _ qA qA
    rw [hqA]
    exact isPullback_pointwiseQuotientProjection_ulift H I hI A.unop.unop
  rw [pointwiseQuotientPresheafGrpProjection_hom_hom]
  apply hq.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (eqToIso (pointwiseQuotientPresheafGrp_X_eq H I hI).symm)
  all_goals rfl

/-- The definitional identification between sheafifying the pointwise group object and the
canonical fppf group object. -/
private noncomputable def pointsFppfGroupObjectMapIso
    (H : _root_.CommHopfAlgCat.{u} R) :
    let F := presheafToSheaf (CommAlgCat.fppfTopology R) (Type (u + 1))
    let _ : F.Monoidal := Functor.Monoidal.ofChosenFiniteProducts F
    F.mapGrp.obj (pointsPresheafGrp H) ≅ pointsFppfGroupObject H :=
  Iso.refl _

/-- The carrier-level identification induced by `pointsFppfGroupObjectMapIso`. -/
private noncomputable def pointsFppfGroupObjectCarrierIso
    (H : _root_.CommHopfAlgCat.{u} R) :
    (presheafToSheaf (CommAlgCat.fppfTopology R) (Type (u + 1))).obj
        (pointsPresheafGrp H).X ≅ (pointsFppfGroupObject H).X := by
  let _ : (presheafToSheaf
      (CommAlgCat.fppfTopology R) (Type (u + 1))).Monoidal :=
    Functor.Monoidal.ofChosenFiniteProducts _
  exact (Grp.forget _).mapIso (pointsFppfGroupObjectMapIso H)

/-- The canonical comparison from the product of the two fppf sheaves to the sheafification of
their pointwise product. This is the inverse of the product comparison supplied by the left
exactness of fppf sheafification, after identifying the two sheafified factors with the carriers of
their fppf group objects. -/
noncomputable def fppfQuotientTorsorProductIso
    (H : _root_.CommHopfAlgCat.{u} R) (I : HopfIdeal R H) :
    (pointsFppfGroupObject H).X ⊗ (pointsFppfGroupObject (quotient H I)).X ≅
      (presheafToSheaf (CommAlgCat.fppfTopology R) (Type (u + 1))).obj
        ((pointsPresheafGrp H).X ⊗ (pointsPresheafGrp (quotient H I)).X) :=
  tensorIso
      (pointsFppfGroupObjectCarrierIso H).symm
      (pointsFppfGroupObjectCarrierIso (quotient H I)).symm ≪≫
    (CartesianMonoidalCategory.prodComparisonIso
      (presheafToSheaf (CommAlgCat.fppfTopology R) (Type (u + 1)))
      (pointsPresheafGrp H).X (pointsPresheafGrp (quotient H I)).X).symm

/-- The inclusion of the closed subgroup represented by `H / I` into the ambient fppf group. -/
noncomputable def quotientSubgroupPointsFppfGrpInclusion
    (H : _root_.CommHopfAlgCat.{u} R) (I : HopfIdeal R H) :
    pointsFppfGroupObject (quotient H I) ⟶ pointsFppfGroupObject H := by
  let _ : (presheafToSheaf
      (CommAlgCat.fppfTopology R) (Type (u + 1))).Monoidal :=
    Functor.Monoidal.ofChosenFiniteProducts _
  exact (presheafToSheaf
    (CommAlgCat.fppfTopology R) (Type (u + 1))).mapGrp.map
      (quotientSubgroupPointsPresheafGrpInclusion H I)

/-- The action map in the sheafified torsor square, defined on the product of the ambient and
subgroup fppf sheaves. -/
noncomputable def fppfQuotientTorsorAction
    (H : _root_.CommHopfAlgCat.{u} R) (I : HopfIdeal R H) :
    (pointsFppfGroupObject H).X ⊗ (pointsFppfGroupObject (quotient H I)).X ⟶
      (pointsFppfGroupObject H).X :=
  CartesianMonoidalCategory.fst _ _ *
    (CartesianMonoidalCategory.snd _ _ ≫
      (quotientSubgroupPointsFppfGrpInclusion H I).hom.hom)

private theorem sheafify_pointwiseQuotientTorsorFst
    (H : _root_.CommHopfAlgCat.{u} R) (I : HopfIdeal R H) :
    (fppfQuotientTorsorProductIso H I).hom ≫
        (presheafToSheaf (CommAlgCat.fppfTopology R) (Type (u + 1))).map
          (CartesianMonoidalCategory.fst
            (pointsPresheafGrp H).X (pointsPresheafGrp (quotient H I)).X) ≫
      (pointsFppfGroupObjectCarrierIso H).hom =
        CartesianMonoidalCategory.fst _ _ := by
  let F := presheafToSheaf (CommAlgCat.fppfTopology R) (Type (u + 1))
  let _ : F.Monoidal := Functor.Monoidal.ofChosenFiniteProducts _
  -- Unfold the product and carrier comparison isomorphisms so that the stable monoidal
  -- comparison lemmas below apply; there is no lemma for their packaged composite.
  change ((pointsFppfGroupObjectCarrierIso H).inv ⊗ₘ
        (pointsFppfGroupObjectCarrierIso (quotient H I)).inv) ≫
      (CartesianMonoidalCategory.prodComparisonIso F
        (pointsPresheafGrp H).X (pointsPresheafGrp (quotient H I)).X).inv ≫
      F.map (CartesianMonoidalCategory.fst
        (pointsPresheafGrp H).X (pointsPresheafGrp (quotient H I)).X) ≫
      (pointsFppfGroupObjectCarrierIso H).hom =
    CartesianMonoidalCategory.fst _ _
  rw [← Functor.Monoidal.μ_of_cartesianMonoidalCategory,
    Functor.Monoidal.μ_fst_assoc, CartesianMonoidalCategory.tensorHom_fst_assoc,
    Iso.inv_hom_id, Category.comp_id]

private theorem sheafify_pointwiseQuotientTorsorAction
    (H : _root_.CommHopfAlgCat.{u} R) (I : HopfIdeal R H) :
    (fppfQuotientTorsorProductIso H I).hom ≫
        (presheafToSheaf (CommAlgCat.fppfTopology R) (Type (u + 1))).map
          (pointwiseQuotientTorsorAction H I) ≫
      (pointsFppfGroupObjectCarrierIso H).hom =
        fppfQuotientTorsorAction H I := by
  let F := presheafToSheaf (CommAlgCat.fppfTopology R) (Type (u + 1))
  let _ : F.Monoidal := Functor.Monoidal.ofChosenFiniteProducts _
  let _ : IsMonHom (pointsFppfGroupObjectCarrierIso H).hom := by
    -- The carrier isomorphism is obtained by forgetting a group-object isomorphism, so its
    -- monoid-hom instance is exposed only after reducing to that underlying morphism.
    change IsMonHom (pointsFppfGroupObjectMapIso H).hom.hom.hom
    infer_instance
  -- Expose the two action definitions; the subsequent group-object lemmas reason about their
  -- multiplication composites, not the named wrappers themselves.
  change (fppfQuotientTorsorProductIso H I).hom ≫
        F.map (CartesianMonoidalCategory.fst _ _ *
          (CartesianMonoidalCategory.snd _ _ ≫
            (quotientSubgroupPointsPresheafGrpInclusion H I).hom.hom)) ≫
        (pointsFppfGroupObjectCarrierIso H).hom =
      CartesianMonoidalCategory.fst _ _ *
        (CartesianMonoidalCategory.snd _ _ ≫
          (quotientSubgroupPointsFppfGrpInclusion H I).hom.hom)
  rw [Functor.map_mul, MonObj.mul_comp, MonObj.comp_mul]
  congr 1
  · exact sheafify_pointwiseQuotientTorsorFst H I
  · -- Unfold the product comparison and sheafified subgroup inclusion to expose the
    -- second projection; no public lemma identifies this entire composite at once.
    change ((pointsFppfGroupObjectCarrierIso H).inv ⊗ₘ
          (pointsFppfGroupObjectCarrierIso (quotient H I)).inv) ≫
        (CartesianMonoidalCategory.prodComparisonIso F
          (pointsPresheafGrp H).X (pointsPresheafGrp (quotient H I)).X).inv ≫
        F.map (CartesianMonoidalCategory.snd _ _ ≫
          (quotientSubgroupPointsPresheafGrpInclusion H I).hom.hom) ≫
        (pointsFppfGroupObjectCarrierIso H).hom =
      CartesianMonoidalCategory.snd _ _ ≫
        (quotientSubgroupPointsFppfGrpInclusion H I).hom.hom
    rw [← Functor.Monoidal.μ_of_cartesianMonoidalCategory, Functor.map_comp]
    simp only [Category.assoc]
    rw [Functor.Monoidal.μ_snd_assoc,
      CartesianMonoidalCategory.tensorHom_snd_assoc]
    rfl

/-- The kernel pair of the fppf quotient projection `G ⟶ G / V(I)` is `G × V(I)` via
`(g,n) ↦ (g,gn)`. Together with
`isLocallySurjective_fppfQuotientProjection`, this gives the two torsor conditions. -/
theorem isPullback_fppfQuotientTorsor
    (H : _root_.CommHopfAlgCat.{u} R) (I : HopfIdeal R H) (hI : I.IsNormal) :
    IsPullback
      (CartesianMonoidalCategory.fst _ _)
      (fppfQuotientTorsorAction H I)
      (fppfQuotientProjection H I hI).hom.hom
      (fppfQuotientProjection H I hI).hom.hom := by
  let F := presheafToSheaf (CommAlgCat.fppfTopology R) (Type (u + 1))
  let _ : F.Monoidal := Functor.Monoidal.ofChosenFiniteProducts _
  have h := (isPullback_pointwiseQuotientTorsor H I hI).map F
  apply h.of_iso (fppfQuotientTorsorProductIso H I).symm
    (pointsFppfGroupObjectCarrierIso H)
    (pointsFppfGroupObjectCarrierIso H)
    (eqToIso (fppfQuotientSheaf_X_eq H I hI).symm)
  · apply (cancel_epi (fppfQuotientTorsorProductIso H I).hom).1
    simpa only [Category.assoc, Iso.symm_hom, Iso.hom_inv_id_assoc] using
      sheafify_pointwiseQuotientTorsorFst H I
  · apply (cancel_epi (fppfQuotientTorsorProductIso H I).hom).1
    simpa only [Category.assoc, Iso.symm_hom, Iso.hom_inv_id_assoc] using
      sheafify_pointwiseQuotientTorsorAction H I
  · rw [fppfQuotientProjection_hom]
    rfl
  · rw [fppfQuotientProjection_hom]
    rfl

end TauCeti.CommHopfAlgCat
