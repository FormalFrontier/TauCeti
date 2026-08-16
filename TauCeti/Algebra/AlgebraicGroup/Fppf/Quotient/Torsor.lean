/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Pullbacks
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
sheafification gives the corresponding pullback square for the fppf quotient sheaf. The product
in the sheafified statement is presented as the sheafification of the pointwise product; the
left-exact monoidal structure identifies it canonically with the product of the two sheaves.

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
open scoped CategoryTheory.MonObj

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
    change pointwiseQuotientMk H I hI A p.1 =
      pointwiseQuotientMk H I hI A (p.1 * quotientPointsHom H I A p.2)
    have hn : pointwiseQuotientMk H I hI A (quotientPointsHom H I A p.2) = 1 :=
      (pointwiseQuotientMk_eq_one_iff H I hI A _).2
        (quotientPointsHom_mem_quotientPointsSubgroup H I A p.2)
    rw [map_mul, hn, mul_one]
  · rintro ⟨g, n⟩ ⟨g', n'⟩ ⟨hg, hgn⟩
    change g = g' at hg
    change g * quotientPointsHom H I A n =
      g' * quotientPointsHom H I A n' at hgn
    subst g'
    apply Prod.ext
    · rfl
    apply quotientPointsHom_injective H I A
    exact mul_left_cancel hgn
  · intro g g' hgg'
    change pointwiseQuotientMk H I hI A g = pointwiseQuotientMk H I hI A g' at hgg'
    have hmem : g⁻¹ * g' ∈ quotientPointsSubgroup H I A := by
      rw [pointwiseQuotientMk_apply, pointwiseQuotientMk_apply] at hgg'
      exact QuotientGroup.eq.mp hgg'
    obtain ⟨n, hn⟩ := hmem
    refine ⟨⟨g, n⟩, rfl, ?_⟩
    change g * quotientPointsHom H I A n = g'
    rw [hn]
    simp

private theorem pointwiseQuotientProjection_app_apply
    (H : _root_.CommHopfAlgCat.{u} R) (I : HopfIdeal R H) (hI : I.IsNormal)
    (A : CommAlgCat.{u} R) (g : HopfAlgebra.points (R := R) (H := H) A) :
    (pointwiseQuotientProjection H I hI).app A g =
      eqToHom (pointwiseQuotientFunctor_obj H I hI A).symm
        (pointwiseQuotientMk H I hI A g) := by
  rw [pointwiseQuotientProjection_app]
  erw [GrpCat.comp_apply]

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
  rw [CategoryTheory.Limits.Types.isPullback_iff]
  have hp := (CategoryTheory.Limits.Types.isPullback_iff _ _ _ _).mp
    (isPullback_pointwiseQuotientMk H I hI A)
  refine ⟨?_, hp.2.1, ?_⟩
  · ext p
    change (pointwiseQuotientProjection H I hI).app A p.1 =
      (pointwiseQuotientProjection H I hI).app A
        (p.1 * quotientPointsHom H I A p.2)
    rw [pointwiseQuotientProjection_app_apply,
      pointwiseQuotientProjection_app_apply]
    exact congrArg (eqToHom (pointwiseQuotientFunctor_obj H I hI A).symm)
      (ConcreteCategory.congr_hom hp.1 p)
  · intro g g' hgg'
    have hgg'' : pointwiseQuotientMk H I hI A g =
        pointwiseQuotientMk H I hI A g' := by
      apply (ConcreteCategory.bijective_of_isIso
        (eqToHom (pointwiseQuotientFunctor_obj H I hI A).symm)).injective
      change (pointwiseQuotientProjection H I hI).app A g =
        (pointwiseQuotientProjection H I hI).app A g' at hgg'
      simpa only [pointwiseQuotientProjection_app_apply] using hgg'
    exact hp.2.2 g g' hgg''

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
  rw [CategoryTheory.Limits.Types.isPullback_iff]
  have hp := (CategoryTheory.Limits.Types.isPullback_iff _ _ _ _).mp
    (isPullback_pointwiseQuotientProjection H I hI A)
  refine ⟨?_, ?_, ?_⟩
  · ext p
    exact ConcreteCategory.congr_hom hp.1 ⟨p.1.down, p.2.down⟩
  · rintro ⟨g, n⟩ ⟨g', n'⟩ ⟨hg, hgn⟩
    have hpair := hp.2.1 ⟨g.down, n.down⟩ ⟨g'.down, n'.down⟩
      ⟨ULift.ext_iff.mp hg, ULift.ext_iff.mp hgn⟩
    exact congrArg (fun p => ((ULift.up p.1 : ULift.{u + 1, u} _),
      (ULift.up p.2 : ULift.{u + 1, u} _))) hpair
  · intro g g' hgg'
    obtain ⟨p, hp₁, hp₂⟩ := hp.2.2 g.down g'.down (ULift.ext_iff.mp hgg')
    exact ⟨((ULift.up p.1 : ULift.{u + 1, u} _),
        (ULift.up p.2 : ULift.{u + 1, u} _)),
      congrArg (ULift.up : _ → ULift.{u + 1, u} _) hp₁,
      congrArg (ULift.up : _ → ULift.{u + 1, u} _) hp₂⟩

/-- The inclusion of subgroup points into ambient points, used to define the torsor action. -/
private noncomputable def quotientSubgroupPointsPresheafGrpInclusion
    (H : _root_.CommHopfAlgCat.{u} R) (I : HopfIdeal R H) :
    pointsPresheafGrp (quotient H I) ⟶ pointsPresheafGrp H :=
  groupFunctorGrpMap <| Functor.whiskerRight
    (Functor.whiskerLeft (opOpEquivalence (CommAlgCat.{u} R)).functor
      (mapPointsFunctor (mkQuotient H I)))
    GrpCat.uliftFunctor.{u + 1, u}

/-- The first projection in the pointwise torsor square, `(g, n) ↦ g`. -/
noncomputable def pointwiseQuotientTorsorFst
    (H : _root_.CommHopfAlgCat.{u} R) (I : HopfIdeal R H) :
    (pointsPresheafGrp H).X ⊗ (pointsPresheafGrp (quotient H I)).X ⟶
      (pointsPresheafGrp H).X :=
  CartesianMonoidalCategory.fst _ _

/-- The action map in the pointwise torsor square, `(g, n) ↦ gn`. -/
noncomputable def pointwiseQuotientTorsorSnd
    (H : _root_.CommHopfAlgCat.{u} R) (I : HopfIdeal R H) :
    (pointsPresheafGrp H).X ⊗ (pointsPresheafGrp (quotient H I)).X ⟶
      (pointsPresheafGrp H).X :=
  CartesianMonoidalCategory.lift
      (CartesianMonoidalCategory.fst _ _)
      (CartesianMonoidalCategory.snd _ _ ≫
        (quotientSubgroupPointsPresheafGrpInclusion H I).hom.hom) ≫
    (pointsPresheafGrp H).grp.mul

private theorem pointwiseQuotientTorsorFst_app
    (H : _root_.CommHopfAlgCat.{u} R) (I : HopfIdeal R H)
    (A : ((CommAlgCat.{u} R)ᵒᵖ)ᵒᵖ) :
    (pointwiseQuotientTorsorFst H I).app A =
      (↾fun p : ULift (HopfAlgebra.points (R := R) (H := H) A.unop.unop) ×
        ULift (HopfAlgebra.points (R := R) (H := quotient H I) A.unop.unop) => p.1) := by
  rfl

private theorem pointwiseQuotientTorsorSnd_app
    (H : _root_.CommHopfAlgCat.{u} R) (I : HopfIdeal R H)
    (A : ((CommAlgCat.{u} R)ᵒᵖ)ᵒᵖ) :
    (pointwiseQuotientTorsorSnd H I).app A =
      (↾fun p : ULift (HopfAlgebra.points (R := R) (H := H) A.unop.unop) ×
        ULift (HopfAlgebra.points (R := R) (H := quotient H I) A.unop.unop) =>
          ULift.up (p.1.down * quotientPointsHom H I A.unop.unop p.2.down)) := by
  rfl

private theorem pointwiseQuotientTorsorProjection_app
    (H : _root_.CommHopfAlgCat.{u} R) (I : HopfIdeal R H) (hI : I.IsNormal)
    (A : ((CommAlgCat.{u} R)ᵒᵖ)ᵒᵖ) :
    (eqToHom (pointsPresheafGrp_X_eq H) ≫
      Functor.whiskerRight
        (Functor.whiskerRight (pointwiseQuotientPresheafProjection H I hI)
          GrpCat.uliftFunctor.{u + 1, u}) (forget GrpCat.{u + 1})).app A =
      (↾fun g : ULift (HopfAlgebra.points (R := R) (H := H) A.unop.unop) =>
        ULift.up ((pointwiseQuotientProjection H I hI).app A.unop.unop g.down)) := by
  ext g
  rfl

/-- The pointwise quotient projection has the expected torsor kernel pair: two ambient points
have the same quotient class exactly when they differ by a unique point of the closed subgroup
represented by `H / I`. -/
theorem isPullback_pointwiseQuotientTorsor
    (H : _root_.CommHopfAlgCat.{u} R) (I : HopfIdeal R H) (hI : I.IsNormal) :
    IsPullback
      (pointwiseQuotientTorsorFst H I)
      (pointwiseQuotientTorsorSnd H I)
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
      (pointwiseQuotientTorsorFst H I)
      (pointwiseQuotientTorsorSnd H I) q q := by
    apply IsPullback.of_forall_isPullback_app
    intro A
    rw [pointwiseQuotientTorsorFst_app, pointwiseQuotientTorsorSnd_app]
    rw [pointwiseQuotientTorsorProjection_app]
    exact isPullback_pointwiseQuotientProjection_ulift H I hI A.unop.unop
  rw [pointwiseQuotientPresheafGrpProjection_hom_hom]
  apply hq.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (eqToIso (pointwiseQuotientPresheafGrp_X_eq H I hI).symm)
  all_goals rfl

/-- The first projection in the sheafified torsor square. -/
noncomputable def fppfQuotientTorsorFst
    (H : _root_.CommHopfAlgCat.{u} R) (I : HopfIdeal R H) :
    (presheafToSheaf (CommAlgCat.fppfTopology R) (Type (u + 1))).obj
        ((pointsPresheafGrp H).X ⊗ (pointsPresheafGrp (quotient H I)).X) ⟶
      (pointsFppfGroupObject H).X :=
  (presheafToSheaf (CommAlgCat.fppfTopology R) (Type (u + 1))).map
      (pointwiseQuotientTorsorFst H I) ≫
    eqToHom (pointsFppfGroupObject_X_eq H).symm

/-- The action map in the sheafified torsor square. -/
noncomputable def fppfQuotientTorsorSnd
    (H : _root_.CommHopfAlgCat.{u} R) (I : HopfIdeal R H) :
    (presheafToSheaf (CommAlgCat.fppfTopology R) (Type (u + 1))).obj
        ((pointsPresheafGrp H).X ⊗ (pointsPresheafGrp (quotient H I)).X) ⟶
      (pointsFppfGroupObject H).X :=
  (presheafToSheaf (CommAlgCat.fppfTopology R) (Type (u + 1))).map
      (pointwiseQuotientTorsorSnd H I) ≫
    eqToHom (pointsFppfGroupObject_X_eq H).symm

/-- The fppf quotient projection is a torsor under the closed subgroup represented by `H / I`:
the sheafification of `G × V(I)` is the kernel pair of `G ⟶ G / V(I)` via `(g,n) ↦ (g,gn)`.
Equivalently, the canonical morphism from that product to `G ×_{G/V(I)} G` is an isomorphism. -/
theorem isPullback_fppfQuotientTorsor
    (H : _root_.CommHopfAlgCat.{u} R) (I : HopfIdeal R H) (hI : I.IsNormal) :
    IsPullback
      (fppfQuotientTorsorFst H I)
      (fppfQuotientTorsorSnd H I)
      (fppfQuotientProjection H I hI).hom.hom
      (fppfQuotientProjection H I hI).hom.hom := by
  let F := presheafToSheaf (CommAlgCat.fppfTopology R) (Type (u + 1))
  have h := (isPullback_pointwiseQuotientTorsor H I hI).map F
  apply h.of_iso (Iso.refl _) (eqToIso (pointsFppfGroupObject_X_eq H).symm)
    (eqToIso (pointsFppfGroupObject_X_eq H).symm)
    (eqToIso (fppfQuotientSheaf_X_eq H I hI).symm)
  · rfl
  · rfl
  · rw [fppfQuotientProjection_hom]
    rfl
  · rw [fppfQuotientProjection_hom]
    rfl

end TauCeti.CommHopfAlgCat
