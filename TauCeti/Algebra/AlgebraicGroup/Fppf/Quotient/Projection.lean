/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.CategoryTheory.Sites.EpiMono
public import TauCeti.Algebra.AlgebraicGroup.Fppf.Quotient.Basic

/-!
# Local surjectivity of fppf quotient projections

Let `H` be a commutative Hopf algebra over a commutative ring `R`, and let `I` be a normal Hopf
ideal. The fppf quotient sheaf of `G = Spec H` by the closed normal subgroup cut out by `I` was
constructed by sheafifying the pointwise quotient presheaf. This file proves that its canonical
projection

```text
G ⟶ G / V(I)
```

is an epimorphism of group objects and that the underlying morphism of fppf sheaves is locally
surjective. The latter is the descent-theoretic content of passing from the pointwise quotient to
the fppf quotient: sections of the quotient need not lift globally, but they lift after an fppf
cover.

The proof first observes that the raw pointwise quotient maps are surjective. Their natural
transformation is therefore an epimorphism, and this remains so after universe lifting, forgetting
to types, and applying sheafification. Local surjectivity then follows from Mathlib's
characterization of epimorphisms of type-valued sheaves.

## Main declarations

* `TauCeti.CommHopfAlgCat.instEpiFppfQuotientProjection`: the quotient projection is an
  epimorphism of group objects in fppf sheaves.
* `TauCeti.CommHopfAlgCat.isLocallySurjective_fppfQuotientProjection`: its underlying sheaf map
  is locally surjective.

## References

* J. S. Milne, *Algebraic Groups* (2017), Section 5.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Section 14.

This is the local-surjectivity part of the quotient and torsor interface in Layer 3,
"Normality and quotients", of the ReductiveGroups roadmap.
-/

public section

open CategoryTheory Opposite
open scoped CategoryTheory.MonObj

namespace TauCeti.CommHopfAlgCat

universe u

variable {R : Type u} [CommRing R]

private instance instEpiPointwiseQuotientPresheafProjectionApp
    (H : _root_.CommHopfAlgCat.{u} R) (I : HopfIdeal R H) (hI : I.IsNormal)
    (A : ((CommAlgCat.{u} R)ᵒᵖ)ᵒᵖ) :
    Epi ((pointwiseQuotientPresheafProjection H I hI).app A) := by
  rw [pointwiseQuotientPresheafProjection, Functor.whiskerLeft_app,
    pointwiseQuotientProjection_app]
  apply (GrpCat.epi_iff_surjective _).2
  intro y
  obtain ⟨z, rfl⟩ := (ConcreteCategory.bijective_of_isIso
    (eqToHom (pointwiseQuotientFunctor_obj H I hI
      ((opOpEquivalence (CommAlgCat.{u} R)).functor.obj A)).symm)).surjective y
  obtain ⟨x, rfl⟩ := pointwiseQuotientMk_surjective H I hI
    ((opOpEquivalence (CommAlgCat.{u} R)).functor.obj A) z
  exact ⟨x, rfl⟩

private instance instEpiPointwiseQuotientPresheafProjection
    (H : _root_.CommHopfAlgCat.{u} R) (I : HopfIdeal R H) (hI : I.IsNormal) :
    Epi (pointwiseQuotientPresheafProjection H I hI) :=
  NatTrans.epi_of_epi_app _

private instance instEpiPointwiseQuotientPresheafGrpProjectionHom
    (H : _root_.CommHopfAlgCat.{u} R) (I : HopfIdeal R H) (hI : I.IsNormal) :
    Epi (pointwiseQuotientPresheafGrpProjection H I hI).hom.hom := by
  let _ (A : ((CommAlgCat.{u} R)ᵒᵖ)ᵒᵖ) :
      Epi ((Functor.whiskerRight
        (Functor.whiskerRight (pointwiseQuotientPresheafProjection H I hI)
          GrpCat.uliftFunctor.{u + 1, u}) (forget GrpCat.{u + 1})).app A) := by
    apply ConcreteCategory.epi_of_surjective
    intro y
    obtain ⟨x, hx⟩ :=
      (GrpCat.epi_iff_surjective _).1
        (inferInstance : Epi ((pointwiseQuotientPresheafProjection H I hI).app A)) y.down
    refine ⟨ULift.up x, ?_⟩
    erw [pointwiseQuotientPresheafProjection_ulift_app_apply]
    exact ULift.ext _ _ hx
  let _ : Epi (Functor.whiskerRight
      (Functor.whiskerRight (pointwiseQuotientPresheafProjection H I hI)
        GrpCat.uliftFunctor.{u + 1, u}) (forget GrpCat.{u + 1})) :=
    NatTrans.epi_of_epi_app _
  rw [pointwiseQuotientPresheafGrpProjection_hom_hom]
  infer_instance

private instance instEpiFppfQuotientProjectionHom
    (H : _root_.CommHopfAlgCat.{u} R) (I : HopfIdeal R H) (hI : I.IsNormal) :
    Epi (fppfQuotientProjection H I hI).hom.hom := by
  let _ : (presheafToSheaf (CommAlgCat.fppfTopology R) (Type (u + 1))).Monoidal :=
    Functor.Monoidal.ofChosenFiniteProducts _
  rw [fppfQuotientProjection_hom]
  infer_instance

/-- The canonical projection from an affine group to its fppf quotient by a normal closed
subgroup is an epimorphism of group objects in fppf sheaves. -/
instance instEpiFppfQuotientProjection
    (H : _root_.CommHopfAlgCat.{u} R) (I : HopfIdeal R H) (hI : I.IsNormal) :
    Epi (fppfQuotientProjection H I hI) := by
  constructor
  intro F f g hfg
  apply Grp.hom_ext
  apply (cancel_epi (fppfQuotientProjection H I hI).hom.hom).1
  simpa only [Grp.comp_hom_hom] using congrArg (fun q => q.hom.hom) hfg

/-- The underlying morphism of fppf sheaves of the canonical quotient projection is locally
surjective: every section of the quotient lifts to an ambient-group section after an fppf cover. -/
theorem isLocallySurjective_fppfQuotientProjection
    (H : _root_.CommHopfAlgCat.{u} R) (I : HopfIdeal R H) (hI : I.IsNormal) :
    Sheaf.IsLocallySurjective (fppfQuotientProjection H I hI).hom.hom := by
  rw [Sheaf.isLocallySurjective_iff_epi']
  infer_instance

end TauCeti.CommHopfAlgCat
