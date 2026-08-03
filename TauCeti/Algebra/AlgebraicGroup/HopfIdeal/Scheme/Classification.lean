/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Subobject.Basic
public import Mathlib.Order.Hom.Basic
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Scheme.Basic
public import TauCeti.Algebra.HopfAlgebra.Kernel

/-!
# Closed subgroup schemes and Hopf ideals

For a commutative Hopf algebra `H` over a commutative ring `R`, this file classifies the closed
subgroup subobjects of the affine group scheme `Spec H`. A closed subgroup scheme is an ordinary
categorical subobject whose representative arrow is a closed immersion on underlying schemes.
The closed-immersion condition is pulled back through the forgetful functors, so it is independent
of the representative chosen for the subobject.

A Hopf ideal `I` determines the closed subgroup `Spec (H ⧸ I) ⟶ Spec H`. Inclusion of Hopf ideals
reverses inclusion of closed subgroup schemes, and every closed subgroup arises in this way. The
classification is therefore packaged as an order isomorphism from the order dual of the Hopf
ideals of `H`.

## Main declarations

* `TauCeti.ClosedSubgroupScheme`: closed subgroup subobjects of a group scheme.
* `TauCeti.CommHopfAlgCat.quotientClosedSubgroup`: the closed subgroup cut out by a Hopf ideal.
* `TauCeti.CommHopfAlgCat.quotientClosedSubgroup_le_iff`: the order-reversing inclusion
  criterion.
* `TauCeti.CommHopfAlgCat.hopfIdealOrderIsoClosedSubgroup`: the classification of closed
  subgroup schemes of `Spec H` by Hopf ideals of `H`.

## References

* J. S. Milne, *Algebraic Groups*, Definition 3.10 and Propositions 3.12 and 3.15.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Section 16.

The references state the classical correspondence. The proof here works over an arbitrary
commutative base ring and uses categorical subobjects to identify isomorphic presentations.
-/

public section

open CategoryTheory

namespace TauCeti

universe u

open AlgebraicGeometry

/-- The property of a morphism of group schemes that its underlying scheme morphism is a closed
immersion. Pulling the property back along the two forgetful functors makes its invariance under
isomorphisms available from the generic morphism-property API. -/
def closedSubgroupMorphismProperty (S : CommRingCat.{u}) :
    MorphismProperty (Grp (Over (Spec S))) :=
  MorphismProperty.inverseImage (@IsClosedImmersion) (Grp.forget _ ⋙ Over.forget _)

/-- The underlying closed-immersion property is invariant under isomorphisms of group schemes. -/
instance closedSubgroupMorphismProperty_respectsIso (S : CommRingCat.{u}) :
    (closedSubgroupMorphismProperty S).RespectsIso := by
  change (MorphismProperty.inverseImage (@IsClosedImmersion)
    (Grp.forget _ ⋙ Over.forget _)).RespectsIso
  let _ : MorphismProperty.RespectsIso (@IsClosedImmersion) :=
    AlgebraicGeometry.IsClosedImmersion.respectsIso
  exact MorphismProperty.RespectsIso.inverseImage (@IsClosedImmersion)
    (Grp.forget _ ⋙ Over.forget _)

/-- A group-scheme morphism whose underlying scheme morphism is a closed immersion is a
monomorphism. -/
instance (priority := 900) mono_of_isClosedImmersion_underlying {S : CommRingCat.{u}}
    {G K : Grp (Over (Spec S))} (f : G ⟶ K) [IsClosedImmersion f.hom.hom.left] : Mono f := by
  apply (Grp.forget _ ⋙ Over.forget _).mono_of_mono_map
  change Mono f.hom.hom.left
  infer_instance

/-- A morphism has `closedSubgroupMorphismProperty` exactly when its underlying scheme morphism is
a closed immersion. -/
@[simp]
lemma closedSubgroupMorphismProperty_iff (S : CommRingCat.{u})
    {G K : Grp (Over (Spec S))} (f : G ⟶ K) :
    closedSubgroupMorphismProperty S f ↔ IsClosedImmersion f.hom.hom.left :=
  Iff.rfl

/-- A closed subgroup scheme of `G` is a categorical subobject represented by a closed immersion
on underlying schemes. The use of `Subobject` identifies presentations isomorphic over `G`. -/
abbrev ClosedSubgroupScheme {S : CommRingCat.{u}} (G : Grp (Over (Spec S))) :=
  {P : Subobject G // closedSubgroupMorphismProperty S P.arrow}

namespace ClosedSubgroupScheme

variable {S : CommRingCat.{u}} {G : Grp (Over (Spec S))}

/-- Construct a closed subgroup scheme from a monomorphism whose underlying scheme morphism is a
closed immersion. -/
@[expose] noncomputable def mk {X : Grp (Over (Spec S))} (i : X ⟶ G) [Mono i]
    (hi : IsClosedImmersion i.hom.hom.left) : ClosedSubgroupScheme G :=
  ⟨Subobject.mk i, by
    rw [← Subobject.underlyingIso_hom_comp_eq_mk i,
      (closedSubgroupMorphismProperty S).cancel_left_of_respectsIso]
    exact hi⟩

/-- The subobject underlying a closed subgroup scheme constructed from an explicit arrow is the
subobject represented by that arrow. -/
@[simp]
lemma coe_mk {X : Grp (Over (Spec S))} (i : X ⟶ G) [Mono i]
    (hi : IsClosedImmersion i.hom.hom.left) :
    (mk i hi).1 = Subobject.mk i :=
  rfl

end ClosedSubgroupScheme

namespace CommHopfAlgCat

variable {R : Type u} [CommRing R]

/-- The closed subgroup scheme of `Spec H` cut out by the Hopf ideal `I`. -/
@[expose] noncomputable def quotientClosedSubgroup (H : _root_.CommHopfAlgCat.{u} R)
    (I : HopfIdeal R H) :
    ClosedSubgroupScheme
      ((AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj (Opposite.op H)) :=
  ClosedSubgroupScheme.mk (quotientSpecι H I) inferInstance

/-- The subobject underlying `quotientClosedSubgroup` is represented by the quotient closed
immersion `Spec (H ⧸ I) ⟶ Spec H`. -/
@[simp]
lemma quotientClosedSubgroup_coe (H : _root_.CommHopfAlgCat.{u} R) (I : HopfIdeal R H) :
    (quotientClosedSubgroup H I).1 = Subobject.mk (quotientSpecι H I) :=
  rfl

/-- Inclusion of quotient closed subgroup schemes is exactly reverse inclusion of their defining
Hopf ideals. -/
@[simp]
theorem quotientClosedSubgroup_le_iff (H : _root_.CommHopfAlgCat.{u} R)
    {I J : HopfIdeal R H} :
    quotientClosedSubgroup H I ≤ quotientClosedSubgroup H J ↔ J ≤ I := by
  constructor
  · intro h x hx
    let g := Subobject.ofMkLEMk (quotientSpecι H I) (quotientSpecι H J) h
    let F := AlgebraicGeometry.hopfSpec (CommRingCat.of R)
    let hF : F.FullyFaithful :=
      AlgebraicGeometry.hopfSpec.fullyFaithful (R := CommRingCat.of R)
    have hg : g ≫ quotientSpecι H J = quotientSpecι H I :=
      Subobject.ofMkLEMk_comp h
    have hopEq :
        hF.preimage g ≫
            (mkQuotient H J).op =
          (mkQuotient H I).op := by
      apply hF.map_injective
      rw [F.map_comp, hF.map_preimage]
      simpa [F, quotientSpecι_def] using hg
    have hcoord :
        mkQuotient H J ≫
            (hF.preimage g).unop =
          mkQuotient H I := by
      simpa using congrArg Quiver.Hom.unop hopEq
    apply (mkQuotient_eq_zero_iff H I x).mp
    have hxzero : (mkQuotient H J).hom x = 0 :=
      (mkQuotient_eq_zero_iff H J x).mpr hx
    have happ := congrArg (fun k : H ⟶ quotient H I => k.hom x) hcoord
    rw [← happ, _root_.CommHopfAlgCat.comp_apply, hxzero, map_zero]
  · intro hJI
    exact Subobject.mk_le_mk_of_comm (quotientSpecMapOfLe H hJI)
      (quotientSpecMapOfLe_comp_quotientSpecι H hJI)

private noncomputable def hopfIdealClosedSubgroupOrderEmbedding
    (H : _root_.CommHopfAlgCat.{u} R) :
    (HopfIdeal R H)ᵒᵈ ↪o
      ClosedSubgroupScheme
        ((AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj (Opposite.op H)) where
  toFun I := quotientClosedSubgroup H I
  inj' := fun I J h => by
    apply le_antisymm
    · exact (quotientClosedSubgroup_le_iff H).mp (le_of_eq h)
    · exact (quotientClosedSubgroup_le_iff H).mp (le_of_eq h.symm)
  map_rel_iff' := quotientClosedSubgroup_le_iff H

private theorem quotientSubobject_ker_eq_mk
    (H K : _root_.CommHopfAlgCat.{u} R) (f : H ⟶ K) (hf : Function.Surjective f.hom)
    {X : Grp (Over (Spec (CommRingCat.of R)))}
    (e : (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj (Opposite.op K) ≅ X)
    (i : X ⟶ (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj (Opposite.op H)) [Mono i]
    (hmap_f : (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map f.op = e.hom ≫ i) :
    Subobject.mk (quotientSpecι H (HopfIdeal.ker f.hom hf)) = Subobject.mk i := by
  let I : HopfIdeal R H := HopfIdeal.ker f.hom hf
  let F := AlgebraicGeometry.hopfSpec (CommRingCat.of R)
  let qIso : quotient H I ≅ K :=
    _root_.CommHopfAlgCat.isoMk (HopfIdeal.kerLiftBialgEquiv f.hom hf) ≪≫
      _root_.CommHopfAlgCat.ofIsoSelf K
  have hq : mkQuotient H I ≫ qIso.hom = f := by
    ext x
    exact HopfIdeal.kerLiftBialgHom_mk f.hom hf x
  have hqInv : f ≫ qIso.inv = mkQuotient H I := by
    rw [← hq]
    simp
  let qSpecIso : quotientSpec H I ≅ X := (F.mapIso qIso.op).symm ≪≫ e
  apply Subobject.mk_eq_mk_of_comm (quotientSpecι H I) i qSpecIso
  dsimp only [qSpecIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv]
  change F.map qIso.inv.op ≫ e.hom ≫ i = quotientSpecι H I
  rw [← hmap_f, ← F.map_comp, ← op_comp, hqInv]
  change (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map (mkQuotient H I).op =
    quotientSpecι H I
  exact (quotientSpecι_def H I).symm

private theorem isAffine_closedSubgroup
    (H : _root_.CommHopfAlgCat.{u} R)
    (P : ClosedSubgroupScheme
      ((AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj (Opposite.op H))) :
    IsAffine (P.1 : Grp (Over (Spec (CommRingCat.of R)))).X.left := by
  let F := AlgebraicGeometry.hopfSpec (CommRingCat.of R)
  let i : (P.1 : Grp (Over (Spec (CommRingCat.of R)))) ⟶ F.obj (Opposite.op H) := P.1.arrow
  have hi : IsClosedImmersion i.hom.hom.left := by
    simpa [i] using P.2
  have hTarget : IsAffine (F.obj (Opposite.op H)).X.left :=
    AlgebraicGeometry.essImage_hopfSpec.mp (F.obj_mem_essImage (Opposite.op H))
  exact (@IsClosedImmersion.isAffine_surjective_of_isAffine _ _ hTarget
    i.hom.hom.left hi).1

private noncomputable def closedSubgroupCoordinateMorphism
    (H K : _root_.CommHopfAlgCat.{u} R)
    (P : ClosedSubgroupScheme
      ((AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj (Opposite.op H)))
    (e : (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj (Opposite.op K) ≅
      (P.1 : Grp (Over (Spec (CommRingCat.of R))))) : H ⟶ K :=
  (AlgebraicGeometry.hopfSpec.fullyFaithful (R := CommRingCat.of R)).preimage
    (e.hom ≫ P.1.arrow) |>.unop

private theorem hopfSpec_map_closedSubgroupCoordinateMorphism
    (H K : _root_.CommHopfAlgCat.{u} R)
    (P : ClosedSubgroupScheme
      ((AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj (Opposite.op H)))
    (e : (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj (Opposite.op K) ≅
      (P.1 : Grp (Over (Spec (CommRingCat.of R))))) :
    (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map
        (closedSubgroupCoordinateMorphism H K P e).op = e.hom ≫ P.1.arrow := by
  let F := AlgebraicGeometry.hopfSpec (CommRingCat.of R)
  let hF := AlgebraicGeometry.hopfSpec.fullyFaithful (R := CommRingCat.of R)
  change F.map (hF.preimage (e.hom ≫ P.1.arrow)) = e.hom ≫ P.1.arrow
  exact hF.map_preimage (e.hom ≫ P.1.arrow)

private theorem closedSubgroupCoordinateMorphism_surjective
    (H K : _root_.CommHopfAlgCat.{u} R)
    (P : ClosedSubgroupScheme
      ((AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj (Opposite.op H)))
    (e : (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj (Opposite.op K) ≅
      (P.1 : Grp (Over (Spec (CommRingCat.of R))))) :
    Function.Surjective (closedSubgroupCoordinateMorphism H K P e).hom := by
  apply (isClosedImmersion_hopfSpec_map_iff (S := CommRingCat.of R)
    (closedSubgroupCoordinateMorphism H K P e)).mp
  rw [hopfSpec_map_closedSubgroupCoordinateMorphism H K P e]
  apply (closedSubgroupMorphismProperty_iff _ (e.hom ≫ P.1.arrow)).mp
  exact MorphismProperty.RespectsIso.precomp
    (closedSubgroupMorphismProperty (CommRingCat.of R)) e.hom P.1.arrow P.2

private theorem exists_surjective_hopf_presentation
    (H : _root_.CommHopfAlgCat.{u} R)
    (P : ClosedSubgroupScheme
      ((AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj (Opposite.op H))) :
    ∃ (K : _root_.CommHopfAlgCat.{u} R)
      (e : (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj (Opposite.op K) ≅
        (P.1 : Grp (Over (Spec (CommRingCat.of R)))))
      (f : H ⟶ K),
      Function.Surjective f.hom ∧
        (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map f.op = e.hom ≫ P.1.arrow := by
  let F := AlgebraicGeometry.hopfSpec (CommRingCat.of R)
  have hEss : F.essImage (P.1 : Grp (Over (Spec (CommRingCat.of R)))) :=
    AlgebraicGeometry.essImage_hopfSpec.mpr (isAffine_closedSubgroup H P)
  let K := hEss.witness.unop
  let e : F.obj (Opposite.op K) ≅ (P.1 : Grp (Over (Spec (CommRingCat.of R)))) := hEss.getIso
  exact ⟨K, e, closedSubgroupCoordinateMorphism H K P e,
    closedSubgroupCoordinateMorphism_surjective H K P e,
    hopfSpec_map_closedSubgroupCoordinateMorphism H K P e⟩

private theorem hopfIdealClosedSubgroupOrderEmbedding_surjective
    (H : _root_.CommHopfAlgCat.{u} R) :
    Function.Surjective (hopfIdealClosedSubgroupOrderEmbedding H) := by
  intro P
  obtain ⟨K, e, f, hf, hmap_f⟩ := exists_surjective_hopf_presentation H P
  let I : HopfIdeal R H := HopfIdeal.ker f.hom hf
  refine ⟨I, Subtype.ext ?_⟩
  change Subobject.mk (quotientSpecι H I) = P.1
  simpa [I] using quotientSubobject_ker_eq_mk H K f hf e P.1.arrow hmap_f

/-- Hopf ideals of `H`, ordered by reverse inclusion, are order-isomorphic to the closed subgroup
schemes of `Spec H`. -/
noncomputable def hopfIdealOrderIsoClosedSubgroup
    (H : _root_.CommHopfAlgCat.{u} R) :
    (HopfIdeal R H)ᵒᵈ ≃o
      ClosedSubgroupScheme
        ((AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj (Opposite.op H)) :=
  OrderIso.ofSurjective (hopfIdealClosedSubgroupOrderEmbedding H)
    (hopfIdealClosedSubgroupOrderEmbedding_surjective H)

/-- The forward direction of the closed-subgroup classification sends a Hopf ideal to its quotient
closed subgroup scheme. -/
lemma hopfIdealOrderIsoClosedSubgroup_apply (H : _root_.CommHopfAlgCat.{u} R)
    (I : (HopfIdeal R H)ᵒᵈ) :
    hopfIdealOrderIsoClosedSubgroup H I = quotientClosedSubgroup H I :=
  by
    rw [hopfIdealOrderIsoClosedSubgroup, OrderIso.ofSurjective_apply]
    rfl

/-- Every closed subgroup scheme is the quotient closed subgroup cut out by the Hopf ideal
recovered by the inverse classification. -/
lemma hopfIdealOrderIsoClosedSubgroup_apply_symm
    (H : _root_.CommHopfAlgCat.{u} R)
    (P : ClosedSubgroupScheme
      ((AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj (Opposite.op H))) :
    quotientClosedSubgroup H ((hopfIdealOrderIsoClosedSubgroup H).symm P) = P := by
  rw [← hopfIdealOrderIsoClosedSubgroup_apply H]
  exact (hopfIdealOrderIsoClosedSubgroup H).apply_symm_apply P

/-- Applying the inverse classification to a quotient closed subgroup recovers its defining Hopf
ideal. -/
lemma hopfIdealOrderIsoClosedSubgroup_symm_apply_quotient
    (H : _root_.CommHopfAlgCat.{u} R) (I : HopfIdeal R H) :
    (hopfIdealOrderIsoClosedSubgroup H).symm (quotientClosedSubgroup H I) = I := by
  rw [← hopfIdealOrderIsoClosedSubgroup_apply H (show (HopfIdeal R H)ᵒᵈ from I)]
  exact (hopfIdealOrderIsoClosedSubgroup H).symm_apply_apply _

end CommHopfAlgCat

end TauCeti
