/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Hom.Basic
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Scheme.Basic
public import TauCeti.Algebra.HopfAlgebra.Kernel
public import TauCeti.AlgebraicGeometry.GroupScheme.ClosedSubgroup

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
* `TauCeti.CommHopfAlgCat.hopfIdealOrderIsoClosedSubgroup_symm_apply_eq_ker`: the inverse
  classification computed from a surjective coordinate presentation.

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

namespace CommHopfAlgCat

variable {R : Type u} [CommRing R]

/-- The closed subgroup scheme of `Spec H` cut out by the Hopf ideal `I`. -/
noncomputable def quotientClosedSubgroup (H : _root_.CommHopfAlgCat.{u} R)
    (I : HopfIdeal R H) :
    ClosedSubgroupScheme
      ((AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj (Opposite.op H)) :=
  ClosedSubgroupScheme.mk (quotientSpecι H I)

/-- The subobject underlying `quotientClosedSubgroup` is represented by the quotient closed
immersion `Spec (H ⧸ I) ⟶ Spec H`. -/
@[simp]
lemma quotientClosedSubgroup_coe (H : _root_.CommHopfAlgCat.{u} R) (I : HopfIdeal R H) :
    (quotientClosedSubgroup H I).1 = Subobject.mk (quotientSpecι H I) :=
  by
    unfold quotientClosedSubgroup
    exact ClosedSubgroupScheme.coe_mk (quotientSpecι H I)

/-- Inclusion of quotient closed subgroup schemes is exactly reverse inclusion of their defining
Hopf ideals. -/
@[simp]
theorem quotientClosedSubgroup_le_iff (H : _root_.CommHopfAlgCat.{u} R)
    {I J : HopfIdeal R H} :
    quotientClosedSubgroup H I ≤ quotientClosedSubgroup H J ↔ J ≤ I := by
  constructor
  · intro h x hx
    have hSubobject :
        (quotientClosedSubgroup H I).1 ≤ (quotientClosedSubgroup H J).1 := h
    rw [quotientClosedSubgroup_coe, quotientClosedSubgroup_coe] at hSubobject
    let g := Subobject.ofMkLEMk (quotientSpecι H I) (quotientSpecι H J) hSubobject
    let F := AlgebraicGeometry.hopfSpec (CommRingCat.of R)
    let hF : F.FullyFaithful :=
      AlgebraicGeometry.hopfSpec.fullyFaithful (R := CommRingCat.of R)
    have hg : g ≫ quotientSpecι H J = quotientSpecι H I :=
      Subobject.ofMkLEMk_comp hSubobject
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
      simpa only [unop_comp, Quiver.Hom.unop_op] using
        congrArg Quiver.Hom.unop hopEq
    apply (mkQuotient_eq_zero_iff H I x).mp
    have hxzero : (mkQuotient H J).hom x = 0 :=
      (mkQuotient_eq_zero_iff H J x).mpr hx
    have happ := congrArg (fun k : H ⟶ quotient H I => k.hom x) hcoord
    rw [← happ, _root_.CommHopfAlgCat.comp_apply, hxzero, map_zero]
  · intro hJI
    -- The order on `ClosedSubgroupScheme` is inherited from its underlying subobject. The public
    -- projection equation then identifies the quotient presentations used by `Subobject`.
    change (quotientClosedSubgroup H I).1 ≤ (quotientClosedSubgroup H J).1
    rw [quotientClosedSubgroup_coe, quotientClosedSubgroup_coe]
    exact Subobject.mk_le_mk_of_comm (quotientSpecMapOfLe H hJI)
      (quotientSpecMapOfLe_comp_quotientSpecι H hJI)

/-- The private order embedding underlying the classification of Hopf ideals by closed subgroup
schemes. -/
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
    Subobject.mk (quotientSpecι H (HopfIdeal.kerOfSurjective f.hom hf)) = Subobject.mk i := by
  let I : HopfIdeal R H := HopfIdeal.kerOfSurjective f.hom hf
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
  -- The hom of this composite is the spectrum map of the opposite inverse of `qIso`, followed
  -- by `e.hom`; recording that identification isolates the definitional `mapIso` representation.
  have qSpecIso_hom : qSpecIso.hom = F.map qIso.inv.op ≫ e.hom := rfl
  rw [qSpecIso_hom, Category.assoc, ← hmap_f, ← F.map_comp, ← op_comp, hqInv,
    quotientSpecι_def]

private theorem isAffine_closedSubgroup
    (H : _root_.CommHopfAlgCat.{u} R)
    (P : ClosedSubgroupScheme
      ((AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj (Opposite.op H))) :
    IsAffine (P.1 : Grp (Over (Spec (CommRingCat.of R)))).X.left := by
  let F := AlgebraicGeometry.hopfSpec (CommRingCat.of R)
  let i : (P.1 : Grp (Over (Spec (CommRingCat.of R)))) ⟶ F.obj (Opposite.op H) := P.1.arrow
  have hi : IsClosedImmersion i.hom.hom.left := by
    simpa only [i] using
      (closedSubgroupMorphismProperty_iff _ P.1.arrow).mp P.2
  have hTarget : IsAffine (F.obj (Opposite.op H)).X.left :=
    AlgebraicGeometry.essImage_hopfSpec.mp (F.obj_mem_essImage (Opposite.op H))
  exact (@IsClosedImmersion.isAffine_surjective_of_isAffine _ _ hTarget
    i.hom.hom.left hi).1

/-- The Hopf-algebra morphism corresponding to a chosen affine presentation of a closed subgroup
scheme. -/
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
  simpa only [closedSubgroupCoordinateMorphism, Quiver.Hom.op_unop] using
    hF.map_preimage (e.hom ≫ P.1.arrow)

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
    (closedSubgroupMorphismProperty (Spec (CommRingCat.of R))) e.hom P.1.arrow P.2

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
  let I : HopfIdeal R H := HopfIdeal.kerOfSurjective f.hom hf
  refine ⟨OrderDual.toDual I, Subtype.ext ?_⟩
  -- The private order embedding forgets only the reversed order. Its value at `toDual I` is the
  -- public quotient construction, whose projection equation exposes the represented subobject.
  have hEmbedding :
      (hopfIdealClosedSubgroupOrderEmbedding H (OrderDual.toDual I)).1 =
        (quotientClosedSubgroup H I).1 := by
    unfold hopfIdealClosedSubgroupOrderEmbedding OrderDual.toDual
    rfl
  rw [hEmbedding, quotientClosedSubgroup_coe]
  exact (quotientSubobject_ker_eq_mk H K f hf e P.1.arrow hmap_f).trans
    (Subobject.mk_arrow P.1)

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
@[simp↓]
lemma hopfIdealOrderIsoClosedSubgroup_apply (H : _root_.CommHopfAlgCat.{u} R)
    (I : (HopfIdeal R H)ᵒᵈ) :
    hopfIdealOrderIsoClosedSubgroup H I =
      quotientClosedSubgroup H (OrderDual.ofDual I) :=
  by
    rw [hopfIdealOrderIsoClosedSubgroup, OrderIso.ofSurjective_apply]
    unfold OrderDual.ofDual
    rfl

/-- Every closed subgroup scheme is the quotient closed subgroup cut out by the Hopf ideal
recovered by the inverse classification. -/
@[simp↓]
lemma hopfIdealOrderIsoClosedSubgroup_apply_symm_apply
    (H : _root_.CommHopfAlgCat.{u} R)
    (P : ClosedSubgroupScheme
      ((AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj (Opposite.op H))) :
    quotientClosedSubgroup H
      (OrderDual.ofDual ((hopfIdealOrderIsoClosedSubgroup H).symm P)) = P := by
  calc
    quotientClosedSubgroup H
        (OrderDual.ofDual ((hopfIdealOrderIsoClosedSubgroup H).symm P)) =
        hopfIdealOrderIsoClosedSubgroup H ((hopfIdealOrderIsoClosedSubgroup H).symm P) :=
      (hopfIdealOrderIsoClosedSubgroup_apply H _).symm
    _ = P := (hopfIdealOrderIsoClosedSubgroup H).apply_symm_apply P

/-- Applying the inverse classification to a quotient closed subgroup recovers its defining Hopf
ideal. -/
@[simp↓]
lemma hopfIdealOrderIsoClosedSubgroup_symm_apply_quotientClosedSubgroup
    (H : _root_.CommHopfAlgCat.{u} R) (I : HopfIdeal R H) :
    (hopfIdealOrderIsoClosedSubgroup H).symm (quotientClosedSubgroup H I) =
      OrderDual.toDual I := by
  have hApply :=
    hopfIdealOrderIsoClosedSubgroup_apply H (OrderDual.toDual I)
  exact (congrArg (hopfIdealOrderIsoClosedSubgroup H).symm hApply).symm.trans
    ((hopfIdealOrderIsoClosedSubgroup H).symm_apply_apply (OrderDual.toDual I))

/-- Given an explicit affine presentation of a closed subgroup scheme, the inverse classification
recovers the Hopf ideal that is the kernel of its surjective coordinate morphism. -/
theorem hopfIdealOrderIsoClosedSubgroup_symm_apply_eq_ker
    (H K : _root_.CommHopfAlgCat.{u} R)
    (P : ClosedSubgroupScheme
      ((AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj (Opposite.op H)))
    (e : (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj (Opposite.op K) ≅
      (P.1 : Grp (Over (Spec (CommRingCat.of R)))))
    (f : H ⟶ K) (hf : Function.Surjective f.hom)
    (hmap_f : (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map f.op =
      e.hom ≫ P.1.arrow) :
    (hopfIdealOrderIsoClosedSubgroup H).symm P =
      OrderDual.toDual (HopfIdeal.kerOfSurjective f.hom hf) := by
  let I : HopfIdeal R H := HopfIdeal.kerOfSurjective f.hom hf
  have hP : quotientClosedSubgroup H I = P := by
    apply Subtype.ext
    rw [quotientClosedSubgroup_coe]
    exact (quotientSubobject_ker_eq_mk H K f hf e P.1.arrow hmap_f).trans
      (Subobject.mk_arrow P.1)
  rw [← hP]
  exact hopfIdealOrderIsoClosedSubgroup_symm_apply_quotientClosedSubgroup H I

end CommHopfAlgCat

end TauCeti
